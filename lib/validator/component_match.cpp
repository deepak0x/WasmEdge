// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2019-2025 Second State INC

//===-- component_match.cpp - Structural matching and instantiation -------===//
//
// The component-model subtype relation (MVP: structural equality modulo
// resource identity), resource-id walkers, and the instantiation engine that
// substitutes imported resources and freshens defined ones.
//
//===----------------------------------------------------------------------===//

#include "common/errinfo.h"
#include "common/spdlog.h"
#include "validator/validator.h"

#include <string>
#include <unordered_map>
#include <unordered_set>

namespace WasmEdge {
namespace Validator {

using namespace std::literals;

using CtxView = ComponentContext;

// NOLINTBEGIN(misc-no-recursion) -- type structures are finitely nested.

const CtxView::TypeEntry *
Validator::resolveQualType(const CtxView::QualValType &Q,
                           CtxView::TypeEntry &Storage) noexcept {
  if (Q.VT.isPrimValType() || Q.Home == nullptr) {
    return nullptr;
  }
  const auto *Entry = Q.Home->getType(Q.VT.getTypeIndex());
  if (Entry == nullptr) {
    return nullptr;
  }
  Storage = *Entry;
  if (Entry->ResourceId.has_value()) {
    Storage.ResourceId =
        CtxView::ResourceMap::apply(Q.Remap, *Entry->ResourceId);
  }
  Storage.Remap = CompCtx.composeRemap(Q.Remap, Entry->Remap);
  return &Storage;
}

namespace {
// Effective resource id behind an own/borrow handle index.
std::optional<uint32_t> handleResourceId(const CtxView::Scope *Home,
                                         const CtxView::ResourceMap *Remap,
                                         uint32_t Idx) noexcept {
  if (Home == nullptr) {
    return std::nullopt;
  }
  const auto *Entry = Home->getType(Idx);
  if (Entry == nullptr || !Entry->ResourceId.has_value()) {
    return std::nullopt;
  }
  return CtxView::ResourceMap::apply(Remap, *Entry->ResourceId);
}
} // namespace

// Resolves through type-index and prim-alias indirections.
Validator::NormalVal
Validator::normalizeValType(const CtxView::QualValType &Q) noexcept {
  if (Q.VT.isPrimValType()) {
    return {Q.VT.getCode(), nullptr, nullptr, nullptr, true};
  }
  CtxView::TypeEntry Storage;
  const auto *Entry = resolveQualType(Q, Storage);
  if (Entry == nullptr) {
    return {};
  }
  return normalizeEntry(*Entry);
}

Validator::NormalVal
Validator::normalizeEntry(const CtxView::TypeEntry &E) const noexcept {
  if (E.DT == nullptr || !E.DT->isDefValType()) {
    return {};
  }
  const auto &DVT = E.DT->getDefValType();
  if (DVT.isPrimValType()) {
    return {static_cast<ComponentTypeCode>(DVT.getPrimValType()), nullptr,
            nullptr, nullptr, true};
  }
  return {ComponentTypeCode::TypeIndex, &DVT, E.Home, E.Remap, true};
}

bool Validator::matchValType(const CtxView::QualValType &Sub,
                             const CtxView::QualValType &Sup,
                             ResourceSubst &Subst) noexcept {
  return matchNormalVal(normalizeValType(Sub), normalizeValType(Sup), Subst);
}

bool Validator::matchNormalVal(const NormalVal &NSub, const NormalVal &NSup,
                               ResourceSubst &Subst) noexcept {
  if (!NSub.Valid || !NSup.Valid) {
    return false;
  }
  if (NSub.DVT == nullptr && NSup.DVT == nullptr) {
    return NSub.Prim == NSup.Prim;
  }
  if (NSub.DVT == nullptr || NSup.DVT == nullptr) {
    return false;
  }
  const auto &A = *NSub.DVT;
  const auto &B = *NSup.DVT;
  auto MatchSub = [&](const ComponentValType &VA,
                      const ComponentValType &VB) noexcept {
    return matchValType({VA, NSub.Home, NSub.Remap},
                        {VB, NSup.Home, NSup.Remap}, Subst);
  };
  auto MatchOpt = [&](const std::optional<ComponentValType> &VA,
                      const std::optional<ComponentValType> &VB) noexcept {
    if (VA.has_value() != VB.has_value()) {
      return false;
    }
    return !VA.has_value() || MatchSub(*VA, *VB);
  };
  if (A.isRecordTy() && B.isRecordTy()) {
    const auto &RA = A.getRecord().LabelTypes;
    const auto &RB = B.getRecord().LabelTypes;
    if (RA.size() != RB.size()) {
      return false;
    }
    for (size_t I = 0; I < RA.size(); ++I) {
      if (RA[I].getLabel() != RB[I].getLabel() ||
          !MatchSub(RA[I].getValType(), RB[I].getValType())) {
        return false;
      }
    }
    return true;
  }
  if (A.isVariantTy() && B.isVariantTy()) {
    const auto &VA = A.getVariant().Cases;
    const auto &VB = B.getVariant().Cases;
    if (VA.size() != VB.size()) {
      return false;
    }
    for (size_t I = 0; I < VA.size(); ++I) {
      if (VA[I].first != VB[I].first || !MatchOpt(VA[I].second, VB[I].second)) {
        return false;
      }
    }
    return true;
  }
  if (A.isListTy() && B.isListTy()) {
    if (A.getList().Len != B.getList().Len) {
      return false;
    }
    return MatchSub(A.getList().ValTy, B.getList().ValTy);
  }
  if (A.isTupleTy() && B.isTupleTy()) {
    const auto &TA = A.getTuple().Types;
    const auto &TB = B.getTuple().Types;
    if (TA.size() != TB.size()) {
      return false;
    }
    for (size_t I = 0; I < TA.size(); ++I) {
      if (!MatchSub(TA[I], TB[I])) {
        return false;
      }
    }
    return true;
  }
  if (A.isFlagsTy() && B.isFlagsTy()) {
    return A.getFlags().Labels == B.getFlags().Labels;
  }
  if (A.isEnumTy() && B.isEnumTy()) {
    return A.getEnum().Labels == B.getEnum().Labels;
  }
  if (A.isOptionTy() && B.isOptionTy()) {
    return MatchSub(A.getOption().ValTy, B.getOption().ValTy);
  }
  if (A.isResultTy() && B.isResultTy()) {
    return MatchOpt(A.getResult().ValTy, B.getResult().ValTy) &&
           MatchOpt(A.getResult().ErrTy, B.getResult().ErrTy);
  }
  if ((A.isOwnTy() && B.isOwnTy()) || (A.isBorrowTy() && B.isBorrowTy())) {
    const uint32_t IA = A.isOwnTy() ? A.getOwn().Idx : A.getBorrow().Idx;
    const uint32_t IB = B.isOwnTy() ? B.getOwn().Idx : B.getBorrow().Idx;
    const auto RA = handleResourceId(NSub.Home, NSub.Remap, IA);
    const auto RB = handleResourceId(NSup.Home, NSup.Remap, IB);
    if (!RA.has_value() || !RB.has_value()) {
      return false;
    }
    uint32_t SupId = *RB;
    auto It = Subst.find(SupId);
    if (It != Subst.end()) {
      SupId = It->second;
    }
    return *RA == SupId;
  }
  return false;
}

bool Validator::matchFunc(const CtxView::FuncInfo &Sub,
                          const CtxView::FuncInfo &Sup,
                          ResourceSubst &Subst) noexcept {
  if (Sub.FT == nullptr || Sup.FT == nullptr) {
    return false;
  }
  const auto PA = Sub.FT->getParamList();
  const auto PB = Sup.FT->getParamList();
  if (PA.size() != PB.size()) {
    return false;
  }
  for (size_t I = 0; I < PA.size(); ++I) {
    if (PA[I].getLabel() != PB[I].getLabel() ||
        !matchValType({PA[I].getValType(), Sub.Home, Sub.Remap},
                      {PB[I].getValType(), Sup.Home, Sup.Remap}, Subst)) {
      return false;
    }
  }
  const auto RA = Sub.FT->getResultList();
  const auto RB = Sup.FT->getResultList();
  if (RA.size() != RB.size()) {
    return false;
  }
  for (size_t I = 0; I < RA.size(); ++I) {
    if (!matchValType({RA[I].getValType(), Sub.Home, Sub.Remap},
                      {RB[I].getValType(), Sup.Home, Sup.Remap}, Subst)) {
      return false;
    }
  }
  return true;
}

bool Validator::matchTypeEntry(const CtxView::TypeEntry &Sub,
                               const CtxView::TypeEntry &Sup,
                               ResourceSubst &Subst) noexcept {
  // Abstract resource supertype: binds (or re-checks) the substitution.
  if (Sup.ResourceId.has_value() && Sup.DT == nullptr) {
    if (!Sub.ResourceId.has_value()) {
      return false;
    }
    auto [It, New] = Subst.emplace(*Sup.ResourceId, *Sub.ResourceId);
    return New || It->second == *Sub.ResourceId;
  }
  if (Sup.ResourceId.has_value()) {
    if (!Sub.ResourceId.has_value()) {
      return false;
    }
    uint32_t SupId = *Sup.ResourceId;
    auto It = Subst.find(SupId);
    if (It != Subst.end()) {
      SupId = It->second;
    }
    return *Sub.ResourceId == SupId;
  }
  if (Sub.ResourceId.has_value()) {
    return false;
  }
  if (Sup.Inst != nullptr) {
    return Sub.Inst != nullptr &&
           matchInstanceInfo(*Sub.Inst, *Sup.Inst, Subst);
  }
  if (Sup.Comp != nullptr) {
    return Sub.Comp != nullptr &&
           matchComponentInfo(*Sub.Comp, *Sup.Comp, Subst);
  }
  if (Sup.DT == nullptr || Sub.DT == nullptr) {
    return false;
  }
  if (Sup.DT->isFuncType()) {
    if (!Sub.DT->isFuncType()) {
      return false;
    }
    return matchFunc({&Sub.DT->getFuncType(), Sub.Home, Sub.Remap},
                     {&Sup.DT->getFuncType(), Sup.Home, Sup.Remap}, Subst);
  }
  if (Sup.DT->isDefValType()) {
    if (!Sub.DT->isDefValType()) {
      return false;
    }
    return matchNormalVal(normalizeEntry(Sub), normalizeEntry(Sup), Subst);
  }
  return false;
}

bool Validator::matchInstanceInfo(const CtxView::InstanceInfo &Sub,
                                  const CtxView::InstanceInfo &Sup,
                                  ResourceSubst &Subst) noexcept {
  for (const auto &[Name, SupE] : Sup.Exports) {
    auto It = Sub.Exports.find(Name);
    if (It == Sub.Exports.end()) {
      return false;
    }
    if (!matchExtern(It->second, SupE, Subst)) {
      return false;
    }
  }
  return true;
}

bool Validator::matchComponentInfo(const CtxView::ComponentInfo &Sub,
                                   const CtxView::ComponentInfo &Sup,
                                   ResourceSubst &Subst) noexcept {
  // Imports contravariant: everything Sub requires, Sup must require
  // compatibly (so args satisfying Sup satisfy Sub).
  for (const auto &[Name, SubImp] : Sub.Imports) {
    const CtxView::ExternInfo *SupImp = nullptr;
    for (const auto &[SupName, E] : Sup.Imports) {
      if (SupName == Name) {
        SupImp = &E;
        break;
      }
    }
    if (SupImp == nullptr) {
      return false;
    }
    if (!matchExtern(*SupImp, SubImp, Subst)) {
      return false;
    }
  }
  // Exports covariant.
  for (const auto &[Name, SupE] : Sup.Exports) {
    auto It = Sub.Exports.find(Name);
    if (It == Sub.Exports.end()) {
      return false;
    }
    if (!matchExtern(It->second, SupE, Subst)) {
      return false;
    }
  }
  return true;
}

bool Validator::matchExtern(const CtxView::ExternInfo &Sub,
                            const CtxView::ExternInfo &Sup,
                            ResourceSubst &Subst) noexcept {
  if (Sub.K != Sup.K) {
    return false;
  }
  using Kind = CtxView::ExternInfo::Kind;
  switch (Sup.K) {
  case Kind::CoreModule: {
    if (Sub.CoreMod == nullptr || Sup.CoreMod == nullptr) {
      return false;
    }
    // Imports contravariant by (module, name); exports covariant.
    for (const auto &[Mod, Name, SubExt] : Sub.CoreMod->Imports) {
      const CtxView::CoreExternInfo *SupExt = nullptr;
      for (const auto &[SMod, SName, E] : Sup.CoreMod->Imports) {
        if (SMod == Mod && SName == Name) {
          SupExt = &E;
          break;
        }
      }
      if (SupExt == nullptr || !matchCoreExtern(*SupExt, SubExt)) {
        return false;
      }
    }
    for (const auto &[Name, SupExt] : Sup.CoreMod->Exports) {
      auto It = Sub.CoreMod->Exports.find(Name);
      if (It == Sub.CoreMod->Exports.end() ||
          !matchCoreExtern(It->second, SupExt)) {
        return false;
      }
    }
    return true;
  }
  case Kind::Func:
    return matchFunc(Sub.Func, Sup.Func, Subst);
  case Kind::Value:
    return matchValType(Sub.Value, Sup.Value, Subst);
  case Kind::Type:
    return matchTypeEntry(Sub.Type, Sup.Type, Subst);
  case Kind::Instance:
    return Sub.Inst != nullptr && Sup.Inst != nullptr &&
           matchInstanceInfo(*Sub.Inst, *Sup.Inst, Subst);
  case Kind::Component:
    return Sub.Comp != nullptr && Sup.Comp != nullptr &&
           matchComponentInfo(*Sub.Comp, *Sup.Comp, Subst);
  }
  return false;
}

bool Validator::matchCoreFuncType(const AST::SubType *Sub,
                                  const AST::SubType *Sup) const noexcept {
  if (Sub == nullptr || Sup == nullptr) {
    return false;
  }
  const auto &CA = Sub->getCompositeType();
  const auto &CB = Sup->getCompositeType();
  if (!CA.isFunc() || !CB.isFunc()) {
    return false;
  }
  return CA.getFuncType().getParamTypes() == CB.getFuncType().getParamTypes() &&
         CA.getFuncType().getReturnTypes() == CB.getFuncType().getReturnTypes();
}

bool Validator::matchCoreExtern(
    const CtxView::CoreExternInfo &Sub,
    const CtxView::CoreExternInfo &Sup) const noexcept {
  if (Sub.Kind != Sup.Kind) {
    return false;
  }
  auto MatchLimits = [](const AST::Limit &LA, const AST::Limit &LB) noexcept {
    if (LA.is64() != LB.is64() || LA.isShared() != LB.isShared()) {
      return false;
    }
    if (LA.getMin() < LB.getMin()) {
      return false;
    }
    if (LB.hasMax()) {
      return LA.hasMax() && LA.getMax() <= LB.getMax();
    }
    return true;
  };
  switch (Sup.Kind) {
  case ExternalType::Function:
  case ExternalType::Tag:
    return matchCoreFuncType(Sub.Func, Sup.Func);
  case ExternalType::Table:
    return Sub.Table != nullptr && Sup.Table != nullptr &&
           Sub.Table->getRefType() == Sup.Table->getRefType() &&
           MatchLimits(Sub.Table->getLimit(), Sup.Table->getLimit());
  case ExternalType::Memory:
    return Sub.Memory != nullptr && Sup.Memory != nullptr &&
           MatchLimits(Sub.Memory->getLimit(), Sup.Memory->getLimit());
  case ExternalType::Global:
    return Sub.Global != nullptr && Sup.Global != nullptr &&
           Sub.Global->getValType() == Sup.Global->getValType() &&
           Sub.Global->getValMut() == Sup.Global->getValMut();
  default:
    return false;
  }
}

bool Validator::containsBorrow(const CtxView::QualValType &Q) noexcept {
  const auto N = normalizeValType(Q);
  if (!N.Valid || N.DVT == nullptr) {
    return false;
  }
  const auto &D = *N.DVT;
  auto Sub = [&](const ComponentValType &VT) noexcept {
    return containsBorrow({VT, N.Home, N.Remap});
  };
  if (D.isBorrowTy()) {
    return true;
  }
  if (D.isRecordTy()) {
    for (const auto &LT : D.getRecord().LabelTypes) {
      if (Sub(LT.getValType())) {
        return true;
      }
    }
    return false;
  }
  if (D.isVariantTy()) {
    for (const auto &[Label, Ty] : D.getVariant().Cases) {
      if (Ty.has_value() && Sub(*Ty)) {
        return true;
      }
    }
    return false;
  }
  if (D.isListTy()) {
    return Sub(D.getList().ValTy);
  }
  if (D.isTupleTy()) {
    for (const auto &Ty : D.getTuple().Types) {
      if (Sub(Ty)) {
        return true;
      }
    }
    return false;
  }
  if (D.isOptionTy()) {
    return Sub(D.getOption().ValTy);
  }
  if (D.isResultTy()) {
    const auto &R = D.getResult();
    return (R.ValTy.has_value() && Sub(*R.ValTy)) ||
           (R.ErrTy.has_value() && Sub(*R.ErrTy));
  }
  return false;
}

void Validator::collectResources(const CtxView::QualValType &Q,
                                 std::unordered_set<uint32_t> &Out) noexcept {
  collectResourcesNormal(normalizeValType(Q), Out);
}

void Validator::collectResourcesNormal(
    const NormalVal &N, std::unordered_set<uint32_t> &Out) noexcept {
  if (!N.Valid || N.DVT == nullptr) {
    return;
  }
  const auto &D = *N.DVT;
  auto Sub = [&](const ComponentValType &VT) noexcept {
    collectResources({VT, N.Home, N.Remap}, Out);
  };
  if (D.isOwnTy() || D.isBorrowTy()) {
    const uint32_t Idx = D.isOwnTy() ? D.getOwn().Idx : D.getBorrow().Idx;
    if (auto Id = handleResourceId(N.Home, N.Remap, Idx)) {
      Out.insert(*Id);
    }
    return;
  }
  if (D.isRecordTy()) {
    for (const auto &LT : D.getRecord().LabelTypes) {
      Sub(LT.getValType());
    }
  } else if (D.isVariantTy()) {
    for (const auto &[Label, Ty] : D.getVariant().Cases) {
      if (Ty.has_value()) {
        Sub(*Ty);
      }
    }
  } else if (D.isListTy()) {
    Sub(D.getList().ValTy);
  } else if (D.isTupleTy()) {
    for (const auto &Ty : D.getTuple().Types) {
      Sub(Ty);
    }
  } else if (D.isOptionTy()) {
    Sub(D.getOption().ValTy);
  } else if (D.isResultTy()) {
    if (D.getResult().ValTy.has_value()) {
      Sub(*D.getResult().ValTy);
    }
    if (D.getResult().ErrTy.has_value()) {
      Sub(*D.getResult().ErrTy);
    }
  }
}

void Validator::collectResources(const CtxView::ExternInfo &Info,
                                 std::unordered_set<uint32_t> &Out) noexcept {
  using Kind = CtxView::ExternInfo::Kind;
  switch (Info.K) {
  case Kind::CoreModule:
    return;
  case Kind::Func: {
    if (Info.Func.FT == nullptr) {
      return;
    }
    for (const auto &P : Info.Func.FT->getParamList()) {
      collectResources({P.getValType(), Info.Func.Home, Info.Func.Remap}, Out);
    }
    for (const auto &R : Info.Func.FT->getResultList()) {
      collectResources({R.getValType(), Info.Func.Home, Info.Func.Remap}, Out);
    }
    return;
  }
  case Kind::Value:
    collectResources(Info.Value, Out);
    return;
  case Kind::Type: {
    const auto &E = Info.Type;
    if (E.ResourceId.has_value()) {
      Out.insert(*E.ResourceId);
      return;
    }
    if (E.Inst != nullptr) {
      for (const auto &[Name, Sub] : E.Inst->Exports) {
        collectResources(Sub, Out);
      }
      return;
    }
    if (E.Comp != nullptr) {
      for (const auto &[Name, Sub] : E.Comp->Imports) {
        collectResources(Sub, Out);
      }
      for (const auto &[Name, Sub] : E.Comp->Exports) {
        collectResources(Sub, Out);
      }
      return;
    }
    if (E.DT != nullptr && E.DT->isDefValType()) {
      collectResourcesNormal(normalizeEntry(E), Out);
      return;
    }
    if (E.DT != nullptr && E.DT->isFuncType()) {
      for (const auto &P : E.DT->getFuncType().getParamList()) {
        collectResources({P.getValType(), E.Home, E.Remap}, Out);
      }
      for (const auto &R : E.DT->getFuncType().getResultList()) {
        collectResources({R.getValType(), E.Home, E.Remap}, Out);
      }
    }
    return;
  }
  case Kind::Instance:
    if (Info.Inst != nullptr) {
      for (const auto &[Name, Sub] : Info.Inst->Exports) {
        collectResources(Sub, Out);
      }
    }
    return;
  case Kind::Component:
    if (Info.Comp != nullptr) {
      for (const auto &[Name, Sub] : Info.Comp->Imports) {
        collectResources(Sub, Out);
      }
      for (const auto &[Name, Sub] : Info.Comp->Exports) {
        collectResources(Sub, Out);
      }
    }
    return;
  }
}

bool Validator::originatesIn(uint32_t Id,
                             const CtxView::Scope &Scope) const noexcept {
  const auto &Entry = CompCtx.getResource(Id);
  for (const auto *S = Entry.Origin; S != nullptr; S = S->Parent) {
    if (S == &Scope) {
      return true;
    }
  }
  return false;
}

// ---------------------------------------------------------------------------
// Instantiation.
// ---------------------------------------------------------------------------

namespace {
// Rebuilds info graphs across an instantiation boundary, remapping resource
// ids eagerly in direct fields and lazily (via remap chains) in AST leaves.
struct Freshener {
  Validator &V;
  ComponentContext &Ctx;
  const CtxView::ResourceMap *Node; // combined substitution + freshening
  std::unordered_map<const CtxView::InstanceInfo *,
                     const CtxView::InstanceInfo *>
      InstMemo;
  std::unordered_map<const CtxView::ComponentInfo *,
                     const CtxView::ComponentInfo *>
      CompMemo;

  // NOLINTBEGIN(misc-no-recursion)
  CtxView::ExternInfo rebuild(const CtxView::ExternInfo &E) noexcept {
    using Kind = CtxView::ExternInfo::Kind;
    CtxView::ExternInfo R = E;
    switch (E.K) {
    case Kind::CoreModule:
      break;
    case Kind::Func:
      R.Func.Remap = Ctx.composeRemap(Node, E.Func.Remap);
      break;
    case Kind::Value:
      R.Value.Remap = Ctx.composeRemap(Node, E.Value.Remap);
      break;
    case Kind::Type:
      R.Type = rebuildEntry(E.Type);
      break;
    case Kind::Instance:
      R.Inst = rebuildInstance(E.Inst);
      break;
    case Kind::Component:
      R.Comp = rebuildComponent(E.Comp);
      break;
    }
    return R;
  }

  CtxView::TypeEntry rebuildEntry(const CtxView::TypeEntry &E) noexcept {
    CtxView::TypeEntry R = E;
    if (E.ResourceId.has_value()) {
      R.ResourceId = Node->apply(*E.ResourceId);
    }
    R.Remap = Ctx.composeRemap(Node, E.Remap);
    if (E.Inst != nullptr) {
      R.Inst = rebuildInstance(E.Inst);
    }
    if (E.Comp != nullptr) {
      R.Comp = rebuildComponent(E.Comp);
    }
    return R;
  }

  const CtxView::InstanceInfo *
  rebuildInstance(const CtxView::InstanceInfo *I) noexcept {
    if (I == nullptr) {
      return nullptr;
    }
    auto It = InstMemo.find(I);
    if (It != InstMemo.end()) {
      return It->second;
    }
    auto *R = Ctx.newInstanceInfo();
    InstMemo.emplace(I, R);
    R->DeclScope = I->DeclScope;
    for (const auto &[Name, E] : I->Exports) {
      R->Exports.emplace(Name, rebuild(E));
    }
    return R;
  }

  const CtxView::ComponentInfo *
  rebuildComponent(const CtxView::ComponentInfo *C) noexcept {
    if (C == nullptr) {
      return nullptr;
    }
    auto It = CompMemo.find(C);
    if (It != CompMemo.end()) {
      return It->second;
    }
    auto *R = Ctx.newComponentInfo();
    CompMemo.emplace(C, R);
    R->DeclScope = C->DeclScope;
    for (const auto &[Name, E] : C->Imports) {
      R->Imports.emplace_back(Name, rebuild(E));
    }
    for (const auto &[Name, E] : C->Exports) {
      R->Exports.emplace(Name, rebuild(E));
    }
    return R;
  }
  // NOLINTEND(misc-no-recursion)
};
} // namespace

Expect<const CtxView::InstanceInfo *> Validator::instantiateComponentInfo(
    const CtxView::ComponentInfo &CI,
    Span<const AST::Component::InstantiateArg<AST::Component::SortIndex>>
        Args) noexcept {
  // Resolve arguments; names must be unique.
  std::unordered_map<std::string_view, CtxView::ExternInfo> ArgMap;
  for (const auto &Arg : Args) {
    EXPECTED_TRY(auto Info, resolveSortIndex(Arg.getIndex()));
    if (!ArgMap.emplace(Arg.getName(), Info).second) {
      spdlog::error(ErrCode::Value::ComponentDuplicateName);
      spdlog::error("    Duplicate instantiation argument '{}'."sv,
                    Arg.getName());
      return Unexpect(ErrCode::Value::ComponentDuplicateName);
    }
    // Values are consumed by being passed as arguments.
    if (!Arg.getIndex().getSort().isCore() &&
        Arg.getIndex().getSort().getSortType() ==
            AST::Component::Sort::SortType::Value) {
      auto &VE = CompCtx.top().Values[Arg.getIndex().getIdx()];
      if (VE.Consumed) {
        spdlog::error(ErrCode::Value::ComponentValueAlreadyConsumed);
        return Unexpect(ErrCode::Value::ComponentValueAlreadyConsumed);
      }
      VE.Consumed = true;
    }
  }
  // Match every import; accumulate the resource substitution.
  ResourceSubst Subst;
  for (const auto &[Name, Req] : CI.Imports) {
    auto It = ArgMap.find(Name);
    if (It == ArgMap.end()) {
      spdlog::error(ErrCode::Value::MissingArgument);
      spdlog::error("    Missing instantiation argument '{}'."sv, Name);
      return Unexpect(ErrCode::Value::MissingArgument);
    }
    if (!matchExtern(It->second, Req, Subst)) {
      // A missing export on an instance argument gets its own diagnostic.
      if (Req.K == CtxView::ExternInfo::Kind::Instance &&
          It->second.K == CtxView::ExternInfo::Kind::Instance &&
          Req.Inst != nullptr && It->second.Inst != nullptr) {
        for (const auto &[ExpName, ReqE] : Req.Inst->Exports) {
          if (It->second.Inst->Exports.find(ExpName) ==
              It->second.Inst->Exports.end()) {
            spdlog::error(ErrCode::Value::InstanceMissingExpectedExport);
            spdlog::error(
                "    Instance argument '{}' is missing expected export "
                "'{}'."sv,
                Name, ExpName);
            return Unexpect(ErrCode::Value::InstanceMissingExpectedExport);
          }
        }
      }
      spdlog::error(ErrCode::Value::ArgTypeMismatch);
      spdlog::error("    Instantiation argument '{}' has an incompatible "
                    "type."sv,
                    Name);
      return Unexpect(ErrCode::Value::ArgTypeMismatch);
    }
  }

  // Combined remap: substituted imports + freshened defined resources.
  std::unordered_set<uint32_t> Reachable;
  for (const auto &[Name, E] : CI.Exports) {
    collectResources(E, Reachable);
  }
  auto *Node = CompCtx.newResourceMap();
  Node->Map = Subst;
  for (const uint32_t Id : Reachable) {
    if (Node->Map.count(Id) != 0) {
      continue;
    }
    const auto &Entry = CompCtx.getResource(Id);
    if (!Entry.FromImport && CI.DeclScope != nullptr &&
        originatesIn(Id, *CI.DeclScope)) {
      // Freshened ids carry no definition body: the fresh resource belongs
      // to the created instance, so it is never canon-local here.
      Node->Map.emplace(Id,
                        CompCtx.addResource(nullptr, &CompCtx.top(), false));
    }
  }

  Freshener F{*this, CompCtx, Node, {}, {}};
  auto *Result = CompCtx.newInstanceInfo();
  Result->DeclScope = CI.DeclScope;
  for (const auto &[Name, E] : CI.Exports) {
    Result->Exports.emplace(Name, F.rebuild(E));
  }
  return Result;
}

Expect<CtxView::ExternInfo>
Validator::resolveSortIndex(const AST::Component::SortIndex &SI) noexcept {
  CtxView::ExternInfo Info;
  const auto &S = CompCtx.top();
  const auto &Sort = SI.getSort();
  const uint32_t Idx = SI.getIdx();
  if (Sort.isCore()) {
    if (Sort.getCoreSortType() == AST::Component::Sort::CoreSortType::Module) {
      const auto *Mod = S.getCoreModule(Idx);
      if (Mod == nullptr) {
        spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
        spdlog::error("    Core module index {} out of bounds (size {})."sv,
                      Idx, S.CoreModules.size());
        return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
      }
      Info.K = CtxView::ExternInfo::Kind::CoreModule;
      Info.CoreMod = Mod;
      return Info;
    }
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error(
        "    Core sorts other than module cannot be used at component level."sv);
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  switch (Sort.getSortType()) {
  case AST::Component::Sort::SortType::Func: {
    const auto *F = S.getFunc(Idx);
    if (F == nullptr) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    Function index {} out of bounds (size {})."sv, Idx,
                    S.Funcs.size());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    Info.K = CtxView::ExternInfo::Kind::Func;
    Info.Func = *F;
    return Info;
  }
  case AST::Component::Sort::SortType::Value: {
    if (Idx >= S.Values.size()) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    Value index {} out of bounds (size {})."sv, Idx,
                    S.Values.size());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    Info.K = CtxView::ExternInfo::Kind::Value;
    Info.Value = S.Values[Idx].Type;
    return Info;
  }
  case AST::Component::Sort::SortType::Type: {
    const auto *E = S.getType(Idx);
    if (E == nullptr) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    Type index {} out of bounds (size {})."sv, Idx,
                    S.Types.size());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    Info.K = CtxView::ExternInfo::Kind::Type;
    Info.Type = *E;
    return Info;
  }
  case AST::Component::Sort::SortType::Component: {
    const auto *C = S.getComponent(Idx);
    if (C == nullptr) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    Component index {} out of bounds (size {})."sv, Idx,
                    S.Components.size());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    Info.K = CtxView::ExternInfo::Kind::Component;
    Info.Comp = C;
    return Info;
  }
  case AST::Component::Sort::SortType::Instance: {
    const auto *I = S.getInstance(Idx);
    if (I == nullptr) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    Instance index {} out of bounds (size {})."sv, Idx,
                    S.Instances.size());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    Info.K = CtxView::ExternInfo::Kind::Instance;
    Info.Inst = I;
    return Info;
  }
  default:
    spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
    return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
  }
}

// NOLINTEND(misc-no-recursion)

} // namespace Validator
} // namespace WasmEdge
