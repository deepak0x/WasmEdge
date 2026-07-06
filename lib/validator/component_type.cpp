// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2019-2025 Second State INC

//===-- component_type.cpp - Type / descriptor / declarator validation ----===//
//
// Validation of component-model type definitions, extern descriptors, and the
// declaration bodies of moduletype / instancetype / componenttype, producing
// the resolved info views defined in validator/component_context.h.
//
//===----------------------------------------------------------------------===//

#include "common/errinfo.h"
#include "common/spdlog.h"
#include "validator/validator.h"

#include <algorithm>
#include <cctype>
#include <string>
#include <unordered_set>
#include <vector>

namespace WasmEdge {
namespace Validator {

using namespace std::literals;

namespace {

std::string toLowerCopy(std::string_view SV) {
  std::string R(SV);
  std::transform(R.begin(), R.end(), R.begin(), [](unsigned char C) {
    return static_cast<char>(std::tolower(C));
  });
  return R;
}

// Label validity + case-insensitive uniqueness within one type definition.
Expect<void> checkLabel(std::string_view Label,
                        std::unordered_set<std::string> &Seen,
                        std::string_view Where,
                        ErrCode::Value DupCode) noexcept {
  if (Label.empty()) {
    spdlog::error(ErrCode::Value::NameCannotBeEmpty);
    spdlog::error("    {} label cannot be empty."sv, Where);
    return Unexpect(ErrCode::Value::NameCannotBeEmpty);
  }
  if (!isKebabString(Label)) {
    spdlog::error(ErrCode::Value::ComponentNameNotKebab);
    spdlog::error("    {} label '{}' is not in kebab case."sv, Where, Label);
    return Unexpect(ErrCode::Value::ComponentNameNotKebab);
  }
  if (!Seen.insert(toLowerCopy(Label)).second) {
    spdlog::error(DupCode);
    spdlog::error("    {} label '{}' conflicts with a previous label."sv, Where,
                  Label);
    return Unexpect(DupCode);
  }
  return {};
}

} // namespace

// valtype ::= i:<typeidx> | pvt:<primvaltype>. A type index must refer to a
// defvaltype entry in the current scope.
Expect<void> Validator::validate(const ComponentValType &VT) noexcept {
  if (VT.isPrimValType()) {
    if (VT.getCode() == ComponentTypeCode::ErrContext) {
      spdlog::error(ErrCode::Value::ComponentNotImplValidator);
      spdlog::error("    error-context type requires the async feature."sv);
      return Unexpect(ErrCode::Value::ComponentNotImplValidator);
    }
    return {};
  }
  const auto *Entry = CompCtx.top().getType(VT.getTypeIndex());
  if (Entry == nullptr) {
    spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
    spdlog::error("    Value type index {} out of bounds (size {})."sv,
                  VT.getTypeIndex(), CompCtx.top().Types.size());
    return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
  }
  if (Entry->DT == nullptr || !Entry->DT->isDefValType()) {
    spdlog::error(ErrCode::Value::NotADefinedType);
    spdlog::error("    Value type index {} does not refer to a value type."sv,
                  VT.getTypeIndex());
    return Unexpect(ErrCode::Value::NotADefinedType);
  }
  return {};
}

Expect<void>
Validator::validate(const AST::Component::DefValType &DVT) noexcept {
  std::unordered_set<std::string> Seen;
  if (DVT.isPrimValType()) {
    return validate(
        ComponentValType(static_cast<ComponentTypeCode>(DVT.getPrimValType())));
  }
  if (DVT.isRecordTy()) {
    const auto &Rec = DVT.getRecord();
    if (Rec.LabelTypes.empty()) {
      spdlog::error(ErrCode::Value::VariantMustHaveCase);
      spdlog::error("    Record type must have at least one field."sv);
      return Unexpect(ErrCode::Value::VariantMustHaveCase);
    }
    for (const auto &LT : Rec.LabelTypes) {
      EXPECTED_TRY(checkLabel(LT.getLabel(), Seen, "Record field"sv,
                              ErrCode::Value::RecordFieldNameConflicts));
      EXPECTED_TRY(validate(LT.getValType()));
    }
    return {};
  }
  if (DVT.isVariantTy()) {
    const auto &Var = DVT.getVariant();
    if (Var.Cases.empty()) {
      spdlog::error(ErrCode::Value::VariantMustHaveCase);
      spdlog::error("    Variant type must have at least one case."sv);
      return Unexpect(ErrCode::Value::VariantMustHaveCase);
    }
    for (const auto &[Label, Ty] : Var.Cases) {
      EXPECTED_TRY(checkLabel(Label, Seen, "Variant case"sv,
                              ErrCode::Value::VariantCaseNameConflicts));
      if (Ty.has_value()) {
        EXPECTED_TRY(validate(*Ty));
      }
    }
    return {};
  }
  if (DVT.isListTy()) {
    const auto &List = DVT.getList();
    if (List.Len.has_value() && *List.Len == 0) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Fixed-length list must have a non-zero length."sv);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    return validate(List.ValTy);
  }
  if (DVT.isTupleTy()) {
    const auto &Tup = DVT.getTuple();
    if (Tup.Types.empty()) {
      spdlog::error(ErrCode::Value::VariantMustHaveCase);
      spdlog::error("    Tuple type must have at least one element."sv);
      return Unexpect(ErrCode::Value::VariantMustHaveCase);
    }
    for (const auto &Ty : Tup.Types) {
      EXPECTED_TRY(validate(Ty));
    }
    return {};
  }
  if (DVT.isFlagsTy()) {
    const auto &Flags = DVT.getFlags();
    if (Flags.Labels.empty()) {
      spdlog::error(ErrCode::Value::VariantMustHaveCase);
      spdlog::error("    Flags type must have at least one label."sv);
      return Unexpect(ErrCode::Value::VariantMustHaveCase);
    }
    if (Flags.Labels.size() > 32) {
      spdlog::error(ErrCode::Value::CannotHaveMoreThan32Flags);
      spdlog::error("    Flags type has {} labels."sv, Flags.Labels.size());
      return Unexpect(ErrCode::Value::CannotHaveMoreThan32Flags);
    }
    for (const auto &Label : Flags.Labels) {
      EXPECTED_TRY(checkLabel(Label, Seen, "Flags"sv,
                              ErrCode::Value::FlagNameConflicts));
    }
    return {};
  }
  if (DVT.isEnumTy()) {
    const auto &Enum = DVT.getEnum();
    if (Enum.Labels.empty()) {
      spdlog::error(ErrCode::Value::VariantMustHaveCase);
      spdlog::error("    Enum type must have at least one label."sv);
      return Unexpect(ErrCode::Value::VariantMustHaveCase);
    }
    for (const auto &Label : Enum.Labels) {
      EXPECTED_TRY(checkLabel(Label, Seen, "Enum"sv,
                              ErrCode::Value::EnumTagNameConflicts));
    }
    return {};
  }
  if (DVT.isOptionTy()) {
    return validate(DVT.getOption().ValTy);
  }
  if (DVT.isResultTy()) {
    const auto &Res = DVT.getResult();
    if (Res.ValTy.has_value()) {
      EXPECTED_TRY(validate(*Res.ValTy));
    }
    if (Res.ErrTy.has_value()) {
      EXPECTED_TRY(validate(*Res.ErrTy));
    }
    return {};
  }
  if (DVT.isOwnTy() || DVT.isBorrowTy()) {
    const uint32_t Idx = DVT.isOwnTy() ? DVT.getOwn().Idx : DVT.getBorrow().Idx;
    const auto *Entry = CompCtx.top().getType(Idx);
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    own/borrow type index {} out of bounds (size {})."sv,
                    Idx, CompCtx.top().Types.size());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    if (!Entry->ResourceId.has_value()) {
      spdlog::error(ErrCode::Value::NotADefinedType);
      spdlog::error(
          "    own/borrow type index {} does not refer to a resource type."sv,
          Idx);
      return Unexpect(ErrCode::Value::NotADefinedType);
    }
    return {};
  }
  // stream / future are gated behind the async feature.
  spdlog::error(ErrCode::Value::ComponentNotImplValidator);
  spdlog::error("    stream/future types require the async feature."sv);
  return Unexpect(ErrCode::Value::ComponentNotImplValidator);
}

Expect<void> Validator::validate(const AST::Component::FuncType &FT) noexcept {
  if (FT.isAsync()) {
    spdlog::error(ErrCode::Value::ComponentNotImplValidator);
    spdlog::error("    async function types are not supported yet."sv);
    return Unexpect(ErrCode::Value::ComponentNotImplValidator);
  }
  std::unordered_set<std::string> Seen;
  for (const auto &Param : FT.getParamList()) {
    EXPECTED_TRY(checkLabel(Param.getLabel(), Seen, "Function parameter"sv,
                            ErrCode::Value::ComponentDuplicateName));
    EXPECTED_TRY(validate(Param.getValType()));
  }
  if (FT.getResultList().size() > 1) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error("    Function types may have at most one result."sv);
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  for (const auto &Result : FT.getResultList()) {
    if (!Result.getLabel().empty()) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Function results cannot be named."sv);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    EXPECTED_TRY(validate(Result.getValType()));
    if (containsBorrow({Result.getValType(), &CompCtx.top(), nullptr})) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Function results cannot contain borrow handles."sv);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
  }
  return {};
}

Expect<void>
Validator::validate(const AST::Component::ResourceType &RT) noexcept {
  if (CompCtx.top().K != ComponentContext::Scope::Kind::Component) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error(
        "    Resource types cannot be defined in component or instance types."sv);
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  if (RT.getCallback().has_value()) {
    spdlog::error(ErrCode::Value::ComponentNotImplValidator);
    spdlog::error("    async resource destructors are not supported yet."sv);
    return Unexpect(ErrCode::Value::ComponentNotImplValidator);
  }
  if (RT.getDestructor().has_value()) {
    const uint32_t Idx = *RT.getDestructor();
    const auto *Dtor = CompCtx.top().getCoreFunc(Idx);
    if (Dtor == nullptr) {
      spdlog::error(ErrCode::Value::InvalidIndex);
      spdlog::error("    Destructor core function index {} out of bounds."sv,
                    Idx);
      return Unexpect(ErrCode::Value::InvalidIndex);
    }
    // The destructor must have type [rep] -> [].
    const ValType Rep =
        RT.isAddrI64() ? ValType(TypeCode::I64) : ValType(TypeCode::I32);
    const auto &CT = Dtor->getCompositeType();
    if (!CT.isFunc() || CT.getFuncType().getParamTypes().size() != 1 ||
        CT.getFuncType().getParamTypes()[0] != Rep ||
        !CT.getFuncType().getReturnTypes().empty()) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Resource destructor must have type [{}] -> []."sv,
                    RT.isAddrI64() ? "i64"sv : "i32"sv);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
  }
  return {};
}

// core:deftype ::= rectype | moduletype. Rectypes push one core:type entry
// per subtype; moduletypes are validated in their own scope.
Expect<void>
Validator::validate(const AST::Component::CoreDefType &DType) noexcept {
  if (DType.isRecType()) {
    // Depth memoization for the core subtype hierarchy checks; resized on
    // demand by the core validator.
    std::vector<uint32_t> SubTypeDepthMap;
    for (const auto &ST : DType.getSubTypes()) {
      EXPECTED_TRY(validate(ST,
                            static_cast<uint32_t>(Checker.getTypes().size()),
                            SubTypeDepthMap));
      CompCtx.top().CoreTypes.push_back({&ST, nullptr});
    }
    return {};
  }
  EXPECTED_TRY(const auto *Info, validateModuleType(DType.getModuleType()));
  CompCtx.top().CoreTypes.push_back({nullptr, Info});
  return {};
}

Expect<void>
Validator::validate(const AST::Component::DefType &DType) noexcept {
  if (DType.isDefValType()) {
    EXPECTED_TRY(validate(DType.getDefValType()));
    auto &S = CompCtx.top();
    S.Types.push_back({&DType, &S, nullptr, nullptr, nullptr, {}});
  } else if (DType.isFuncType()) {
    EXPECTED_TRY(validate(DType.getFuncType()));
    auto &S = CompCtx.top();
    S.Types.push_back({&DType, &S, nullptr, nullptr, nullptr, {}});
  } else if (DType.isResourceType()) {
    EXPECTED_TRY(validate(DType.getResourceType()));
    auto &S = CompCtx.top();
    const uint32_t Id =
        CompCtx.addResource(&DType.getResourceType(), &S, false);
    S.Types.push_back({&DType, &S, nullptr, nullptr, nullptr, Id});
  } else if (DType.isInstanceType()) {
    EXPECTED_TRY(const auto *Info,
                 validateInstanceType(DType.getInstanceType()));
    auto &S = CompCtx.top();
    S.Types.push_back({&DType, &S, nullptr, Info, nullptr, {}});
  } else if (DType.isComponentType()) {
    EXPECTED_TRY(const auto *Info,
                 validateComponentType(DType.getComponentType()));
    auto &S = CompCtx.top();
    S.Types.push_back({&DType, &S, nullptr, nullptr, Info, {}});
  }
  return {};
}

// core:importdesc inside moduletype declarations; func/tag type indices
// resolve in the moduletype's own core type space.
Expect<ComponentContext::CoreExternInfo>
Validator::validate(const AST::Component::CoreImportDesc &Desc) noexcept {
  ComponentContext::CoreExternInfo Info;
  if (Desc.isFunc()) {
    const auto *Entry = CompCtx.top().getCoreType(Desc.getTypeIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::CoreTypeIndexOutOfBounds);
      spdlog::error("    Core type index {} out of bounds (size {})."sv,
                    Desc.getTypeIndex(), CompCtx.top().CoreTypes.size());
      return Unexpect(ErrCode::Value::CoreTypeIndexOutOfBounds);
    }
    if (Entry->Func == nullptr || !Entry->Func->getCompositeType().isFunc()) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Core type index {} is not a function type."sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    Info.Kind = ExternalType::Function;
    Info.Func = Entry->Func;
  } else if (Desc.isTable()) {
    EXPECTED_TRY(validate(Desc.getTableType()));
    Info.Kind = ExternalType::Table;
    Info.Table = &Desc.getTableType();
  } else if (Desc.isMemory()) {
    EXPECTED_TRY(validate(Desc.getMemoryType()));
    Info.Kind = ExternalType::Memory;
    Info.Memory = &Desc.getMemoryType();
  } else if (Desc.isGlobal()) {
    EXPECTED_TRY(validate(Desc.getGlobalType()));
    Info.Kind = ExternalType::Global;
    Info.Global = &Desc.getGlobalType();
  } else if (Desc.isTag()) {
    const uint32_t Idx = Desc.getTagType().getTypeIdx();
    const auto *Entry = CompCtx.top().getCoreType(Idx);
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::CoreTypeIndexOutOfBounds);
      spdlog::error("    Tag type index {} out of bounds."sv, Idx);
      return Unexpect(ErrCode::Value::CoreTypeIndexOutOfBounds);
    }
    if (Entry->Func == nullptr || !Entry->Func->getCompositeType().isFunc() ||
        !Entry->Func->getCompositeType()
             .getFuncType()
             .getReturnTypes()
             .empty()) {
      spdlog::error(ErrCode::Value::InvalidTagResultType);
      spdlog::error("    Tag types must be function types without results."sv);
      return Unexpect(ErrCode::Value::InvalidTagResultType);
    }
    Info.Kind = ExternalType::Tag;
    Info.Func = Entry->Func;
  }
  return Info;
}

// moduletype ::= 0x50 md*:vec(<core:moduledecl>). Runs in a ModuleType scope
// whose core type space is local to the declaration body.
Expect<const ComponentContext::CoreModuleInfo *> Validator::validateModuleType(
    Span<const AST::Component::CoreModuleDecl> Decls) noexcept {
  ComponentContext::ScopedScope Guard(
      CompCtx, ComponentContext::Scope::Kind::ModuleType);
  auto *Info = CompCtx.newCoreModuleInfo();
  for (const auto &Decl : Decls) {
    if (Decl.isImport()) {
      const auto &Imp = Decl.getImport();
      EXPECTED_TRY(auto Ext, validate(Imp.getImportDesc()));
      Info->Imports.emplace_back(std::string(Imp.getModuleName()),
                                 std::string(Imp.getName()), Ext);
    } else if (Decl.isType()) {
      const auto *T = Decl.getType();
      if (T == nullptr) {
        spdlog::error(ErrCode::Value::InvalidTypeReference);
        return Unexpect(ErrCode::Value::InvalidTypeReference);
      }
      // MVP: module types cannot define nested module types.
      if (T->isModuleType()) {
        spdlog::error(ErrCode::Value::InvalidTypeReference);
        spdlog::error("    Module types cannot define nested module types."sv);
        return Unexpect(ErrCode::Value::InvalidTypeReference);
      }
      EXPECTED_TRY(validate(*T));
    } else if (Decl.isAlias()) {
      EXPECTED_TRY(validate(Decl.getAlias()));
    } else if (Decl.isExport()) {
      const auto &Exp = Decl.getExport();
      EXPECTED_TRY(auto Ext, validate(Exp.getImportDesc()));
      if (!Info->Exports.emplace(std::string(Exp.getName()), Ext).second) {
        spdlog::error(ErrCode::Value::DupExportName);
        spdlog::error("    Module type export '{}' name conflict."sv,
                      Exp.getName());
        return Unexpect(ErrCode::Value::DupExportName);
      }
    }
  }
  return Info;
}

// core:alias inside moduletype declarations: only outer aliases of the core
// type sort are expressible; MVP additionally rejects aliasing module types.
Expect<void>
Validator::validate(const AST::Component::CoreAlias &Alias) noexcept {
  if (Alias.getSort().isCore() &&
      Alias.getSort().getCoreSortType() ==
          AST::Component::Sort::CoreSortType::Type) {
    const auto *Target = CompCtx.scopeUp(Alias.getComponentJump());
    if (Target == nullptr) {
      spdlog::error(ErrCode::Value::InvalidIndex);
      spdlog::error("    Outer alias count {} exceeds enclosing scopes."sv,
                    Alias.getComponentJump());
      return Unexpect(ErrCode::Value::InvalidIndex);
    }
    const auto *Entry = Target->getCoreType(Alias.getIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::CoreTypeIndexOutOfBounds);
      spdlog::error("    Aliased core type index {} out of bounds."sv,
                    Alias.getIndex());
      return Unexpect(ErrCode::Value::CoreTypeIndexOutOfBounds);
    }
    if (Entry->Mod != nullptr) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Module types cannot be aliased into module types."sv);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    CompCtx.top().CoreTypes.push_back(*Entry);
    return {};
  }
  spdlog::error(ErrCode::Value::MalformedAliasTarget);
  spdlog::error("    Core aliases can only target the core type sort."sv);
  return Unexpect(ErrCode::Value::MalformedAliasTarget);
}

Expect<const ComponentContext::InstanceInfo *> Validator::validateInstanceType(
    const AST::Component::InstanceType &IT) noexcept {
  ComponentContext::ScopedScope Guard(
      CompCtx, ComponentContext::Scope::Kind::InstanceType);
  auto *Info = CompCtx.newInstanceInfo();
  Info->DeclScope = &Guard.get();
  for (const auto &Decl : IT.getDecl()) {
    EXPECTED_TRY(validate(Decl, Info->Exports));
  }
  return Info;
}

Expect<const ComponentContext::ComponentInfo *>
Validator::validateComponentType(
    const AST::Component::ComponentType &CT) noexcept {
  ComponentContext::ScopedScope Guard(
      CompCtx, ComponentContext::Scope::Kind::ComponentType);
  auto *Info = CompCtx.newComponentInfo();
  Info->DeclScope = &Guard.get();
  for (const auto &Decl : CT.getDecl()) {
    EXPECTED_TRY(validate(Decl, *Info));
  }
  return Info;
}

Expect<void>
Validator::validate(const AST::Component::InstanceDecl &Decl,
                    ComponentContext::ExternMap &Exports) noexcept {
  if (Decl.isCoreType()) {
    const auto *T = Decl.getCoreType();
    if (T == nullptr) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    return validate(*T);
  }
  if (Decl.isType()) {
    const auto *T = Decl.getType();
    if (T == nullptr) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    return validate(*T);
  }
  if (Decl.isAlias()) {
    return validate(Decl.getAlias());
  }
  if (Decl.isExportDecl()) {
    const auto &ED = Decl.getExport();
    EXPECTED_TRY(ComponentName CN, parseExportName(ED.getName()));
    if (!ComponentContext::addUniqueName(
            CompCtx.top().ExportNames, ComponentContext::makeNameRecord(CN))) {
      spdlog::error(ErrCode::Value::ComponentDuplicateName);
      spdlog::error("    Export name '{}' is not strongly-unique."sv,
                    ED.getName());
      return Unexpect(ErrCode::Value::ComponentDuplicateName);
    }
    EXPECTED_TRY(auto Info, validate(ED.getExternDesc(), false));
    defineExtern(Info);
    EXPECTED_TRY(checkAnnotatedName(CN, Info));
    recordResourceLabel(CN, Info);
    Exports.emplace(std::string(ED.getName()), Info);
    return {};
  }
  spdlog::error(ErrCode::Value::InvalidTypeReference);
  return Unexpect(ErrCode::Value::InvalidTypeReference);
}

Expect<void>
Validator::validate(const AST::Component::ComponentDecl &Decl,
                    ComponentContext::ComponentInfo &Info) noexcept {
  if (Decl.isImportDecl()) {
    const auto &ID = Decl.getImport();
    EXPECTED_TRY(auto Ext, defineImport(ID.getName(), ID.getExternDesc()));
    Info.Imports.emplace_back(std::string(ID.getName()), Ext);
    return {};
  }
  return validate(Decl.getInstance(), Info.Exports);
}

// externdesc resolution: bounds/kind checks plus entity typing. Sub-resource
// type bounds allocate a fresh abstract id in the current scope.
Expect<ComponentContext::ExternInfo>
Validator::validate(const AST::Component::ExternDesc &Desc,
                    bool ImportSide) noexcept {
  using DescType = AST::Component::ExternDesc::DescType;
  ComponentContext::ExternInfo Info;
  auto &S = CompCtx.top();
  switch (Desc.getDescType()) {
  case DescType::CoreType: {
    const auto *Entry = S.getCoreType(Desc.getTypeIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::CoreTypeIndexOutOfBounds);
      spdlog::error("    Core type index {} out of bounds."sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::CoreTypeIndexOutOfBounds);
    }
    if (Entry->Mod == nullptr) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Core type index {} is not a module type."sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    Info.K = ComponentContext::ExternInfo::Kind::CoreModule;
    Info.CoreMod = Entry->Mod;
    return Info;
  }
  case DescType::FuncType: {
    const auto *Entry = S.getType(Desc.getTypeIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::InvalidIndex);
      spdlog::error("    Type index {} out of bounds (size {})."sv,
                    Desc.getTypeIndex(), S.Types.size());
      return Unexpect(ErrCode::Value::InvalidIndex);
    }
    if (Entry->DT == nullptr || !Entry->DT->isFuncType()) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Type index {} is not a function type."sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    Info.K = ComponentContext::ExternInfo::Kind::Func;
    Info.Func = {&Entry->DT->getFuncType(), Entry->Home, Entry->Remap};
    return Info;
  }
  case DescType::ValueBound: {
    Info.K = ComponentContext::ExternInfo::Kind::Value;
    if (Desc.isEqType()) {
      const uint32_t Idx = Desc.getTypeIndex();
      if (Idx >= S.Values.size()) {
        spdlog::error(ErrCode::Value::InvalidIndex);
        spdlog::error("    Value index {} out of bounds (size {})."sv, Idx,
                      S.Values.size());
        return Unexpect(ErrCode::Value::InvalidIndex);
      }
      Info.Value = S.Values[Idx].Type;
      return Info;
    }
    EXPECTED_TRY(validate(Desc.getValType()));
    Info.Value = {Desc.getValType(), &S, nullptr};
    return Info;
  }
  case DescType::TypeBound: {
    Info.K = ComponentContext::ExternInfo::Kind::Type;
    if (Desc.isEqType()) {
      const auto *Entry = S.getType(Desc.getTypeIndex());
      if (Entry == nullptr) {
        spdlog::error(ErrCode::Value::InvalidIndex);
        spdlog::error("    Type index {} out of bounds (size {})."sv,
                      Desc.getTypeIndex(), S.Types.size());
        return Unexpect(ErrCode::Value::InvalidIndex);
      }
      Info.Type = *Entry;
      return Info;
    }
    // (sub resource): fresh abstract resource type.
    const uint32_t Id = CompCtx.addResource(nullptr, &S, ImportSide);
    Info.Type = {nullptr, &S, nullptr, nullptr, nullptr, Id};
    return Info;
  }
  case DescType::ComponentType: {
    const auto *Entry = S.getType(Desc.getTypeIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::InvalidIndex);
      spdlog::error("    Type index {} out of bounds (size {})."sv,
                    Desc.getTypeIndex(), S.Types.size());
      return Unexpect(ErrCode::Value::InvalidIndex);
    }
    if (Entry->Comp == nullptr) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Type index {} is not a component type."sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    Info.K = ComponentContext::ExternInfo::Kind::Component;
    Info.Comp = Entry->Comp;
    return Info;
  }
  case DescType::InstanceType: {
    const auto *Entry = S.getType(Desc.getTypeIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::InvalidIndex);
      spdlog::error("    Type index {} out of bounds (size {})."sv,
                    Desc.getTypeIndex(), S.Types.size());
      return Unexpect(ErrCode::Value::InvalidIndex);
    }
    if (Entry->Inst == nullptr) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Type index {} is not an instance type."sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    Info.K = ComponentContext::ExternInfo::Kind::Instance;
    Info.Inst = Entry->Inst;
    return Info;
  }
  default:
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
}

void Validator::defineExtern(
    const ComponentContext::ExternInfo &Info) noexcept {
  auto &S = CompCtx.top();
  using Kind = ComponentContext::ExternInfo::Kind;
  switch (Info.K) {
  case Kind::CoreModule:
    S.CoreModules.push_back(Info.CoreMod);
    break;
  case Kind::Func:
    S.Funcs.push_back(Info.Func);
    break;
  case Kind::Value:
    S.Values.push_back({Info.Value, false});
    break;
  case Kind::Type:
    S.Types.push_back(Info.Type);
    break;
  case Kind::Instance:
    S.Instances.push_back(Info.Inst);
    break;
  case Kind::Component:
    S.Components.push_back(Info.Comp);
    break;
  }
}

Expect<ComponentName>
Validator::parseImportName(std::string_view Name) noexcept {
  // `relative-url=` is not part of the extern-name grammar.
  if (Name.rfind("relative-url="sv, 0) == 0) {
    spdlog::error(ErrCode::Value::InvalidExternName);
    spdlog::error("    Import name '{}' is not a valid extern name."sv, Name);
    return Unexpect(ErrCode::Value::InvalidExternName);
  }
  EXPECTED_TRY(ComponentName CN, ComponentName::parse(Name));
  if (CN.getKind() == ComponentNameKind::Invalid) {
    spdlog::error(ErrCode::Value::InvalidExternName);
    spdlog::error("    Import name '{}' is not a valid extern name."sv, Name);
    return Unexpect(ErrCode::Value::InvalidExternName);
  }
  return CN;
}

Expect<ComponentName>
Validator::parseExportName(std::string_view Name) noexcept {
  // `relative-url=` is not part of the extern-name grammar.
  if (Name.rfind("relative-url="sv, 0) == 0) {
    spdlog::error(ErrCode::Value::InvalidExternName);
    spdlog::error("    Export name '{}' is not a valid extern name."sv, Name);
    return Unexpect(ErrCode::Value::InvalidExternName);
  }
  EXPECTED_TRY(ComponentName CN, ComponentName::parse(Name));
  switch (CN.getKind()) {
  case ComponentNameKind::Label:
  case ComponentNameKind::Constructor:
  case ComponentNameKind::Method:
  case ComponentNameKind::Static:
  case ComponentNameKind::InterfaceType:
    return CN;
  case ComponentNameKind::Invalid:
    spdlog::error(ErrCode::Value::InvalidExternName);
    spdlog::error("    Export name '{}' is not a valid extern name."sv, Name);
    return Unexpect(ErrCode::Value::InvalidExternName);
  default:
    // Dep / url / hash names are import-only.
    spdlog::error(ErrCode::Value::InvalidExportName);
    spdlog::error("    Export name '{}' kind is not valid for exports."sv,
                  Name);
    return Unexpect(ErrCode::Value::InvalidExportName);
  }
}

Expect<ComponentContext::ExternInfo>
Validator::defineImport(std::string_view Name,
                        const AST::Component::ExternDesc &Desc) noexcept {
  EXPECTED_TRY(ComponentName CN, parseImportName(Name));
  if (!ComponentContext::addUniqueName(CompCtx.top().ImportNames,
                                       ComponentContext::makeNameRecord(CN))) {
    spdlog::error(ErrCode::Value::ComponentImportNameConflict);
    spdlog::error("    Import name '{}' is not strongly-unique."sv, Name);
    return Unexpect(ErrCode::Value::ComponentImportNameConflict);
  }
  EXPECTED_TRY(auto Info, validate(Desc, true));
  defineExtern(Info);
  EXPECTED_TRY(checkAnnotatedName(CN, Info));
  recordResourceLabel(CN, Info);
  return Info;
}

Expect<ComponentContext::ExternInfo> Validator::defineExport(
    std::string_view Name, const ComponentContext::ExternInfo &Inferred,
    const std::optional<AST::Component::ExternDesc> &Ascribed) noexcept {
  EXPECTED_TRY(ComponentName CN, parseExportName(Name));
  if (!ComponentContext::addUniqueName(CompCtx.top().ExportNames,
                                       ComponentContext::makeNameRecord(CN))) {
    spdlog::error(ErrCode::Value::ComponentDuplicateName);
    spdlog::error("    Export name '{}' is not strongly-unique."sv, Name);
    return Unexpect(ErrCode::Value::ComponentDuplicateName);
  }
  ComponentContext::ExternInfo Result = Inferred;
  if (Ascribed.has_value()) {
    EXPECTED_TRY(auto Asc, validate(*Ascribed, false));
    ResourceSubst Subst;
    if (!matchExtern(Inferred, Asc, Subst)) {
      spdlog::error(ErrCode::Value::ExportAscriptionIncompatible);
      spdlog::error(
          "    Ascribed type of export '{}' is not compatible with the "
          "exported definition."sv,
          Name);
      return Unexpect(ErrCode::Value::ExportAscriptionIncompatible);
    }
    Result = Asc;
  }
  defineExtern(Result);
  EXPECTED_TRY(checkAnnotatedName(CN, Result));
  recordResourceLabel(CN, Result);
  return Result;
}

// Annotated plainnames: [constructor]r / [method]r.m / [static]r.m are only
// valid on funcs whose signature agrees with resource r.
Expect<void> Validator::checkAnnotatedName(
    const ComponentName &Name,
    const ComponentContext::ExternInfo &Info) noexcept {
  const auto Kind = Name.getKind();
  if (Kind != ComponentNameKind::Constructor &&
      Kind != ComponentNameKind::Method && Kind != ComponentNameKind::Static) {
    return {};
  }
  if (Info.K != ComponentContext::ExternInfo::Kind::Func ||
      Info.Func.FT == nullptr) {
    spdlog::error(ErrCode::Value::ComponentInvalidName);
    spdlog::error(
        "    Annotated name '{}' is only allowed on function imports/exports."sv,
        Name.getOriginalName());
    return Unexpect(ErrCode::Value::ComponentInvalidName);
  }
  // The first label must match a preceding resource import/export.
  std::string_view ResourceLabel;
  if (Kind == ComponentNameKind::Constructor) {
    ResourceLabel = Name.getDetail().get<ConstructorDetail>().Label;
  } else if (Kind == ComponentNameKind::Method) {
    ResourceLabel = Name.getDetail().get<MethodDetail>().Resource;
  } else {
    ResourceLabel = Name.getDetail().get<StaticDetail>().Resource;
  }
  const auto &Labels = CompCtx.top().ResourceLabels;
  auto It = Labels.find(std::string(ResourceLabel));
  if (It == Labels.end()) {
    spdlog::error(ErrCode::Value::ComponentInvalidName);
    spdlog::error(
        "    Annotated name '{}' does not match a preceding resource '{}'."sv,
        Name.getOriginalName(), ResourceLabel);
    return Unexpect(ErrCode::Value::ComponentInvalidName);
  }
  const uint32_t ResId = It->second;
  const auto &FT = *Info.Func.FT;

  // Resolves a valtype to own/borrow of ResId.
  auto IsHandleOf = [this](const ComponentContext::QualValType &Q, bool WantOwn,
                           uint32_t Id) noexcept -> bool {
    ComponentContext::TypeEntry Storage;
    const auto *Entry = resolveQualType(Q, Storage);
    if (Entry == nullptr || Entry->DT == nullptr ||
        !Entry->DT->isDefValType()) {
      return false;
    }
    const auto &DVT = Entry->DT->getDefValType();
    uint32_t HandleIdx = 0;
    if (WantOwn && DVT.isOwnTy()) {
      HandleIdx = DVT.getOwn().Idx;
    } else if (!WantOwn && DVT.isBorrowTy()) {
      HandleIdx = DVT.getBorrow().Idx;
    } else {
      return false;
    }
    const auto *Res = Entry->Home->getType(HandleIdx);
    if (Res == nullptr || !Res->ResourceId.has_value()) {
      return false;
    }
    return ComponentContext::ResourceMap::apply(Entry->Remap,
                                                *Res->ResourceId) == Id;
  };

  if (Kind == ComponentNameKind::Constructor) {
    // Result must be (own R) or (result (own R) (error E)?).
    bool Ok = false;
    if (FT.getResultList().size() == 1) {
      ComponentContext::QualValType Q{FT.getResultList()[0].getValType(),
                                      Info.Func.Home, Info.Func.Remap};
      Ok = IsHandleOf(Q, true, ResId);
      if (!Ok) {
        ComponentContext::TypeEntry Storage;
        const auto *Entry = resolveQualType(Q, Storage);
        if (Entry != nullptr && Entry->DT != nullptr &&
            Entry->DT->isDefValType() &&
            Entry->DT->getDefValType().isResultTy()) {
          const auto &Res = Entry->DT->getDefValType().getResult();
          if (Res.ValTy.has_value()) {
            Ok = IsHandleOf({*Res.ValTy, Entry->Home, Entry->Remap}, true,
                            ResId);
          }
        }
      }
    }
    if (!Ok) {
      spdlog::error(ErrCode::Value::ComponentInvalidName);
      spdlog::error("    Constructor '{}' must return (own {})."sv,
                    Name.getOriginalName(), ResourceLabel);
      return Unexpect(ErrCode::Value::ComponentInvalidName);
    }
  } else if (Kind == ComponentNameKind::Method) {
    // First parameter must be (param "self" (borrow R)).
    bool Ok = false;
    if (!FT.getParamList().empty()) {
      const auto &Self = FT.getParamList()[0];
      Ok = Self.getLabel() == "self"sv &&
           IsHandleOf({Self.getValType(), Info.Func.Home, Info.Func.Remap},
                      false, ResId);
    }
    if (!Ok) {
      spdlog::error(ErrCode::Value::ComponentInvalidName);
      spdlog::error(
          "    Method '{}' must take (param \"self\" (borrow {})) first."sv,
          Name.getOriginalName(), ResourceLabel);
      return Unexpect(ErrCode::Value::ComponentInvalidName);
    }
  }
  return {};
}

void Validator::recordResourceLabel(
    const ComponentName &Name,
    const ComponentContext::ExternInfo &Info) noexcept {
  if (Name.getKind() == ComponentNameKind::Label &&
      Info.K == ComponentContext::ExternInfo::Kind::Type &&
      Info.Type.ResourceId.has_value()) {
    CompCtx.top().ResourceLabels.emplace(std::string(Name.getOriginalName()),
                                         *Info.Type.ResourceId);
  }
}

// External view of an inline core module: its imports in order and the
// resolved types of its exports.
Expect<const ComponentContext::CoreModuleInfo *>
Validator::buildCoreModuleInfo(const AST::Module &Mod) noexcept {
  auto *Info = CompCtx.newCoreModuleInfo();
  const auto &Types = Mod.getTypeSection().getContent();

  auto TypeAt = [&Types](uint32_t Idx) noexcept -> const AST::SubType * {
    return Idx < Types.size() ? &Types[Idx] : nullptr;
  };

  // Core index spaces: imports first, then definitions.
  std::vector<ComponentContext::CoreExternInfo> Funcs, Tables, Memories,
      Globals, Tags;
  for (const auto &Imp : Mod.getImportSection().getContent()) {
    ComponentContext::CoreExternInfo Ext;
    switch (Imp.getExternalType()) {
    case ExternalType::Function:
      Ext = {ExternalType::Function, TypeAt(Imp.getExternalFuncTypeIdx()),
             nullptr, nullptr, nullptr};
      Funcs.push_back(Ext);
      break;
    case ExternalType::Table:
      Ext = {ExternalType::Table, nullptr, &Imp.getExternalTableType(), nullptr,
             nullptr};
      Tables.push_back(Ext);
      break;
    case ExternalType::Memory:
      Ext = {ExternalType::Memory, nullptr, nullptr,
             &Imp.getExternalMemoryType(), nullptr};
      Memories.push_back(Ext);
      break;
    case ExternalType::Global:
      Ext = {ExternalType::Global, nullptr, nullptr, nullptr,
             &Imp.getExternalGlobalType()};
      Globals.push_back(Ext);
      break;
    case ExternalType::Tag:
      Ext = {ExternalType::Tag, TypeAt(Imp.getExternalTagType().getTypeIdx()),
             nullptr, nullptr, nullptr};
      Tags.push_back(Ext);
      break;
    default:
      break;
    }
    Info->Imports.emplace_back(std::string(Imp.getModuleName()),
                               std::string(Imp.getExternalName()), Ext);
  }
  for (const auto TIdx : Mod.getFunctionSection().getContent()) {
    Funcs.push_back(
        {ExternalType::Function, TypeAt(TIdx), nullptr, nullptr, nullptr});
  }
  for (const auto &Seg : Mod.getTableSection().getContent()) {
    Tables.push_back(
        {ExternalType::Table, nullptr, &Seg.getTableType(), nullptr, nullptr});
  }
  for (const auto &MT : Mod.getMemorySection().getContent()) {
    Memories.push_back({ExternalType::Memory, nullptr, nullptr, &MT, nullptr});
  }
  for (const auto &Seg : Mod.getGlobalSection().getContent()) {
    Globals.push_back({ExternalType::Global, nullptr, nullptr, nullptr,
                       &Seg.getGlobalType()});
  }
  for (const auto &TT : Mod.getTagSection().getContent()) {
    Tags.push_back({ExternalType::Tag, TypeAt(TT.getTypeIdx()), nullptr,
                    nullptr, nullptr});
  }

  for (const auto &Exp : Mod.getExportSection().getContent()) {
    const uint32_t Idx = Exp.getExternalIndex();
    ComponentContext::CoreExternInfo Ext;
    switch (Exp.getExternalType()) {
    case ExternalType::Function:
      if (Idx >= Funcs.size()) {
        continue;
      }
      Ext = Funcs[Idx];
      break;
    case ExternalType::Table:
      if (Idx >= Tables.size()) {
        continue;
      }
      Ext = Tables[Idx];
      break;
    case ExternalType::Memory:
      if (Idx >= Memories.size()) {
        continue;
      }
      Ext = Memories[Idx];
      break;
    case ExternalType::Global:
      if (Idx >= Globals.size()) {
        continue;
      }
      Ext = Globals[Idx];
      break;
    case ExternalType::Tag:
      if (Idx >= Tags.size()) {
        continue;
      }
      Ext = Tags[Idx];
      break;
    default:
      continue;
    }
    Info->Exports.emplace(std::string(Exp.getExternalName()), Ext);
  }
  return Info;
}

} // namespace Validator
} // namespace WasmEdge
