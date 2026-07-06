// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2019-2025 Second State INC

//===-- component_canon.cpp - Canonical built-in validation ---------------===//
//
// Validation of canon lift / lower / resource.* definitions, including the
// validator-side implementation of the canonical ABI `flatten_functype`.
//
//===----------------------------------------------------------------------===//

#include "common/errinfo.h"
#include "common/spdlog.h"
#include "validator/validator.h"

#include <vector>

namespace WasmEdge {
namespace Validator {

using namespace std::literals;

// NOLINTBEGIN(misc-no-recursion) -- type structures are finitely nested.

// Spec flatten_type: appends the flat core types of Q. Returns false for
// types that cannot be flattened (async-gated ones).
bool Validator::flattenValType(const CtxView::QualValType &Q,
                               std::vector<ValType> &Out) noexcept {
  const auto N = normalizeValType(Q);
  if (!N.Valid) {
    return false;
  }
  if (N.DVT == nullptr) {
    switch (N.Prim) {
    case ComponentTypeCode::Bool:
    case ComponentTypeCode::S8:
    case ComponentTypeCode::U8:
    case ComponentTypeCode::S16:
    case ComponentTypeCode::U16:
    case ComponentTypeCode::S32:
    case ComponentTypeCode::U32:
    case ComponentTypeCode::Char:
      Out.push_back(ValType(TypeCode::I32));
      return true;
    case ComponentTypeCode::S64:
    case ComponentTypeCode::U64:
      Out.push_back(ValType(TypeCode::I64));
      return true;
    case ComponentTypeCode::F32:
      Out.push_back(ValType(TypeCode::F32));
      return true;
    case ComponentTypeCode::F64:
      Out.push_back(ValType(TypeCode::F64));
      return true;
    case ComponentTypeCode::String:
      Out.push_back(ValType(TypeCode::I32));
      Out.push_back(ValType(TypeCode::I32));
      return true;
    default:
      return false;
    }
  }
  const auto &D = *N.DVT;
  auto Sub = [&](const ComponentValType &VT) noexcept {
    return flattenValType({VT, N.Home, N.Remap}, Out);
  };
  if (D.isRecordTy()) {
    for (const auto &LT : D.getRecord().LabelTypes) {
      if (!Sub(LT.getValType())) {
        return false;
      }
    }
    return true;
  }
  if (D.isTupleTy()) {
    for (const auto &Ty : D.getTuple().Types) {
      if (!Sub(Ty)) {
        return false;
      }
    }
    return true;
  }
  if (D.isListTy()) {
    const auto &L = D.getList();
    if (L.Len.has_value()) {
      // Fixed-length lists flatten to Len copies of the element.
      for (uint32_t I = 0; I < *L.Len; ++I) {
        if (!Sub(L.ValTy)) {
          return false;
        }
      }
      return true;
    }
    Out.push_back(ValType(TypeCode::I32));
    Out.push_back(ValType(TypeCode::I32));
    return true;
  }
  if (D.isFlagsTy() || D.isEnumTy() || D.isOwnTy() || D.isBorrowTy()) {
    Out.push_back(ValType(TypeCode::I32));
    return true;
  }
  if (D.isVariantTy() || D.isOptionTy() || D.isResultTy()) {
    // flatten_variant: discriminant + element-wise join of the payloads.
    std::vector<std::vector<ComponentValType>> Payloads;
    if (D.isVariantTy()) {
      for (const auto &[Label, Ty] : D.getVariant().Cases) {
        if (Ty.has_value()) {
          Payloads.push_back({*Ty});
        } else {
          Payloads.push_back({});
        }
      }
    } else if (D.isOptionTy()) {
      Payloads.push_back({});
      Payloads.push_back({D.getOption().ValTy});
    } else {
      const auto &R = D.getResult();
      Payloads.push_back(R.ValTy.has_value()
                             ? std::vector<ComponentValType>{*R.ValTy}
                             : std::vector<ComponentValType>{});
      Payloads.push_back(R.ErrTy.has_value()
                             ? std::vector<ComponentValType>{*R.ErrTy}
                             : std::vector<ComponentValType>{});
    }
    auto Join = [](ValType A, ValType B) noexcept {
      if (A == B) {
        return A;
      }
      if ((A.getCode() == TypeCode::I32 && B.getCode() == TypeCode::F32) ||
          (A.getCode() == TypeCode::F32 && B.getCode() == TypeCode::I32)) {
        return ValType(TypeCode::I32);
      }
      return ValType(TypeCode::I64);
    };
    std::vector<ValType> Joined;
    for (const auto &Payload : Payloads) {
      std::vector<ValType> Flat;
      for (const auto &Ty : Payload) {
        if (!flattenValType({Ty, N.Home, N.Remap}, Flat)) {
          return false;
        }
      }
      for (size_t I = 0; I < Flat.size(); ++I) {
        if (I < Joined.size()) {
          Joined[I] = Join(Joined[I], Flat[I]);
        } else {
          Joined.push_back(Flat[I]);
        }
      }
    }
    Out.push_back(ValType(TypeCode::I32));
    Out.insert(Out.end(), Joined.begin(), Joined.end());
    return true;
  }
  return false;
}

// True iff the type transitively contains a list or string (drives the
// memory / realloc option requirements).
bool Validator::needsMemory(const CtxView::QualValType &Q) noexcept {
  const auto N = normalizeValType(Q);
  if (!N.Valid) {
    return false;
  }
  if (N.DVT == nullptr) {
    return N.Prim == ComponentTypeCode::String;
  }
  const auto &D = *N.DVT;
  auto Sub = [&](const ComponentValType &VT) noexcept {
    return needsMemory({VT, N.Home, N.Remap});
  };
  if (D.isListTy()) {
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

// NOLINTEND(misc-no-recursion)

// Shared canonopt structural rules: duplicates, index validity, and the
// per-site option whitelist.
Expect<void>
Validator::validateCanonOptions(const AST::Component::Canonical &Canon,
                                bool IsLift) noexcept {
  bool SeenEncoding = false, SeenMemory = false, SeenRealloc = false,
       SeenPostReturn = false;
  for (const auto &Opt : Canon.getOptions()) {
    switch (Opt.getCode()) {
    case ComponentCanonOptCode::Encode_UTF8:
    case ComponentCanonOptCode::Encode_UTF16:
    case ComponentCanonOptCode::Encode_Latin1:
      if (SeenEncoding) {
        spdlog::error(ErrCode::Value::InvalidCanonOption);
        spdlog::error("    Duplicate string-encoding canonical option."sv);
        return Unexpect(ErrCode::Value::InvalidCanonOption);
      }
      SeenEncoding = true;
      break;
    case ComponentCanonOptCode::Memory: {
      if (SeenMemory) {
        spdlog::error(ErrCode::Value::InvalidCanonOption);
        spdlog::error("    Duplicate memory canonical option."sv);
        return Unexpect(ErrCode::Value::InvalidCanonOption);
      }
      SeenMemory = true;
      const uint32_t Idx = Opt.getIndex();
      if (Idx >= CompCtx.top().CoreMemories.size()) {
        spdlog::error(ErrCode::Value::InvalidIndex);
        spdlog::error("    Canonical option memory index {} out of bounds."sv,
                      Idx);
        return Unexpect(ErrCode::Value::InvalidIndex);
      }
      const auto *Mem = CompCtx.top().CoreMemories[Idx];
      if (Mem != nullptr && Mem->getLimit().is64()) {
        spdlog::error(ErrCode::Value::ComponentCanonMemoryNot32Bit);
        spdlog::error(
            "    Canonical ABI memory must be a 32-bit linear memory."sv);
        return Unexpect(ErrCode::Value::ComponentCanonMemoryNot32Bit);
      }
      break;
    }
    case ComponentCanonOptCode::Realloc: {
      if (SeenRealloc) {
        spdlog::error(ErrCode::Value::InvalidCanonOption);
        spdlog::error("    Duplicate realloc canonical option."sv);
        return Unexpect(ErrCode::Value::InvalidCanonOption);
      }
      SeenRealloc = true;
      const auto *Func = CompCtx.top().getCoreFunc(Opt.getIndex());
      if (Func == nullptr) {
        spdlog::error(ErrCode::Value::InvalidIndex);
        spdlog::error(
            "    Canonical option realloc function index {} out of bounds."sv,
            Opt.getIndex());
        return Unexpect(ErrCode::Value::InvalidIndex);
      }
      // realloc must have type [i32 i32 i32 i32] -> [i32].
      static const std::vector<ValType> ReallocParams(4,
                                                      ValType(TypeCode::I32));
      static const std::vector<ValType> ReallocResults(1,
                                                       ValType(TypeCode::I32));
      const auto &CT = Func->getCompositeType();
      if (!CT.isFunc() || CT.getFuncType().getParamTypes() != ReallocParams ||
          CT.getFuncType().getReturnTypes() != ReallocResults) {
        spdlog::error(ErrCode::Value::InvalidCanonOption);
        spdlog::error(
            "    realloc must have type [i32 i32 i32 i32] -> [i32]."sv);
        return Unexpect(ErrCode::Value::InvalidCanonOption);
      }
      break;
    }
    case ComponentCanonOptCode::PostReturn:
      if (!IsLift || SeenPostReturn) {
        spdlog::error(ErrCode::Value::InvalidCanonOption);
        spdlog::error("    post-return is only allowed once on canon lift."sv);
        return Unexpect(ErrCode::Value::InvalidCanonOption);
      }
      SeenPostReturn = true;
      // The signature is checked in validateCanonLift once the flat type of
      // the lifted function is known.
      break;
    case ComponentCanonOptCode::Async:
    case ComponentCanonOptCode::Callback:
    case ComponentCanonOptCode::AlwaysTaskReturn:
      spdlog::error(ErrCode::Value::ComponentNotImplValidator);
      spdlog::error("    async canonical options are not supported yet."sv);
      return Unexpect(ErrCode::Value::ComponentNotImplValidator);
    default:
      spdlog::error(ErrCode::Value::UnknownCanonicalOption);
      return Unexpect(ErrCode::Value::UnknownCanonicalOption);
    }
  }
  if (SeenRealloc && !SeenMemory) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    realloc requires the memory canonical option."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }
  return {};
}

namespace {
// Option presence probes shared by lift/lower requirement checks.
bool hasOpt(const AST::Component::Canonical &Canon,
            ComponentCanonOptCode Code) noexcept {
  for (const auto &Opt : Canon.getOptions()) {
    if (Opt.getCode() == Code) {
      return true;
    }
  }
  return false;
}
} // namespace

Expect<void>
Validator::validateCanonLift(const AST::Component::Canonical &Canon) noexcept {
  auto &S = CompCtx.top();
  // Target function type.
  const auto *Entry = S.getType(Canon.getTargetIndex());
  if (Entry == nullptr) {
    spdlog::error(ErrCode::Value::InvalidIndex);
    spdlog::error("    canon lift type index {} out of bounds."sv,
                  Canon.getTargetIndex());
    return Unexpect(ErrCode::Value::InvalidIndex);
  }
  if (Entry->DT == nullptr || !Entry->DT->isFuncType()) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error("    canon lift type index {} is not a function type."sv,
                  Canon.getTargetIndex());
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  const CtxView::FuncInfo FI{&Entry->DT->getFuncType(), Entry->Home,
                             Entry->Remap};
  EXPECTED_TRY(validateCanonOptions(Canon, true));

  // Flatten parameters and results in the 'lift' context.
  std::vector<ValType> FlatParams, FlatResults;
  bool ParamsNeedMemory = false, ResultsNeedMemory = false;
  for (const auto &P : FI.FT->getParamList()) {
    if (!flattenValType({P.getValType(), FI.Home, FI.Remap}, FlatParams)) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    ParamsNeedMemory =
        ParamsNeedMemory || needsMemory({P.getValType(), FI.Home, FI.Remap});
  }
  for (const auto &R : FI.FT->getResultList()) {
    if (!flattenValType({R.getValType(), FI.Home, FI.Remap}, FlatResults)) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    ResultsNeedMemory =
        ResultsNeedMemory || needsMemory({R.getValType(), FI.Home, FI.Remap});
  }
  const bool ParamsIndirect = FlatParams.size() > MaxFlatParams;
  const bool ResultsIndirect = FlatResults.size() > MaxFlatResults;
  if (ParamsIndirect) {
    FlatParams.assign(1, ValType(TypeCode::I32));
  }
  if (ResultsIndirect) {
    FlatResults.assign(1, ValType(TypeCode::I32));
  }
  // Required options: lifting params lowers them into the callee's memory.
  if ((ParamsNeedMemory || ParamsIndirect) &&
      !hasOpt(Canon, ComponentCanonOptCode::Realloc)) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    canon lift requires the realloc option."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }
  if ((ParamsNeedMemory || ResultsNeedMemory || ParamsIndirect ||
       ResultsIndirect) &&
      !hasOpt(Canon, ComponentCanonOptCode::Memory)) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    canon lift requires the memory option."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }

  // The callee must have exactly the flattened core type.
  const auto *Callee = S.getCoreFunc(Canon.getIndex());
  if (Callee == nullptr) {
    spdlog::error(ErrCode::Value::InvalidIndex);
    spdlog::error("    canon lift core function index {} out of bounds."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidIndex);
  }
  const auto &CT = Callee->getCompositeType();
  if (!CT.isFunc() || CT.getFuncType().getParamTypes() != FlatParams ||
      CT.getFuncType().getReturnTypes() != FlatResults) {
    spdlog::error(ErrCode::Value::ArgTypeMismatch);
    spdlog::error(
        "    canon lift core function does not match the flattened type."sv);
    return Unexpect(ErrCode::Value::ArgTypeMismatch);
  }

  // post-return has type (func (param flat_results)).
  for (const auto &Opt : Canon.getOptions()) {
    if (Opt.getCode() == ComponentCanonOptCode::PostReturn) {
      const auto *Post = S.getCoreFunc(Opt.getIndex());
      if (Post == nullptr) {
        spdlog::error(ErrCode::Value::InvalidIndex);
        spdlog::error("    post-return core function index {} out of bounds."sv,
                      Opt.getIndex());
        return Unexpect(ErrCode::Value::InvalidIndex);
      }
      const auto &PT = Post->getCompositeType();
      if (!PT.isFunc() || PT.getFuncType().getParamTypes() != FlatResults ||
          !PT.getFuncType().getReturnTypes().empty()) {
        spdlog::error(ErrCode::Value::InvalidCanonOption);
        spdlog::error(
            "    post-return must take the lifted core results and return "
            "nothing."sv);
        return Unexpect(ErrCode::Value::InvalidCanonOption);
      }
    }
  }

  S.Funcs.push_back(FI);
  return {};
}

Expect<void>
Validator::validateCanonLower(const AST::Component::Canonical &Canon) noexcept {
  auto &S = CompCtx.top();
  const auto *FI = S.getFunc(Canon.getIndex());
  if (FI == nullptr) {
    spdlog::error(ErrCode::Value::InvalidIndex);
    spdlog::error("    canon lower function index {} out of bounds."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidIndex);
  }
  EXPECTED_TRY(validateCanonOptions(Canon, false));

  std::vector<ValType> FlatParams, FlatResults;
  bool ParamsNeedMemory = false, ResultsNeedMemory = false;
  for (const auto &P : FI->FT->getParamList()) {
    if (!flattenValType({P.getValType(), FI->Home, FI->Remap}, FlatParams)) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    ParamsNeedMemory =
        ParamsNeedMemory || needsMemory({P.getValType(), FI->Home, FI->Remap});
  }
  for (const auto &R : FI->FT->getResultList()) {
    if (!flattenValType({R.getValType(), FI->Home, FI->Remap}, FlatResults)) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    ResultsNeedMemory =
        ResultsNeedMemory || needsMemory({R.getValType(), FI->Home, FI->Remap});
  }
  const bool ParamsIndirect = FlatParams.size() > MaxFlatParams;
  const bool ResultsIndirect = FlatResults.size() > MaxFlatResults;
  if (ParamsIndirect) {
    FlatParams.assign(1, ValType(TypeCode::I32));
  }
  if (ResultsIndirect) {
    // The caller passes a pointer for the results as the last parameter.
    FlatParams.push_back(ValType(TypeCode::I32));
    FlatResults.clear();
  }
  if ((ResultsNeedMemory) && !hasOpt(Canon, ComponentCanonOptCode::Realloc)) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    canon lower requires the realloc option."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }
  if ((ParamsNeedMemory || ResultsNeedMemory || ParamsIndirect ||
       ResultsIndirect) &&
      !hasOpt(Canon, ComponentCanonOptCode::Memory)) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    canon lower requires the memory option."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }

  S.CoreFuncs.push_back(CompCtx.makeCoreFuncType(FlatParams, FlatResults));
  return {};
}

Expect<void> Validator::validateCanonResourceNew(
    const AST::Component::Canonical &Canon) noexcept {
  auto &S = CompCtx.top();
  if (!Canon.getOptions().empty()) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    resource built-ins take no canonical options."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }
  const auto *Entry = S.getType(Canon.getIndex());
  if (Entry == nullptr) {
    spdlog::error(ErrCode::Value::InvalidIndex);
    spdlog::error("    resource.new type index {} out of bounds."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidIndex);
  }
  if (!Entry->ResourceId.has_value()) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error("    resource.new type index {} is not a resource."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  const auto &Res = CompCtx.getResource(*Entry->ResourceId);
  if (Res.RT == nullptr || Res.Origin != &S) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error(
        "    resource.new requires a locally-defined resource type."sv);
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  const ValType Rep =
      Res.RT->isAddrI64() ? ValType(TypeCode::I64) : ValType(TypeCode::I32);
  const std::vector<ValType> Params{Rep}, Results{ValType(TypeCode::I32)};
  S.CoreFuncs.push_back(CompCtx.makeCoreFuncType(Params, Results));
  return {};
}

Expect<void> Validator::validateCanonResourceRep(
    const AST::Component::Canonical &Canon) noexcept {
  auto &S = CompCtx.top();
  if (!Canon.getOptions().empty()) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    resource built-ins take no canonical options."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }
  const auto *Entry = S.getType(Canon.getIndex());
  if (Entry == nullptr) {
    spdlog::error(ErrCode::Value::InvalidIndex);
    spdlog::error("    resource.rep type index {} out of bounds."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidIndex);
  }
  if (!Entry->ResourceId.has_value()) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error("    resource.rep type index {} is not a resource."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  const auto &Res = CompCtx.getResource(*Entry->ResourceId);
  if (Res.RT == nullptr || Res.Origin != &S) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error(
        "    resource.rep requires a locally-defined resource type."sv);
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  const ValType Rep =
      Res.RT->isAddrI64() ? ValType(TypeCode::I64) : ValType(TypeCode::I32);
  const std::vector<ValType> Params{ValType(TypeCode::I32)}, Results{Rep};
  S.CoreFuncs.push_back(CompCtx.makeCoreFuncType(Params, Results));
  return {};
}

Expect<void> Validator::validateCanonResourceDrop(
    const AST::Component::Canonical &Canon) noexcept {
  auto &S = CompCtx.top();
  if (!Canon.getOptions().empty()) {
    spdlog::error(ErrCode::Value::InvalidCanonOption);
    spdlog::error("    resource built-ins take no canonical options."sv);
    return Unexpect(ErrCode::Value::InvalidCanonOption);
  }
  const auto *Entry = S.getType(Canon.getIndex());
  if (Entry == nullptr) {
    spdlog::error(ErrCode::Value::InvalidIndex);
    spdlog::error("    resource.drop type index {} out of bounds."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidIndex);
  }
  if (!Entry->ResourceId.has_value()) {
    spdlog::error(ErrCode::Value::InvalidTypeReference);
    spdlog::error("    resource.drop type index {} is not a resource."sv,
                  Canon.getIndex());
    return Unexpect(ErrCode::Value::InvalidTypeReference);
  }
  const std::vector<ValType> Params{ValType(TypeCode::I32)};
  const std::vector<ValType> Results;
  S.CoreFuncs.push_back(CompCtx.makeCoreFuncType(Params, Results));
  return {};
}

Expect<void>
Validator::validate(const AST::Component::Canonical &Canon) noexcept {
  switch (Canon.getOpCode()) {
  case ComponentCanonOpCode::Lift:
    return validateCanonLift(Canon);
  case ComponentCanonOpCode::Lower:
    return validateCanonLower(Canon);
  case ComponentCanonOpCode::Resource__new:
    return validateCanonResourceNew(Canon);
  case ComponentCanonOpCode::Resource__rep:
    return validateCanonResourceRep(Canon);
  case ComponentCanonOpCode::Resource__drop:
  case ComponentCanonOpCode::Resource__drop_async:
    return validateCanonResourceDrop(Canon);
  default:
    spdlog::error(ErrCode::Value::ComponentNotImplValidator);
    spdlog::error("    canonical built-in {} is not supported yet."sv,
                  static_cast<uint32_t>(Canon.getOpCode()));
    return Unexpect(ErrCode::Value::ComponentNotImplValidator);
  }
}

} // namespace Validator
} // namespace WasmEdge
