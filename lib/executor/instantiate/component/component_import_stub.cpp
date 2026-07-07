// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2019-2025 Second State INC

//===-- component_import_stub.cpp - permissive root import synthesis ------===//
//
// When the runtime configuration enables component permissive imports, the
// root instantiation satisfies missing imports with synthesized stubs: fresh
// resource types, host functions returning default values, instances
// mirroring their declared shape, and shape-backed host components. Spec
// test suites instantiate components whose imports the embedder never
// provides; this mode supplies the same "universal host" a wast runner
// implies.
//
//===----------------------------------------------------------------------===//

#include "common/errcode.h"
#include "common/spdlog.h"
#include "executor/executor.h"
#include "runtime/instance/component/function.h"

#include <string>
#include <vector>

namespace WasmEdge {
namespace Executor {

using namespace std::literals;
using namespace AST::Component;
using Runtime::Instance::ComponentInstance;
using CompFuncInst = Runtime::Instance::Component::FunctionInstance;

namespace {

// Default value of a component value type, resolving type indices in the
// given instance's type space.
// NOLINTNEXTLINE(misc-no-recursion)
ComponentValVariant defaultValue(const ComponentValType &VT,
                                 const ComponentInstance *Home,
                                 uint32_t Depth = 0) noexcept {
  using TC = ComponentTypeCode;
  if (Depth > 64) {
    return ComponentValVariant{uint32_t(0)};
  }
  switch (VT.getCode()) {
  case TC::Bool:
    return ComponentValVariant{false};
  case TC::S8:
    return ComponentValVariant{int8_t(0)};
  case TC::U8:
    return ComponentValVariant{uint8_t(0)};
  case TC::S16:
    return ComponentValVariant{int16_t(0)};
  case TC::U16:
    return ComponentValVariant{uint16_t(0)};
  case TC::S32:
    return ComponentValVariant{int32_t(0)};
  case TC::U32:
    return ComponentValVariant{uint32_t(0)};
  case TC::S64:
    return ComponentValVariant{int64_t(0)};
  case TC::U64:
    return ComponentValVariant{uint64_t(0)};
  case TC::F32:
    return ComponentValVariant{0.0f};
  case TC::F64:
    return ComponentValVariant{0.0};
  case TC::Char:
    return ComponentValVariant{uint32_t('0')};
  case TC::String:
    return ComponentValVariant{std::string()};
  case TC::TypeIndex:
    break;
  default:
    return ComponentValVariant{uint32_t(0)};
  }
  const auto *DT = Home != nullptr ? Home->getType(VT.getTypeIndex()) : nullptr;
  if (DT == nullptr || !DT->isDefValType()) {
    // Abstract resources reach here: a null own handle.
    return makeComponentVal(OwnVal{0});
  }
  const auto &D = DT->getDefValType();
  if (D.isPrimValType()) {
    ComponentValType Prim(static_cast<ComponentTypeCode>(D.getPrimValType()));
    return defaultValue(Prim, Home, Depth + 1);
  }
  if (D.isRecordTy()) {
    RecordVal R;
    for (const auto &LT : D.getRecord().LabelTypes) {
      R.Fields.emplace_back(std::string(LT.getLabel()),
                            defaultValue(LT.getValType(), Home, Depth + 1));
    }
    return makeComponentVal(std::move(R));
  }
  if (D.isVariantTy()) {
    const auto &Cases = D.getVariant().Cases;
    VariantVal V{0, std::nullopt};
    if (!Cases.empty() && Cases[0].second.has_value()) {
      V.Payload = defaultValue(*Cases[0].second, Home, Depth + 1);
    }
    return makeComponentVal(std::move(V));
  }
  if (D.isListTy()) {
    return makeComponentVal(ListVal{});
  }
  if (D.isTupleTy()) {
    TupleVal T;
    for (const auto &Ty : D.getTuple().Types) {
      T.Values.push_back(defaultValue(Ty, Home, Depth + 1));
    }
    return makeComponentVal(std::move(T));
  }
  if (D.isFlagsTy()) {
    FlagsVal F;
    F.Bits.assign(D.getFlags().Labels.size(), false);
    return makeComponentVal(std::move(F));
  }
  if (D.isEnumTy()) {
    return makeComponentVal(EnumVal{0});
  }
  if (D.isOptionTy()) {
    return makeComponentVal(OptionVal{std::nullopt});
  }
  if (D.isResultTy()) {
    const auto &R = D.getResult();
    ResultVal RV{true, std::nullopt};
    if (R.ValTy.has_value()) {
      RV.Payload = defaultValue(*R.ValTy, Home, Depth + 1);
    }
    return makeComponentVal(std::move(RV));
  }
  if (D.isOwnTy()) {
    return makeComponentVal(OwnVal{0});
  }
  if (D.isBorrowTy()) {
    return makeComponentVal(BorrowVal{0});
  }
  return ComponentValVariant{uint32_t(0)};
}

// A host function for the given component function type: returns default
// values for every declared result.
std::unique_ptr<CompFuncInst>
stubHostFunc(const FuncType &FT, const ComponentInstance *Home) noexcept {
  auto Owned = std::make_unique<FuncType>(FT);
  CompFuncInst::HostFuncCallback Cb = [FTPtr = Owned.get(),
                                       Home](Span<const ComponentValVariant>)
      -> Expect<std::vector<std::pair<ComponentValVariant, ComponentValType>>> {
    std::vector<std::pair<ComponentValVariant, ComponentValType>> Out;
    for (const auto &R : FTPtr->getResultList()) {
      Out.emplace_back(defaultValue(R.getValType(), Home), R.getValType());
    }
    return Out;
  };
  return std::make_unique<CompFuncInst>(std::move(Owned), std::move(Cb), Home);
}

} // namespace

// NOLINTNEXTLINE(misc-no-recursion)
Expect<std::unique_ptr<Runtime::Instance::ComponentInstance>>
Executor::synthesizeInstanceStub(
    Runtime::Instance::ComponentInstance &Owner,
    Span<const AST::Component::InstanceDecl *const> Decls) {
  auto Stub = std::make_unique<ComponentInstance>("");
  Stub->setParent(&Owner);
  for (const auto *Decl : Decls) {
    if (Decl->isCoreType()) {
      if (const auto *CT = Decl->getCoreType()) {
        Stub->addCoreType(*CT);
      }
    } else if (Decl->isType()) {
      if (const auto *DT = Decl->getType()) {
        Stub->addType(*DT);
      }
    } else if (Decl->isAlias()) {
      const auto &A = Decl->getAlias();
      const auto &Sort = A.getSort();
      if (A.getTargetType() == Alias::TargetType::Outer && !Sort.isCore() &&
          Sort.getSortType() == Sort::SortType::Type) {
        // Resolve against the owner chain: one hop out of the shape is the
        // owner itself.
        const auto &Outer = A.getOuter();
        const ComponentInstance *Target = &Owner;
        for (uint32_t I = 1; I < Outer.first && Target != nullptr; ++I) {
          Target = Target->getParent();
        }
        if (Target != nullptr) {
          Stub->addTypeWithResource(Target->getType(Outer.second),
                                    Target->getTypeResource(Outer.second));
        } else {
          Stub->addDummyType();
        }
      } else if (A.getTargetType() == Alias::TargetType::Export &&
                 !Sort.isCore() && Sort.getSortType() == Sort::SortType::Type) {
        const auto &Export = A.getExport();
        const auto *CInst = Stub->getComponentInstance(Export.first);
        if (CInst != nullptr) {
          Stub->addTypeWithResource(CInst->findType(Export.second),
                                    CInst->findTypeResource(Export.second));
        } else {
          Stub->addDummyType();
        }
      }
      // Other alias sorts carry no state a stub needs.
    } else if (Decl->isExportDecl()) {
      const auto &ED = Decl->getExport();
      const auto &Desc = ED.getExternDesc();
      switch (Desc.getDescType()) {
      case ExternDesc::DescType::FuncType: {
        const auto *DT = Stub->getType(Desc.getTypeIndex());
        if (DT != nullptr && DT->isFuncType()) {
          Stub->addHostFunc(ED.getName(),
                            stubHostFunc(DT->getFuncType(), Stub.get()));
        }
        break;
      }
      case ExternDesc::DescType::TypeBound: {
        if (Desc.isEqType()) {
          const uint32_t Idx = Desc.getTypeIndex();
          Stub->addTypeWithResource(Stub->getType(Idx),
                                    Stub->getTypeResource(Idx));
        } else {
          Stub->addHostResourceType(nullptr);
        }
        Stub->exportType(ED.getName(), Stub->getTypeCount() - 1);
        break;
      }
      case ExternDesc::DescType::InstanceType: {
        const auto *DT = Stub->getType(Desc.getTypeIndex());
        if (DT != nullptr && DT->isInstanceType()) {
          std::vector<const InstanceDecl *> Sub;
          for (const auto &D : DT->getInstanceType().getDecl()) {
            Sub.push_back(&D);
          }
          EXPECTED_TRY(auto Nested, synthesizeInstanceStub(*Stub, Sub));
          const ComponentInstance *Ptr = Nested.get();
          Stub->addComponentInstance(std::move(Nested));
          (void)Ptr;
          Stub->exportComponentInstance(
              ED.getName(),
              static_cast<uint32_t>(Stub->getComponentInstanceCount() - 1));
        }
        break;
      }
      case ExternDesc::DescType::ComponentType: {
        const auto *DT = Stub->getType(Desc.getTypeIndex());
        if (DT != nullptr && DT->isComponentType()) {
          Stub->addHostComponent(DT->getComponentType());
        }
        break;
      }
      case ExternDesc::DescType::ValueBound:
      case ExternDesc::DescType::CoreType:
      default:
        // Values and core types carry no runtime state a stub must provide.
        break;
      }
    }
  }
  return Stub;
}

Expect<void>
Executor::synthesizeImport(Runtime::Instance::ComponentInstance &CompInst,
                           const AST::Component::ExternDesc &Desc) {
  switch (Desc.getDescType()) {
  case ExternDesc::DescType::FuncType: {
    const auto *DT = CompInst.getType(Desc.getTypeIndex());
    if (DT == nullptr || !DT->isFuncType()) {
      spdlog::error(ErrCode::Value::UnknownImport);
      spdlog::error("    permissive import: bad function type index {}"sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::UnknownImport);
    }
    CompInst.addFunction(stubHostFunc(DT->getFuncType(), &CompInst));
    return {};
  }
  case ExternDesc::DescType::TypeBound:
    if (Desc.isEqType()) {
      CompInst.addTypeWithResource(
          CompInst.getType(Desc.getTypeIndex()),
          CompInst.getTypeResource(Desc.getTypeIndex()));
    } else {
      // Abstract resource: a fresh opaque host resource type.
      CompInst.addHostResourceType(nullptr);
    }
    return {};
  case ExternDesc::DescType::InstanceType: {
    const auto *DT = CompInst.getType(Desc.getTypeIndex());
    if (DT == nullptr || !DT->isInstanceType()) {
      spdlog::error(ErrCode::Value::UnknownImport);
      spdlog::error("    permissive import: bad instance type index {}"sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::UnknownImport);
    }
    std::vector<const InstanceDecl *> Decls;
    for (const auto &D : DT->getInstanceType().getDecl()) {
      Decls.push_back(&D);
    }
    EXPECTED_TRY(auto Stub, synthesizeInstanceStub(CompInst, Decls));
    CompInst.addComponentInstance(std::move(Stub));
    return {};
  }
  case ExternDesc::DescType::ComponentType: {
    const auto *DT = CompInst.getType(Desc.getTypeIndex());
    if (DT == nullptr || !DT->isComponentType()) {
      spdlog::error(ErrCode::Value::UnknownImport);
      spdlog::error("    permissive import: bad component type index {}"sv,
                    Desc.getTypeIndex());
      return Unexpect(ErrCode::Value::UnknownImport);
    }
    CompInst.addHostComponent(DT->getComponentType());
    return {};
  }
  case ExternDesc::DescType::ValueBound:
  case ExternDesc::DescType::CoreType:
  default:
    spdlog::error(ErrCode::Value::UnknownImport);
    spdlog::error("    permissive import: unsupported import kind"sv);
    return Unexpect(ErrCode::Value::UnknownImport);
  }
}

// Instantiates a host component from its declared shape: export declarations
// become stub exports; import declarations are satisfied implicitly.
Expect<std::unique_ptr<Runtime::Instance::ComponentInstance>>
Executor::instantiateHostComponent(Runtime::Instance::ComponentInstance &Owner,
                                   const AST::Component::ComponentType &Shape) {
  std::vector<const InstanceDecl *> Decls;
  for (const auto &D : Shape.getDecl()) {
    if (!D.isImportDecl()) {
      Decls.push_back(&D.getInstance());
    }
  }
  return synthesizeInstanceStub(Owner, Decls);
}

} // namespace Executor
} // namespace WasmEdge
