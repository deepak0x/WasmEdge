// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: Copyright The WasmEdge Authors

#include "executor/executor.h"

#include "common/errinfo.h"
#include "common/spdlog.h"

#include <string_view>

namespace WasmEdge {
namespace Executor {

using namespace std::literals;

Expect<void>
Executor::instantiate(Runtime::StoreManager &StoreMgr,
                      Runtime::Instance::ComponentInstance &CompInst,
                      const AST::Component::ImportSection &ImportSec) {
  for (const auto &Import : ImportSec.getContent()) {
    const auto &Desc = Import.getDesc();
    switch (Desc.getDescType()) {
    case AST::Component::ExternDesc::DescType::TypeBound:
      // Type imports fill the type index space; hosts supply no types, so
      // eq-bound targets are used and abstract resources stay opaque.
      if (Desc.isEqType()) {
        CompInst.addTypeWithResource(
            CompInst.getType(Desc.getTypeIndex()),
            CompInst.getTypeResource(Desc.getTypeIndex()));
        break;
      }
      if (Conf.getRuntimeConfigure().isComponentPermissiveImports()) {
        // A fresh opaque host resource type stands in for the abstract
        // import so handle operations stay usable.
        CompInst.addHostResourceType(nullptr);
        break;
      }
      CompInst.addDummyType();
      break;
    case AST::Component::ExternDesc::DescType::CoreType:
    case AST::Component::ExternDesc::DescType::FuncType:
    case AST::Component::ExternDesc::DescType::ValueBound:
    case AST::Component::ExternDesc::DescType::ComponentType:
      if (Conf.getRuntimeConfigure().isComponentPermissiveImports()) {
        EXPECTED_TRY(synthesizeImport(CompInst, Desc));
        break;
      }
      // No host-side providers for these sorts.
      spdlog::error(ErrCode::Value::UnknownImport);
      spdlog::error("    import name: {}"sv, Import.getName());
      return Unexpect(ErrCode::Value::UnknownImport);
    case AST::Component::ExternDesc::DescType::InstanceType: {
      // TODO: COMPONENT - type matching for the instance type.
      auto CompName = Import.getName();
      const auto *ImportedCompInst = StoreMgr.findComponent(CompName);
      if (unlikely(ImportedCompInst == nullptr)) {
        if (Conf.getRuntimeConfigure().isComponentPermissiveImports()) {
          EXPECTED_TRY(synthesizeImport(CompInst, Desc));
          break;
        }
        spdlog::error(ErrCode::Value::UnknownImport);
        spdlog::error("    component name: {}"sv, CompName);
        return Unexpect(ErrCode::Value::UnknownImport);
      }
      CompInst.addComponentInstance(ImportedCompInst);
      break;
    }
    default:
      assumingUnreachable();
    }
  }
  return {};
}

Expect<void>
Executor::instantiate(Runtime::Instance::ComponentImportManager &ImportMgr,
                      Runtime::Instance::ComponentInstance &CompInst,
                      const AST::Component::ImportSection &ImportSec) {
  for (const auto &Import : ImportSec.getContent()) {
    const auto &Desc = Import.getDesc();
    switch (Desc.getDescType()) {
    case AST::Component::ExternDesc::DescType::FuncType: {
      auto *Func = ImportMgr.findFunction(Import.getName());
      if (unlikely(Func == nullptr)) {
        if (Conf.getRuntimeConfigure().isComponentPermissiveImports()) {
          EXPECTED_TRY(synthesizeImport(CompInst, Desc));
          break;
        }
        spdlog::error(ErrCode::Value::UnknownImport);
        spdlog::error("    function name: {}"sv, Import.getName());
        return Unexpect(ErrCode::Value::UnknownImport);
      }
      CompInst.addFunction(Func);
      break;
    }
    case AST::Component::ExternDesc::DescType::TypeBound: {
      // Type imports fill the type index space: an argument-supplied type
      // when present, otherwise the eq-bound target.
      const auto *Ty = ImportMgr.findType(Import.getName());
      const auto *RT = static_cast<
          const Runtime::Instance::ComponentInstance::ResourceTypeRT *>(
          ImportMgr.findTypeResource(Import.getName()));
      if (Ty == nullptr && RT == nullptr && Desc.isEqType()) {
        CompInst.addTypeWithResource(
            CompInst.getType(Desc.getTypeIndex()),
            CompInst.getTypeResource(Desc.getTypeIndex()));
      } else {
        CompInst.addTypeWithResource(Ty, RT);
      }
      break;
    }
    case AST::Component::ExternDesc::DescType::ComponentType: {
      if (ImportMgr.hasComponent(Import.getName())) {
        CompInst.addComponentEntry(
            ImportMgr.findComponent(Import.getName()),
            ImportMgr.findComponentShape(Import.getName()),
            ImportMgr.findComponentEnv(Import.getName()));
        break;
      }
      if (Conf.getRuntimeConfigure().isComponentPermissiveImports()) {
        EXPECTED_TRY(synthesizeImport(CompInst, Desc));
        break;
      }
      spdlog::error(ErrCode::Value::UnknownImport);
      spdlog::error("    component name: {}"sv, Import.getName());
      return Unexpect(ErrCode::Value::UnknownImport);
    }
    case AST::Component::ExternDesc::DescType::CoreType: {
      const auto *M = ImportMgr.findCoreModule(Import.getName());
      if (unlikely(M == nullptr)) {
        spdlog::error(ErrCode::Value::UnknownImport);
        spdlog::error("    core module name: {}"sv, Import.getName());
        return Unexpect(ErrCode::Value::UnknownImport);
      }
      CompInst.addModule(*M);
      break;
    }
    case AST::Component::ExternDesc::DescType::ValueBound:
      // TODO: COMPONENT - value imports.
      spdlog::error(ErrCode::Value::ComponentNotImplInstantiate);
      spdlog::error("    incomplete import {} desc types"sv, Import.getName());
      return Unexpect(ErrCode::Value::ComponentNotImplInstantiate);
    case AST::Component::ExternDesc::DescType::InstanceType: {
      // TODO: COMPONENT - type matching for the instance type.
      auto CompName = Import.getName();
      const auto *ImportedCompInst = ImportMgr.findComponentInstance(CompName);
      if (unlikely(ImportedCompInst == nullptr)) {
        if (Conf.getRuntimeConfigure().isComponentPermissiveImports()) {
          EXPECTED_TRY(synthesizeImport(CompInst, Desc));
          break;
        }
        spdlog::error(ErrCode::Value::UnknownImport);
        spdlog::error("    component name: {}"sv, CompName);
        return Unexpect(ErrCode::Value::UnknownImport);
      }
      CompInst.addComponentInstance(ImportedCompInst);
      break;
    }
    default:
      assumingUnreachable();
    }
  }
  return {};
}

} // namespace Executor
} // namespace WasmEdge
