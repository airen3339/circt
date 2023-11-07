//===- Design.h - Dynamic accelerator API -----------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//
//
// DO NOT EDIT!
// This file is distributed as part of an ESI package. The source for this file
// should always be modified within CIRCT.
//
//===----------------------------------------------------------------------===//

// NOLINTNEXTLINE(llvm-header-guard)
#ifndef ESI_DESIGN_H
#define ESI_DESIGN_H

#include "esi/Accelerator.h"
#include "esi/Manifest.h"

#include <any>
#include <cstdint>
#include <string>

namespace esi {
// Forward declarations.
class Instance;

class Design {
public:
  Design(std::optional<ModuleInfo> info,
         std::vector<std::unique_ptr<Instance>> children)
      : _info(info), _children(std::move(children)) {}

  std::optional<ModuleInfo> info() const { return _info; }
  const std::vector<std::unique_ptr<Instance>> &children() const {
    return _children;
  }

protected:
  const std::optional<ModuleInfo> _info;
  const std::vector<std::unique_ptr<Instance>> _children;
};

class Instance : public Design {
public:
  Instance() = delete;
  Instance(const Instance &) = delete;
  ~Instance() = default;
  Instance(AppID id, std::optional<ModuleInfo> info,
           std::vector<std::unique_ptr<Instance>> children)
      : Design(info, std::move(children)), _id(id) {}

  const AppID id() const { return _id; }

protected:
  const AppID _id;
};

} // namespace esi

#endif // ESI_DESIGN_H
