//===- DpiEntryPoints.cpp - ESI cosim DPI calls -----------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Cosim DPI function implementations. Mostly C-C++ gaskets to the C++
// RpcServer.
//
// These function signatures were generated by an HW simulator (see dpi.h) so
// we don't change them to be more rational here. The resulting code gets
// dynamically linked in and I'm concerned about maintaining binary
// compatibility with all the simulators.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/ESI/LLCosim/Server.h"
#include "circt/Dialect/ESI/LLCosim/dpi.h"

#include <algorithm>
#include <cstdio>

using namespace circt::esi::llcosim;

/// If non-null, log to this file. Protected by 'serverMutex`.
static FILE *logFile;
static RpcServer *server = nullptr;
static std::mutex serverMutex;

// ---- Helper functions ----

/// Get the TCP port on which to listen. If the port isn't specified via an
/// environment variable, return 0 to allow automatic selection.
static int findPort() {
  const char *portEnv = getenv("COSIM_PORT");
  if (portEnv == nullptr) {
    printf(
        "[LLCOSIM] RPC server port not found. Letting CapnpRPC select one\n");
    return 0;
  }
  printf("[LLCOSIM] Opening RPC server on port %s\n", portEnv);
  return std::strtoull(portEnv, nullptr, 10);
}

// ---- DPI entry points ----

// Teardown cosimserver (disconnects from primary server port, stops connections
// from active clients).
DPI void sv2cLLCosimserverFinish() {
  std::lock_guard<std::mutex> g(serverMutex);
  printf("[LLCOSIM] Tearing down RPC server.\n");
  if (server != nullptr) {
    server->stop();
    server = nullptr;

    fclose(logFile);
    logFile = nullptr;
  }
}

// Start cosimserver (spawns server for HW-initiated work, listens for
// connections from new SW-clients).
DPI int sv2cLLCosimserverInit() {
  std::lock_guard<std::mutex> g(serverMutex);
  if (server == nullptr) {
    // Open log file if requested.
    const char *logFN = getenv("COSIM_DEBUG_FILE");
    if (logFN != nullptr) {
      printf("[LLCOSIM] Opening debug log: %s\n", logFN);
      logFile = fopen(logFN, "w");
    }

    // Find the port and run.
    printf("[LLCOSIM] Starting RPC server.\n");
    server = new RpcServer();
    server->run(findPort());
  }
  return 0;
}
