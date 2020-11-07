//===- Cosim_DpiPkg.sv - ESI cosim DPI declarations -------------*- C++ -*-===//
//
// Package: CosimCore_DpiPkg
//
// DPI-exposed funcs for cosimserver cosimulation unit-test.
//
//===----------------------------------------------------------------------===//

package Cosim_DpiPkg;

// --------------------- Cosim RPC Server -------------------------------------

// Start cosimserver (spawns server for RTL-initiated work, listens for
// connections from new SW-clients).
import "DPI-C" sv2cCosimserverInit = function int cosim_init();

// Teardown cosimserver (disconnects from primary server port, stops connections
// from active clients).
import "DPI-C" sv2cCosimserverFini = function void cosim_fini();

// --------------------- Endpoint Management ----------------------------------

// Register simulated device endpoints.
// - return 0 on success, non-zero on failure (duplicate EP registered).
import "DPI-C" sv2cCosimserverEpRegister =
  function int cosim_ep_register(
      input int endpoint_id,
      input longint esi_type_id,
      input int type_size);

// --------------------- Endpoint Accessors -----------------------------------

// Attempt to send data to a client.
// - return 0 on success, negative on failure (unregistered EP).
import "DPI-C" sv2cCosimserverEpTryPut = 
  function int cosim_ep_tryput(
    // The ID of the endpoint to which the data should be sent.
    input int unsigned endpoint_id,
    // A data buffer.
    input byte unsigned data[],
    // (Optional) Size of the buffer. If negative, will be dynamically detected.
    input int data_size = -1
    );

// Attempt to recieve data from a client.
//   - Returns negative when call failed (e.g. EP not registered).
//   - If no message, return 0 with size_bytes == 0.
//   - Assumes buffer is large enough to contain entire message. Fails if not
//     large enough. (In the future, will add support for getting the message into a
//     fixed-size buffer over multiple calls.)
import "DPI-C" sv2cCosimserverEpTryGet = 
  function int cosim_ep_tryget(
    // The ID of the endpoint from which data should be recieved.
    input  int unsigned endpoint_id,
    // The buffer in which to put the data. This should be 'output', but the
    // open source simulator Verilator doesn't seem to have a way to do this.
    inout byte unsigned data[],
    // Input: indicates the size of the data[] buffer. If -1, dynamically detect
    // size.
    // Output: the size of the message.
    inout  int unsigned data_size
    );

endpackage // Cosim_DpiPkg
