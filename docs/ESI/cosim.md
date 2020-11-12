# ESI cosimulation model

Elastic Silicon Interfaces provides a feature called cosimulation. Cosim in
general allows communication between the simulation and software. In the ESI
case, it is typed and can be used to build an application and language
specific API which is nearly identical to how the real hardware would
interface. This allows users to simulate against the actual target software
(or some simplification of it), enabling easier co-design.

ESI cosim uses [Cap'nProto](https://capnproto.org/) as a message format and
RPC client/server. Capnp was chosen due to its relatively low-overhead
encoding/decoding (as compared to Protocol Buffers and ilk) is a good fit for
hardware. Using a standard messaging protocol allows users to work with a
variety of languages: the Cap'nProto website lists C++, C#, Erlang, Go,
Haskell, JavaScript, Ocaml, Python, and Rust as languages which support
messages and RPC!

## Usage

To interface with RTL simulators, the [DPI
interface](https://en.wikipedia.org/wiki/SystemVerilog_DPI) is used. ESI
cosim builds and provides a set of SystemVerilog sources and a shared library
which implement both DPI sides. The shared library (C++) starts a capnp RPC
server for client(s) to connect to and interface with the simulations.

### Endpoints

ESI cosim works through a notion of *endpoints* -- typed, bi-directional
cosim bridges which are exposed over RPC. Endpoints are registered with the
RPC interface.

On the RTL side, we provide a SystemVerilog module (`Cosim_Endpoint`) which
provides a simple interface to the client. The modules instances take care of
registering themselves. `DataOut` and `DataIn` carry the raw capnp messages
with corresponding control signals. At present, we only support fixed-size
messages.

```systemverilog
module Cosim_Endpoint
#(
   parameter int ENDPOINT_ID = -1,
   parameter longint ESI_TYPE_ID = -1,
   parameter int TYPE_SIZE_BITS = -1
)
(
   input  logic clk,
   input  logic rstn,

   output logic DataOutValid,
   input  logic DataOutReady,
   output logic[TYPE_SIZE_BITS-1:0] DataOut,

   input  logic DataInValid,
   output logic DataInReady,
   input  logic [TYPE_SIZE_BITS-1:0] DataIn
);
```

The RPC interface allows clients to query all the registered endpoints, grab
a reference to one, and send/recieve messages and/or raw data. Once one
client opens an Endpoint, it is locked until said client closes it.

```capnp
interface CosimDpiServer {
    list @0 () -> (ifaces :List(EsiDpiInterfaceDesc));
    open @1 [S, T] (iface :EsiDpiInterfaceDesc) -> (iface :EsiDpiEndpoint(S, T));
}

struct EsiDpiInterfaceDesc {
    typeID @0 :UInt64;
    endpointID @1 :Int32;
}

interface EsiDpiEndpoint(SendMsgType, RecvMsgType) {
    send @0 (msg :SendMsgType);
    recv @1 (block :Bool = true) -> (hasData :Bool, resp :RecvMsgType); # If 'resp' null, no data

    close @2 ();
}

struct UntypedData {
    data @0 :Data;
}
```

This RPC interface can be used from any supported language. Here's an example for Python:

```py
import capnp

class LoopbackTester:
    def __init__(self, schemaPath):
        self.dpi = capnp.load(schemaPath)
        hostname = os.uname()[1]
        self.rpc_client = capnp.TwoPartyClient(f"{hostname}:1111")
        self.cosim = self.rpc_client.bootstrap().cast_as(self.dpi.CosimDpiServer)

    def openEP(self):
        ifaces = self.cosim.list().wait().ifaces
        openResp = self.cosim.open(ifaces[0]).wait()
        assert openResp.iface is not None
        return openResp.iface

    def write(self, ep):
        r = random.randrange(0, 2**24)
        data = r.to_bytes(3, 'big')
        print(f'Sending: {binascii.hexlify(data)}')
        ep.send(self.dpi.UntypedData.new_message(data=data)).wait()
        return data

    def read(self, ep):
        while True:
            recvResp = ep.recv(False).wait()
            if recvResp.hasData:
                break
            else:
                time.sleep(0.1)
        assert recvResp.resp is not None
        dataMsg = recvResp.resp.as_struct(self.dpi.UntypedData)
        data = dataMsg.data
        print(binascii.hexlify(data))
        return data

    def write_read(self):
        ep = self.openEP()
        print("Testing writes")
        dataSent = self.write(ep)
        print()
        print("Testing reads")
        dataRecv = self.read(ep)
        ep.close().wait()
        assert dataSent == dataRecv
```

## Implementation of the RPC server DPI plugin

In short, an instance of `Cosim_Endpoint` registers itself. The first
registration starts the RPC server (or it can be started via a direct dpi
call). Starting the RPC server involves spining up a thread in which the RPC
server runs. Communication between the simulator thread(s) and the RPC server
thread is through per-endpoint, thread-safe queues. The DPI functions poll
for incoming data or push outgoing data to/from said queues. There is no flow
control yet so it is currently very easy to bloat the infinitely-sized
queues. For the time being, flow-contol has be handled at a higher level.

## Compiling ESI cosim

ESI cosim requires a recent version of Cap'nProto to be installed. A script
is provided (`utils/get-capnp.sh`) which installs a known-working version to
`ext/`. If the build system detects Cap'nProto is installed (either
system-wide or in `ext/`), the ESI cosim DPI code will be enabled as the
`EsiCosimDpiServer` target.

## Running the ESI cosim integration tests

To run the tests, you'll need recent versions of Verilator, Cap'nProto, and
pycapnp installed. For the former two, the are scripts provided in the
`utils/` directory which will download, compile, and place a known-working
version in `ext/` (which the tests know about). For pycapnp, you should use
PIP: `pip3 install pycapnp`.

Once you've got the three above requirements installed, just run the CIRCT
integration tests. They are configured to detect the three above requirements
and run the tests if they're all present.

```sh
cd build # Or wherever you're building CIRCT.
ninja check-circt-integration # Will run all the CIRCT integration tests.
```
