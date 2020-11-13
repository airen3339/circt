//===- Endpoint.h - Cosim endpoint server ----------------------*- C++ -*-===//
//
// Declare the class which is used to model DPI endpoints.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_DIALECT_ESI_COSIM_ENDPOINT_H
#define CIRCT_DIALECT_ESI_COSIM_ENDPOINT_H

#include "circt/Dialect/ESI/cosim/CosimDpi.capnp.h"
#include <functional>
#include <map>
#include <memory>
#include <mutex>
#include <queue>

namespace circt {
namespace esi {
namespace cosim {

/// Implements a bi-directional, thread-safe bridge between the RPC server and
/// DPI functions.
///
/// Several of the methods below are inline with the declaration to make them
/// candidates for inlining during compilation. This is particularly important
/// on the simulation side since polling happens at each clock and we do not
/// want to slow down the simulation any more than necessary.
class Endpoint {
public:
  /// Representing messages as shared pointers to vectors may be a performance
  /// issue in the future but it is the easiest way to ensure memory
  /// correctness.
  using Blob = std::vector<uint8_t>;
  using BlobPtr = std::shared_ptr<Blob>;

  /// Construct an endpoint which knows and the type IDs in both directions.
  Endpoint(uint64_t sendTypeId, int sendTypeMaxSize, uint64_t recvTypeId,
           int recvTypeMaxSize);
  ~Endpoint();
  /// Disallow copying. There is only ONE endpoint object per logical endpoint
  /// so copying is almost always a bug.
  Endpoint(const Endpoint &) = delete;

  uint64_t getSendTypeId() const;
  uint64_t getRecvTypeId() const;

  /// These two are used to set and unset the inUse flag, to ensure that an open
  /// endpoint is not opened again.
  bool setInUse();
  void returnForUse();

  /// Queue message to the simulation.
  void pushMessageToSim(BlobPtr msg) {
    Lock g(m);
    toCosim.push(msg);
  }

  /// Pop from the to-simulator queue. Return true if there was a message in the
  /// queue.
  bool getMessageToSim(BlobPtr &msg) {
    Lock g(m);
    if (toCosim.size() > 0) {
      msg = toCosim.front();
      toCosim.pop();
      return true;
    }
    return false;
  }

  /// Queue message to the RPC client.
  void pushMessageToClient(BlobPtr msg) {
    Lock g(m);
    toClient.push(msg);
  }

  /// Pop from the to-RPC-client queue. Return true if there was a message in
  /// the queue.
  bool getMessageToClient(BlobPtr &msg) {
    Lock g(m);
    if (toClient.size() > 0) {
      msg = toClient.front();
      toClient.pop();
      return true;
    }
    return false;
  }

private:
  const uint64_t sendTypeId;
  const uint64_t recvTypeId;
  bool inUse;

  using Lock = std::lock_guard<std::mutex>;

  /// This class needs to be thread-safe. All of the mutable member variables
  /// are protected with this object-wide lock. This may be a performance issue
  /// in the future.
  std::mutex m;
  /// Message queue from RPC client to the simulation.
  std::queue<BlobPtr> toCosim;
  /// Message queue to RPC client from the simulation.
  std::queue<BlobPtr> toClient;
};

/// The Endpoint registry is where Endpoints report their existence (register)
/// and they are looked up by RPC clients.
class EndpointRegistry {
public:
  /// Register an Endpoint. Creates the Endpoint object and owns it.
  void registerEndpoint(int epId, uint64_t sendTypeId, int sendTypeMaxSize,
                        uint64_t recvTypeId, int recvTypeMaxSize);

  /// Get the specified endpoint, if it exists. Return false if it does not.
  bool get(int epId, Endpoint *&);
  /// Get the specified endpoint, throwing an exception if it doesn't exist.
  /// This method is defined inline so it can be inlined at compile time.
  /// Performance is important here since this method is used in the polling
  /// call from the simulator.
  Endpoint &operator[](int epId) {
    Lock g(m);
    auto it = endpoints.find(epId);
    if (it == endpoints.end())
      throw std::runtime_error("Could not locate Endpoint");
    return it->second;
  }

  /// Iterate over the list of endpoints, calling the provided function for each
  /// endpoint.
  void iterateEndpoints(std::function<void(int id, const Endpoint &)> f) const;
  /// Return the number of endpoints.
  size_t size() const;

private:
  using Lock = std::lock_guard<std::mutex>;

  /// This object needs to be thread-safe. An object-wide mutex is sufficient.
  std::mutex m;

  /// Endpoint ID to object pointer mapping.
  std::map<int, Endpoint> endpoints;
};

} // namespace cosim
} // namespace esi
} // namespace circt

#endif
