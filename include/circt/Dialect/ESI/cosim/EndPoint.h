//===- EndPoint.h - Cosim endpoint server ----------------------*- C++ -*-===//
//
// Declare the class which is used to model DPI endpoints.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/ESI/cosim/CosimDpi.capnp.h"
#include <functional>
#include <map>
#include <memory>
#include <mutex>
#include <queue>

#ifndef __ESI_ENDPOINT_HPP__
#define __ESI_ENDPOINT_HPP__

namespace circt {
namespace esi {
namespace cosim {

/// Implements a bi-directional, thread-safe bridge between the RPC server and
/// DPI functions. These methods are mostly inline to make them candidates for
/// inlining for performance reasons.
class EndPoint {
public:
  /// Representing messages as shared pointers to vectors may be a performance
  /// issue in the future but it is the easiest way to ensure memory
  /// correctness.
  using Blob = std::vector<uint8_t>;
  using BlobPtr = std::shared_ptr<Blob>;

private:
  const uint64_t _EsiTypeId;
  bool _InUse;

  using Lock = std::lock_guard<std::mutex>;

  /// This class needs to be thread-safe. All of the mutable member variables
  /// are protected with this object-wide lock. This may be a performance issue
  /// in the future.
  std::mutex _M;
  /// Message queue from RPC client to the simulation.
  std::queue<BlobPtr> toCosim;
  /// Message queue to RPC client from the simulation.
  std::queue<BlobPtr> toClient;

public:
  EndPoint(uint64_t EsiTypeId, int MaxSize);
  virtual ~EndPoint();
  /// Disallow copying. There is only ONE endpoint so copying is almost always a
  /// bug.
  EndPoint(const EndPoint &) = delete;

  uint64_t GetEsiTypeId() const { return _EsiTypeId; }

  bool SetInUse();
  void ReturnForUse();

  /// Queue message to the simulation.
  void PushMessageToSim(BlobPtr msg) {
    Lock g(_M);
    toCosim.push(msg);
  }

  /// Pop from the to-simulator queue. Return true if there was a message in the
  /// queue.
  bool GetMessageToSim(BlobPtr &msg) {
    Lock g(_M);
    if (toCosim.size() > 0) {
      msg = toCosim.front();
      toCosim.pop();
      return true;
    }
    return false;
  }

  /// Queue message to the RPC client.
  void PushMessageToClient(BlobPtr msg) {
    Lock g(_M);
    toClient.push(msg);
  }

  /// Pop from the to-RPC-client queue. Return true if there was a message in
  /// the queue.
  bool GetMessageToClient(BlobPtr &msg) {
    Lock g(_M);
    if (toClient.size() > 0) {
      msg = toClient.front();
      toClient.pop();
      return true;
    }
    return false;
  }
};

/// The Endpoint registry.
class EndPointRegistry {
  using Lock = std::lock_guard<std::mutex>;

public:
  ~EndPointRegistry();

  /// Takes ownership of ep
  void RegisterEndPoint(int ep_id, long long esi_type_id, int type_size);

  /// Get the specified endpoint, if it exists. Return false if it does not.
  bool Get(int ep_id, EndPoint *&);
  /// Get the specified endpoint, throwing an exception if it doesn't exist.
  EndPoint &operator[](int ep_id);
  /// Iterate over the list of endpoints, calling the provided function for each
  /// endpoint.
  void IterateEndpoints(std::function<void(int id, const EndPoint &)> F) const;
  /// Return the number of endpoints.
  size_t Size() const;

private:
  /// This object needs to be thread-safe. An object-wide mutex is sufficient.
  std::mutex _M;

  /// Endpoint ID to object pointer mapping.
  std::map<int, EndPoint> EndPoints;
};

} // namespace cosim
} // namespace esi
} // namespace circt

#endif
