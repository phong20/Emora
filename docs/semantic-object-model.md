# Semantic object model

This layer separates JavaScript semantic operations from storage.

## Implemented in this phase

- Every ordinary object wrapper carries a `RealmId` and typed internal slots.
- Functions and Promises retain their allocation realm in the compatibility
  runtime.
- `Proxy` is observable for `[[Get]]`, `[[Set]]`, `[[HasProperty]]`,
  `[[Delete]]`, and `[[OwnPropertyKeys]]`.
- Promise thenable assimilation uses the same observable `Get("then")`
  operation, so a Proxy trap or accessor is not bypassed.
- Proxy invariants reject hidden non-configurable keys, duplicate `ownKeys`
  results, invalid non-writable writes, and operations on revoked proxies.
- Promise rejection reporting is exposed through `HostHooks`.
- Analysis owns an effect lattice for property access, user-code calls, throws,
  jobs, suspension, realm sensitivity, Proxy observability, class construction,
  and generator state.

## Internal-slot foundations

`ClassConstructorSlots` and `AsyncGeneratorSlots` are intentionally present
before syntax execution is enabled. The next lowering stages can attach class
constructors, prototype methods, async-generator request queues, and completion
records without changing `Value` or ordinary object layout again.

## Native boundary

LLVM lowering must not treat unknown property operations as pure when a Proxy
can be observed. Programs that reference the intrinsic `Proxy` are rejected by
native analysis and use the compatibility backend until Proxy-aware IR
instructions and deoptimization guards are implemented.
