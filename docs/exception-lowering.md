# ECMAScript exception lowering

## Semantic invariant

`throw value` produces a **ThrowCompletion**, never a normal return value.
The compiler must not use a thrown value to infer, verify, or materialize a
function's normal return type.

## Implemented synchronous path

```text
OXC ThrowStatement
  -> HIR StatementKind::Throw
  -> analysis Terminator::ThrowValue { typed SSA value }
  -> LLVM boxes only when required at the runtime boundary
  -> call @ecmora_throw_uncaught(tag, payload)
  -> LLVM unreachable
```

The thrown expression remains statically typed. Number, Boolean, String,
Object, Callable, Promise and Dynamic values therefore stay in typed SSA and
are boxed only once at the uncaught host boundary. Constant tags and payloads
remain visible to LLVM optimization.

The current HIR has no `Try` node, so every accepted synchronous throw is
uncaught. Aborting at the host boundary is therefore correct for the supported
subset and, critically, cannot be mistaken for a function return.

## Static analysis rules in this batch

- thrown types do not join normal return types;
- statements after a statically terminating throw/return are ignored by return
  inference;
- both arms of `if`, terminal `do/while`, literal-true loops, `for(;;)`, and
  exhaustive independently-terminal switches improve fallthrough analysis;
- top-level throw skips later queued work;
- direct throw inside native async functions or Promise callbacks is rejected
  until rejection completion exists;
- `Promise.reject` is rejected rather than silently lowered as fulfillment.

## Required next phase: explicit completion ABI

Potentially-throwing calls need two outcomes. Keep the current fast ABI for
functions proven `nothrow`; use an explicit completion ABI only for functions
whose effect summary says `may_throw`:

```text
void js_fn(closure, argc, argv, normal_out, throw_out, completion_kind_out)
```

A more compact equivalent is a small completion struct. The exact C ABI is less
important than preserving two distinct CFG successors:

```text
InvokeDirect / InvokeIndirect
    normal -> normal_block(value)
    throw  -> exceptional_block(exception)
```

The analysis pass should compute a fixed-point effect summary per reachable
specialization:

```text
normal_return_types
thrown_types
may_throw
may_suspend
```

Direct calls propagate summaries statically. Unknown indirect calls use a
generic throwing ABI. This allows LLVM to keep the common `nothrow` path as a
plain direct call while emitting exceptional edges only where necessary.

## Try/catch/finally lowering

After the completion ABI exists, add HIR nodes for `Try`, `CatchClause`, and
`Finally`, then lower them as CFG:

- `try` body uses an exception target;
- `catch` binds the thrown ECMAScript value and resumes normal control flow;
- `finally` receives a pending completion (`normal`, `return`, `throw`,
  `break`, or `continue`) and either forwards it or replaces it when the
  finally body itself completes abruptly;
- nested handlers form a lexical exception-target stack;
- a throw from a getter, setter, conversion, or indirect call uses the same
  exceptional edge.

No host-language C++ exception or LLVM landingpad is required for JavaScript
exceptions. Explicit completion values/edges are more portable and make the
ECMAScript semantics visible to optimization.

## Async and Promise integration

An async function converts a synchronous ThrowCompletion into a rejected
Promise. Promise state therefore needs at least `pending`, `fulfilled`, and
`rejected`, and jobs need separate fulfillment/rejection handlers. Only after
that exists may native lowering accept throws in async bodies, `.then`
callbacks, `.catch`, `.finally`, or `Promise.reject`.
