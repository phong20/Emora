# Ecmora analysis architecture

`ecmora-analysis` lowers JavaScript HIR into verified Ecmora IR. It is not the
parser, optimizer, LLVM backend, or runtime. Its responsibility is to prove
what can be represented natively and to emit explicit IR for those decisions.

## Source layout

After running `tools/materialize_analysis.py`, the crate has normal checked-in
Rust source. No analysis source is generated through `OUT_DIR`.

### `src/lib.rs`

Owns stateful lowering and control-flow construction:

- lexical scopes, TDZ state, bindings, cells, and captures;
- CFG blocks, phi nodes, loops, branches, switch, return, and throw lowering;
- expression and statement dispatch;
- object, accessor, callable, and Promise lowering;
- child-function construction and emission of Ecmora IR;
- orchestration of specialization lookup/creation.

This file may use the support and specialization modules, but those modules
must not mutate lowering state directly.

### `src/support.rs`

Owns stateless analysis helpers:

- free-variable collection;
- return-type hint collection;
- expression type hints;
- reachability/use collection for dead binding elimination;
- purity classification;
- mapping HIR operators and compile-time values to IR types/operators.

Functions in this module should be deterministic for the same HIR and input
environment. New whole-function analyses should normally start here rather
than adding more mutable fields to `Lowerer`.

### `src/specialization.rs`

Owns specialization identity and policy:

- `SpecializationKey`, including parameter types, capture layout, callbacks,
  and contextual return seed;
- callback fingerprints;
- the per-source-function specialization budget.

Any new specialization dimension must be represented as a typed field in
`SpecializationKey`. Do not return to formatted-string cache keys.

## Core lowering pipeline

```text
HIR program
   |
   v
predeclare lexical/function bindings
   |
   v
lower statements and expressions
   |-- constant/static value propagation
   |-- contextual type expectations
   |-- CFG and phi construction
   |-- closure/capture materialization
   `-- function specialization
           |-- completed cache hit
           |-- active recursive cycle hit
           `-- predeclare ABI, lower child body, verify returns
   |
   v
Ecmora IR program
   |
   v
verify_program
```

## Specialization invariants

1. **Predeclare before recursive lowering.** A specialization is inserted into
   `active_specializations` as soon as its function name and provisional return
   type are known. Recursive and mutually recursive calls may then reference
   it before its body is complete.

2. **The key describes the ABI and specialized semantics.** Parameter types,
   capture layout, devirtualized callback identity, and contextual return seed
   are all part of the key.

3. **A provisional return type is checked.** When the child body is complete,
   every concrete return must agree with the predeclared type unless the
   specialization explicitly uses `Dynamic`.

4. **Captures are ordered ABI slots.** Capture ordering must be deterministic.
   Callback captures are remapped to the child function's capture values, not
   reused as parent SSA values.

5. **Specialization is bounded.** The per-function limit prevents non-converging
   polymorphic recursion or callback combinations from exhausting compile-time
   memory and generating unbounded native code.

## Tail calls and stack safety

Analysis only recognizes a tail position and emits
`Terminator::TailCallDirect`. IR verification checks target arity and return
compatibility. LLVM codegen implements argument-buffer reuse and the runtime
implements the non-tail recursion depth guard.

Do not put LLVM-specific tail-call mechanics or the recursion counter inside
this crate.

## Adding a new JavaScript feature

Use this order:

1. Add/confirm the HIR representation in `ecmora-hir`.
2. Decide whether the feature is statically representable, requires tagged
   runtime operations, or needs a guarded specialization plus fallback.
3. Add stateless inference/collection logic to `support.rs` when possible.
4. Add lowering state only when information must survive across CFG regions or
   nested function construction.
5. Add explicit IR instructions/terminators rather than hiding semantics in
   analysis-only side tables.
6. Extend `verify_program` before or together with codegen.
7. Add a JavaScript integration test and, for isolated policy, a Rust unit test.

## Planned next splits

`lib.rs` remains large after the first migration. Future behavior-preserving
splits should proceed one responsibility at a time:

- `lower/control_flow.rs`: loops, branches, switch, phi merging;
- `lower/expressions.rs`: expression dispatch and primitive operations;
- `lower/calls.rs`: builtin, Promise, closure, and function calls;
- `lower/objects.rs`: object/property/accessor lowering;
- `environment.rs`: binding, scope, TDZ, and capture operations.

Each split should be a mechanical move with tests green before semantic changes
are introduced. This avoids combining architecture churn with compiler feature
work in the same debugging step.
