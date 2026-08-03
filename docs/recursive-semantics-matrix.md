# Recursive semantics test matrix

This document is the acceptance contract for recursive-function work in Ecmora.
It deliberately separates four different claims:

1. the JavaScript source parses;
2. native analysis can build valid Ecmora IR;
3. optimization changes the recursive call shape;
4. the produced executable has the required runtime behaviour.

A test passing at an earlier layer must never be used as proof for a later
layer. In particular, successfully lowering a tail-recursive function does not
prove tail-call optimization, and successfully compiling an infinitely
recursive function does not prove stack-overflow protection.

## Status meanings

- **GREEN**: executable test enabled now and expected to pass.
- **BASELINE ERROR**: executable test locks the current diagnostic until the
  phase that replaces it is implemented.
- **IGNORED CONTRACT**: desired compile/IR behaviour is already represented by
  an ignored test. The owning phase must enable it and remove the matching
  baseline-error assertion.
- **PARSE FIXTURE**: the complete source case is reserved and frontend-tested,
  but its owning compiler/runtime layer does not exist yet.
- **HARNESS REQUIRED**: the source fixture is reserved, but a native executable
  runner is required before the runtime claim can be tested honestly.

## Matrix

| ID | Behaviour | Current contract | Required phase | Acceptance condition |
|---|---|---|---|---|
| R01 | Direct recursion with a concrete Number base case | GREEN | complete baseline | One Number specialization contains a direct self-call. |
| R02 | Mutual recursion with concrete Bool base cases | GREEN | complete baseline | `isEven` and `isOdd` form a two-function direct-call cycle and both return Bool. |
| R03 | Repeated calls with the same argument types | GREEN | complete baseline | Both call sites reuse one specialization. |
| R04 | Ordinary non-recursive call-site polymorphism | GREEN | complete baseline | Number and String call sites create two specializations. |
| R05 | Recursive function has no internal return seed, but its result is consumed by Number arithmetic | BASELINE ERROR + IGNORED CONTRACT | phase 7 | Expected Number flows from the arithmetic use into the recursive SCC and analysis succeeds. |
| R06 | A recursive edge changes the argument type and creates another specialization | BASELINE ERROR + IGNORED CONTRACT | phases 8-9 | The specialization graph reaches a fixed point without infinite compiler recursion. |
| R07 | A recursive specialization carries a devirtualized callback | BASELINE ERROR + IGNORED CONTRACT | phases 10-11 | Callable identity/signature participates in the specialization key and recursive graph. |
| R08 | Self tail recursion | GREEN baseline + IGNORED CONTRACT | phases 13-15, 18 | Before TCO a normal self-call exists; after TCO no normal recursive call remains. |
| R09 | Mutual tail recursion | PARSE FIXTURE + IGNORED CONTRACT | phase 16 | The normal direct-call cycle is replaced by a bounded-stack trampoline or equivalent dispatch loop. |
| R10 | Tail call through a statically proven callback | PARSE FIXTURE + IGNORED CONTRACT | phase 17 | The source reaches tail lowering and does not allocate one native frame per logical call. |
| R11 | Deep non-tail recursion | PARSE FIXTURE + HARNESS REQUIRED | phases 19-20 | Execution terminates with a JavaScript `RangeError`; the process must not crash or abort. |
| R12 | Infinite recursion whose return participates in arithmetic | PARSE FIXTURE + HARNESS REQUIRED | phases 7, 19-20 | It compiles using the expected Number type and later throws `RangeError` through the completion ABI. |
| R13 | Recursive callback identities exceed the specialization budget | PARSE FIXTURE | phase 9 | Compilation terminates at the configured budget and widens or selects generic fallback deterministically. |
| R14 | Typed recursion crosses to tagged generic fallback | PARSE FIXTURE | phase 22 | Arguments, return value and thrown completion survive both boundary directions. |

## Implemented test file

`crates/ecmora-analysis/tests/recursive_semantics.rs` contains:

- enabled positive IR tests for R01-R04;
- an enabled pre-TCO baseline for R08;
- enabled stable current-diagnostic tests for R05-R07;
- ignored future acceptance tests for R05-R10;
- frontend parse checks for all source contracts R05-R14, including deep
  non-tail recursion, infinite recursion, specialization-budget pressure and
  the typed/generic fallback boundary.

The stack rows are intentionally not represented by a fake analysis-only
assertion. Phases 19-20 must add a native executable test harness and verify the
actual process result and JavaScript error completion.

## Rules for later phases

When a phase gains support for a row:

1. enable the matching ignored contract;
2. remove or invert the matching baseline-error test in the same commit;
3. do not weaken assertions to merely check that compilation returned `Ok` if
   the row requires an IR-shape or runtime property;
4. add native end-to-end coverage for rows marked **HARNESS REQUIRED**;
5. run the focused suite first, then the workspace suite.

Focused command:

```text
cargo test -p ecmora-analysis --test recursive_semantics
```

Workspace command:

```text
cargo test --workspace
```
