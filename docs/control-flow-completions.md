# Control-flow completion model

Ecmora represents statement exits as explicit ECMAScript completions:

- `Normal`
- `Break(target?)`
- `Continue(target?)`
- `Return(value)`
- `Throw(value)`

Labels are attached to the statement they prefix. Nested labels are collected
as one label set, so both labels in `outer: alias: while (...)` can target the
same iteration statement. Unlabeled `break` is consumed only by the nearest
iteration or switch. Unlabeled `continue` is consumed only by the nearest
iteration. A labeled `continue` must resolve to an iteration label.

## try/catch/finally

The compatibility runtime follows completion replacement rules:

1. execute the try block;
2. a `Throw` enters the catch clause when present;
3. execute the finally block for every completion;
4. a non-normal finally completion replaces the prior completion;
5. a normal finally completion preserves the prior completion.

Catch parameters use a dedicated lexical scope. Destructuring catch parameters
are lowered through a hidden catch binding plus ordinary lexical
destructuring declarations.

Throws produced by user functions, getters, setters, Proxy traps and primitive
coercion callbacks travel through a dedicated `JavaScriptThrow` channel and
are converted back into `Completion::Throw`. Internal compiler/runtime errors
remain host errors and cannot be accidentally caught by JavaScript.

## Native boundary

Labels are lowered by the native SSA backend through one unified
`ControlTarget` stack carrying label sets, break/continue destinations and
scope snapshots for phi construction.

`try/catch/finally` deliberately routes to the compatibility backend until the
LLVM backend has a cleanup-pad or explicit completion-dispatch ABI. This avoids
silently skipping finally blocks or treating JavaScript throws as process
exceptions.


## Suspension boundary

The synchronous completion rules above also apply inside async functions when
the compatibility runtime can settle the awaited promise. Native async helper
lifting still rejects an await that crosses a labeled statement or
try/catch/finally, and async-generator `yield` nested inside these containers
still requires the future generator CFG continuation stack. These paths fail
explicitly instead of skipping cleanup code.
