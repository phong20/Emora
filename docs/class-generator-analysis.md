# Classes, async generators, var and analysis

## `var`

The frontend normalizes `var` before runtime and native analysis:

- declarations are collected across nested blocks in the current function;
- the binding is created at function entry with `undefined`;
- initializers remain assignments at their original evaluation point;
- `for`, `for-in`, and `for-of` declarations are rewritten without changing
  loop evaluation order;
- parameter and function-name redeclarations reuse the existing binding.

This lets both backends keep one lexical-binding representation while observing
the user-visible parts of `var` hoisting.

## Promise subclass class objects

Promise subclass metadata now retains an explicit constructor and instance or
static methods/accessors. The compatibility runtime creates constructor and
prototype objects, preserves method receivers, supports `super()`,
`super.method()`, derived-constructor `this` checks, fields stored on a Promise
ordinary-object sidecar, and constructor return completion.

The current class frontend remains deliberately scoped to classes extending
`Promise` or another retained Promise subclass. General arbitrary base classes,
private fields, static blocks, decorators and field initializers need the next
class-element lowering phase.

## Async generators

Calling an `async function*` creates an object with an async-generator state and
request queue. `next`, `return`, and `throw` each create a Promise capability and
resume the generator. Direct top-level yield boundaries preserve the sent value
for expression, declaration, assignment and return forms.

`yield*` and yield nested inside arbitrary control flow are rejected with a
precise compatibility diagnostic until generator CFG continuations are added.
This avoids claiming correctness by replaying a function body.

## Analysis

The native analysis now combines:

- the existing typed SSA flow;
- an abstract-value type-set and constant lattice;
- effect-aware dead-initializer decisions;
- explicit generator, suspension, property, realm and callback effects.

Promise class objects and async-generator request queues remain compatibility
operations. Native analysis rejects reachable boundaries instead of optimizing
through them.
