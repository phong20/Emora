# Numeric tower and coercion boundaries

Ecmora now models ECMAScript numeric values as two disjoint domains:

- `Number`, represented by IEEE-754 binary64;
- `BigInt`, represented by arbitrary-precision signed integers in the
  compatibility runtime.

Arithmetic never silently mixes the domains. Operations such as `1n + 1`,
`1n ** 2n`, shifts, division, remainder and bitwise operations use BigInt.
Mixed Number/BigInt arithmetic raises an error, unary `+` rejects BigInt, and
unsigned right shift rejects BigInt.

## Observable coercion

The compatibility runtime performs `ToPrimitive` before arithmetic:

1. call `@@toPrimitive` when present;
2. otherwise call `valueOf` and `toString` in hint-dependent order;
3. require a primitive result.

Property reads and calls use the existing Proxy-aware object operations, so
coercion does not bypass traps, accessors or user callbacks.

`+` uses the default primitive hint and concatenates when either primitive is
a String. Other arithmetic uses `ToNumeric`. `Number(value)` is the explicit
conversion that may convert BigInt to Number; implicit Number arithmetic may
not.

## Native boundary

Native SSA does not represent BigInt yet. A reachable BigInt expression routes
the build to the compatibility executable.

Native `ToNumber` is emitted only when abstract analysis proves the runtime
value is drawn exclusively from:

`undefined | null | boolean | number | string`

This covers dynamic primitive phis and dynamic exponent operands while
excluding Object, Proxy, callable, Promise, Cell and BigInt. Observable
`ToPrimitive` therefore remains in the compatibility runtime rather than being
incorrectly folded into native arithmetic.
