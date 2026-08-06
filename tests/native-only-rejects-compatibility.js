// Native-only policy regression.
//
// This program intentionally requires BigInt semantics that the native numeric
// tower has not implemented yet. `ecmora build` must fail. It must never embed
// this source into a compatibility executable.
function unsupportedBigInt(n) {
  if (n === 0) {
    return 1n;
  }
  return unsupportedBigInt(n - 1);
}

console.log(unsupportedBigInt(8) + 1n);
