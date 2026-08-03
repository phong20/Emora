function bitOps(a, b) {
  return ((a & b) | (a ^ b)) + (a << 1) + (b >> 1) + (b >>> 1);
}

console.log(bitOps(5, 3));
console.log(~5);
