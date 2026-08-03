const source = { a: 1, b: 2 };
const copied = { z: 0, ...source, b: 3, ..."xy", ...null };
console.log(copied.z, copied.a, copied.b, copied[0], copied[1]);
