function sum3(a, b, c) {
  return a + b + c;
}

function compute(seed) {
  const values = [seed, 20, 12];
  return sum3(...values);
}

console.log(compute(10));
