function compute(seed) {
  const point = { x: seed, y: 2 };
  point.x += 20;
  return point.x + point.y;
}

console.log(compute(20));
