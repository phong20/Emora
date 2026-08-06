function compute(seed) {
  const base = { x: seed };
  const point = { ...base, y: 22 };
  point.y += 0;
  return base.x + point.y;
}

console.log(compute(20));
