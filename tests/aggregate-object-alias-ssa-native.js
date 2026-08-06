function compute(base) {
  const point = { x: base, y: 2 };
  const alias = point;
  alias.x += 20;
  return point.x + point.y;
}

console.log(compute(20));
