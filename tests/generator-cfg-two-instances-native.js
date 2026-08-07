function identity(value) { return value; }
function* counter(seed) {
  let value = seed;
  while (value < seed + identity(2)) {
    yield value;
    value += identity(1);
  }
}
const a = counter(identity(10));
const b = counter(identity(20));
console.log(a.next().value);
console.log(b.next().value);
console.log(a.next().value);
console.log(b.next().value);
