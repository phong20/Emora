function identity(value) { return value; }
function* counter() {
  let value = identity(40);
  yield value;
  value += identity(2);
  yield value;
  return value + identity(1);
}
const it = counter();
const a = it.next();
console.log(a.value);
console.log(a.done);
const b = it.next();
console.log(b.value);
console.log(b.done);
const c = it.next();
console.log(c.value);
console.log(c.done);
