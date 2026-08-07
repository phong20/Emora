function identity(value) { return value; }
function* seq() {
  yield identity(42);
}
function make() {
  return seq();
}
const it = make();
console.log(it.next().value);
