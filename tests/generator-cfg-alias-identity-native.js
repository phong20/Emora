function identity(value) { return value; }
function* seq() {
  yield identity(40);
  yield identity(42);
}
const original = seq();
const alias = original;
console.log(alias.next().value);
console.log(original.next().value);
