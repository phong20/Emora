function identity(value) { return value; }
function* seq() {
  yield identity(40);
  yield identity(42);
}
function pull(iterator) {
  return iterator.next().value;
}
const it = seq();
console.log(pull(it));
console.log(pull(it));
