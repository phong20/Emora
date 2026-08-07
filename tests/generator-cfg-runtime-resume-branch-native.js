function identity(value) { return value; }
function* seq() {
  yield identity(40);
  yield identity(42);
}
const it = seq();
let r;
if (identity(1) === 1) {
  r = it.next();
} else {
  r = it.next();
}
console.log(r.value);
r = it.next();
console.log(r.value);
