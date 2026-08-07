function identity(value) { return value; }
function* worker() {
  const sent = yield identity(40);
  yield sent + identity(2);
}
const it = worker();
console.log(it.next().value);
console.log(it.next(identity(40)).value);
console.log(it.next().done);
