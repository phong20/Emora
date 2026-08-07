function identity(value) { return value; }
function* guarded() {
  try {
    yield identity(40);
    yield identity(41);
  } catch (error) {
    yield error + identity(2);
  }
  return identity(43);
}
const it = guarded();
console.log(it.next().value);
console.log(it.throw(identity(40)).value);
console.log(it.next().value);
