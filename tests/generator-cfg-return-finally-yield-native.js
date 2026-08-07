function identity(value) { return value; }
function* guarded() {
  try {
    yield identity(40);
  } finally {
    yield identity(41);
  }
  return identity(99);
}
const it = guarded();
console.log(it.next().value);
let r = it.return(identity(42));
console.log(r.value);
console.log(r.done);
r = it.next();
console.log(r.value);
console.log(r.done);
