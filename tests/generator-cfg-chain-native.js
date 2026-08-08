function identity(value) {
  return value;
}

function* seq() {
  yield identity(40);
  yield identity(42);
}

const it = seq();
console.log(it.next().value);
console.log(it.next().value);
