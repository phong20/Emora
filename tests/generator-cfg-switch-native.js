function identity(value) { return value; }
function* choose(value) {
  switch (value) {
    case 1:
      yield identity(40);
      break;
    default:
      yield identity(42);
  }
  return identity(43);
}
const a = choose(identity(1));
console.log(a.next().value);
console.log(a.next().value);
const b = choose(identity(2));
console.log(b.next().value);
