function identity(value) { return value; }
let value = identity(0);
outer: {
  try {
    value = identity(40);
    break outer;
  } finally {
    value += identity(2);
  }
}
console.log(value);
