function inspect() {
  let value = 42;
  return typeof value;
}
const callable = inspect;
console.log(callable());
