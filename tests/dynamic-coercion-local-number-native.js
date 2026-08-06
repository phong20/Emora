function compute() {
  let value = 20;
  value += 1;
  value *= 2;
  return value;
}
const callable = compute;
console.log(callable());
