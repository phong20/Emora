function compute() {
  let index = 0;
  let total = 0;
  while (index < 6) {
    total += 7;
    index++;
  }
  return total;
}
const callable = compute;
console.log(callable());
