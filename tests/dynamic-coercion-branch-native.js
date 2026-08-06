function compute(flag) {
  let value = 0;
  if (flag) {
    value = 40;
  } else {
    value = 41;
  }
  return value + 2;
}
const callable = compute;
console.log(callable(true));
