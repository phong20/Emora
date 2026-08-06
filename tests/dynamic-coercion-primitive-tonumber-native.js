function compute() {
  const truth = true;
  const empty = null;
  return +truth + +empty + 41;
}
const callable = compute;
console.log(callable());
