function add(left, right) {
  return left + right;
}
const callable = add;
console.log(callable(40, 2));
console.log(callable("4", "2"));
