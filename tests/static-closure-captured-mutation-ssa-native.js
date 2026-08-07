function identity(value) {
  return value;
}

let total = identity(40);
const add = function add(delta) {
  total += delta;
  return total;
};
console.log(add(identity(2)));
console.log(add(identity(1)));
