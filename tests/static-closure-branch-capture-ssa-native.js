function identity(value) {
  return value;
}

let state = identity(40);
const update = function update(flag) {
  if (flag) {
    state += identity(1);
  } else {
    state += identity(2);
  }
  return state;
};
console.log(update(true));
console.log(update(false));
