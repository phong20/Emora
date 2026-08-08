// regression: runtime property value is not a compile-time constant
function identity(value) {
  return value;
}

let result = {
  value: identity(7),
  done: identity(false),
};

console.log(result.value);
console.log(result.done);

result = {
  value: identity(9),
  done: identity(true),
};

console.log(result.value);
console.log(result.done);
