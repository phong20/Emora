function recursiveNumber(n) {
  if (n === 0) {
    return 6;
  }
  return recursiveNumber(n - 1);
}

function invoke(callback, value) {
  return callback(value);
}

function identity(value) {
  return value;
}

let total = 10;
total -= invoke(identity, 3);
total *= recursiveNumber(2);
const nested = (invoke(identity, 20) + invoke(identity, 22)) - 42;
console.log(total + -recursiveNumber(12000) + recursiveNumber(1) - 42 + nested);
