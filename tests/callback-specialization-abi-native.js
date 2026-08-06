function invoke(callback, value) {
  return callback(value);
}

function twice(value) {
  return value * 2;
}

console.log(invoke(twice, 21));
