function invoke(callback, value) {
  return callback(value);
}

console.log(invoke(value => value * 3, 4));
