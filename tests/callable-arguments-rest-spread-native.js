function forward(prefix, ...tail) {
  function read() {
    return arguments[0] + arguments[1] + arguments[2];
  }
  return read(prefix, ...tail);
}
console.log(forward(1, 20, 21));
