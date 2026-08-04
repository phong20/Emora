function value(flag) {
  if (flag) {
    throw "boom";
  }
  return 42;
}

console.log(value(false));
