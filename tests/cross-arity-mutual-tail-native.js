function even(n) {
  if (n === 0) {
    return true;
  }
  return odd(n - 1, false);
}

function odd(n, ignored) {
  if (n === 0) {
    return false;
  }
  return even(n - 1);
}

console.log(even(20000));
