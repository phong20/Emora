function countdown(n) {
  if (n === 0) {
    return 42;
  }
  return countdown(n - 1);
}

const value = countdown(12000);
console.log(value + countdown(3) - 42);
