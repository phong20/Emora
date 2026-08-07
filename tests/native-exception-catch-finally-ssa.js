function identity(value) { return value; }
let value = identity(0);
try {
  value = identity(40);
  throw identity(2);
} catch (error) {
  value += error;
} finally {
  value += identity(0);
}
console.log(value);
