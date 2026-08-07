function identity(value) { return value; }
function boom() { throw identity(2); }
let value = identity(40);
try {
  boom();
} catch (error) {
  value += error;
}
console.log(value);
