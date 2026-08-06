function Box(value) {
  this.value = value;
}
const Constructor = Box;
const box = new Constructor(42);
console.log(box.value);
