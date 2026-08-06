function read() {
  return this.value;
}
const object = { value: 42, read };
console.log(object.read());
