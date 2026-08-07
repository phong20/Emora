function identity(value) { return value; }
class Box {
  #value;
  constructor(value) { this.#value = value; }
  get() { return this.#value; }
}
const box = new Box(identity(42));
console.log(box.get());
