function identity(value) { return value; }
class Counter {
  #value = identity(40);
  add(delta) { this.#value += delta; return this.#value; }
}
const counter = new Counter();
console.log(counter.add(identity(2)));
console.log(counter.add(identity(1)));
