function identity(value) { return value; }
class Base {
  #base = identity(40);
  get base() { return this.#base; }
}
class Child extends Base {
  #extra = identity(2);
  total() { return this.base + this.#extra; }
}
const value = new Child();
console.log(value.total());
console.log(value instanceof Base);
console.log(value instanceof Child);
