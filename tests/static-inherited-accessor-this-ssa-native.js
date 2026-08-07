function identity(value) {
  return value;
}

const proto = {
  get doubled() {
    return this.raw * identity(2);
  },
  set doubled(value) {
    this.raw = value / identity(2);
  }
};
const object = Object.create(proto);
object.raw = identity(0);
object.doubled = identity(42);
console.log(object.doubled);
