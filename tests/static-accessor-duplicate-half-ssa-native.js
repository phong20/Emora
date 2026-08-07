function identity(value) {
  return value;
}

let hidden = identity(1);
const proto = {
  set value(next) {
    hidden = next;
  },
  get value() {
    return 999;
  },
  get value() {
    return hidden;
  }
};
const object = Object.create(proto);
object.value = identity(42);
console.log(object.value);
