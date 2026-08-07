function identity(value) {
  return value;
}

let hidden = identity(40);
const proto = {
  get value() {
    return hidden;
  },
  set value(next) {
    hidden = next;
  }
};
const object = Object.create(proto);
object.value = identity(42);
console.log(hidden);
console.log(object.value);
