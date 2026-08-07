function identity(value) {
  return value;
}

let hidden = identity(40);
const proto = {
  set value(next) {
    hidden = next;
  },
  get value() {
    return hidden;
  }
};
const object = Object.create(proto);
object.value += identity(2);
console.log(object.value);
