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
object.value += identity(2);
console.log(object.value);
