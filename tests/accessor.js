let hidden = 1;
const object = {
  get value() {
    return hidden;
  },
  set value(next) {
    hidden = next;
  }
};

console.log(object.value);
object.value = 8;
console.log(object.value, hidden, "value" in object);
