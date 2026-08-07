function identity(value) {
  return value;
}

const proto = { value: identity(40) };
const object = Object.create(proto);
console.log(object.value);
object.value = identity(42);
console.log(object.value);
console.log(proto.value);
