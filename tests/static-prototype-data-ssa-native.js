function identity(value) {
  return value;
}

const proto = { base: identity(40) };
const object = Object.create(proto);
object.extra = identity(2);
console.log(object.base + object.extra);
