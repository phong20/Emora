function identity(value) {
  return value;
}

const protoA = {
  get value() {
    return 1;
  },
  value: identity(42)
};
const objectA = Object.create(protoA);
console.log(objectA.value);

const protoB = {
  value: identity(1),
  get value() {
    return 42;
  }
};
const objectB = Object.create(protoB);
console.log(objectB.value);
