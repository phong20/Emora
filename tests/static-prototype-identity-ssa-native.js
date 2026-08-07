const proto = { marker: 1 };
const object = Object.create(proto);
console.log(Object.getPrototypeOf(object) === proto);
