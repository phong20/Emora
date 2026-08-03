let object = { a: 1 };
console.log(typeof object, typeof missing, void 0, "a" in object, object instanceof Object);
console.log(delete object.a, "a" in object);
