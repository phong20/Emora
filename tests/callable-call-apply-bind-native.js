function sum(a, b) {
  return this.base + a + b;
}
const receiver = { base: 30 };
const bound = sum.bind(receiver, 5);
console.log(sum.call(receiver, 5, 7));
console.log(sum.apply(receiver, [5, 7]));
console.log(bound(7));
