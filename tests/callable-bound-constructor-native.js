function Pair(a, b) {
  this.total = a + b;
}
const BoundPair = Pair.bind(null, 40);
const pair = new BoundPair(2);
console.log(pair.total);
console.log(pair instanceof Pair);
