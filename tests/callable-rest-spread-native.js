function sum(first, ...rest) { return first + rest[0] + rest[1]; }
const values = [20, 21];
console.log(sum(1, ...values));
