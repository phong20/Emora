const values = [1, 2, 3, 4];
let sum = 0;
for (const value of values) {
  sum = sum + value;
}

const object = { a: 1, b: 2 };
let keys = "";
for (const key in object) {
  keys = keys + key;
}

console.log(sum, keys);
