const [first, , third] = [1, , 3];
const { x, nested: { value } } = { x: 2, nested: { value: 7 } };
console.log(first, third, x, value);
