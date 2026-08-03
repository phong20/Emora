const [first, , third = 9] = [1, , undefined];
const { x, y: renamed = 4, nested: { value } } = {
  x: 2,
  nested: { value: 7 }
};

console.log(first, third, x, renamed, value);
