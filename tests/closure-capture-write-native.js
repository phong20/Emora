let counter = 1;
let untouched = 100;

const increment = () => {
  counter = counter + 1;
  return counter;
};

console.log(increment(), counter, increment(), counter, untouched);