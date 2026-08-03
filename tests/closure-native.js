let counter = 1;
const increment = () => {
  counter = counter + 1;
  return counter;
};

console.log(increment(), counter, increment(), counter);
