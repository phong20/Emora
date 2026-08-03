let outer = 10;
let unrelated = 50;

const calculate = () => {
  let unrelated = 2;
  return outer + unrelated;
};

console.log(calculate());