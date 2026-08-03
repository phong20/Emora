let used = 10;
let unusedNumber = 20;
let unusedString = "not captured";

const read = () => {
  return used + 1;
};

console.log(read());