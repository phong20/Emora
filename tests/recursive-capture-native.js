let step = 2;
let unused = 100;

function total(n) {
  if (n === 0) {
    return 0;
  }

  return step + total(n - 1);
}

console.log(total(4));