function bigintLeaf(n) {
  if (n === 0) {
    return 1n;
  }
  return bigintLeaf(n - 1);
}

console.log(bigintLeaf(4) - 1);
