function choose(flag) {
  function left(value) { return value + 1; }
  function right(value) { return value + 2; }
  return flag ? left : right;
}
const table = { fn: choose(true) };
console.log(table.fn(41));
