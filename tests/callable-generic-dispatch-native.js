function choose(flag) {
  return flag
    ? function (value) { return value + 2; }
    : function (value) { return value - 2; };
}
const functions = [choose(true), choose(false)];
const selected = functions[0];
console.log(selected(40));
console.log(functions[1](44));
