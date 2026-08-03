exports.base = 20;
exports.twice = (value) => value * 2;

function unusedLoader() {
  return require(Math.random() > 0.5 ? "a" : "b");
}
