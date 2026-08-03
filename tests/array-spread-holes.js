const sparse = [1, , 3];
console.log(sparse.length, 1 in sparse, sparse[1]);
delete sparse[0];
console.log(sparse.length, 0 in sparse, sparse[1], sparse[2]);

const spread = [0, ...sparse, ..."ab"];
console.log(spread.length, 1 in spread, spread[0], spread[1], spread[3], spread[4], spread[5]);

for (const value of sparse) {
  console.log("iter", value);
}
