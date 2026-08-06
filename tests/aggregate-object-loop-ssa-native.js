function compute(limit) {
  const state = { total: 0 };
  let index = 0;
  while (index < limit) {
    state.total += 7;
    index++;
  }
  return state.total;
}

console.log(compute(6));
