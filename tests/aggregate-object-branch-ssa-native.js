function compute(flag, base) {
  const state = { value: 0 };
  if (flag) {
    state.value = base;
  } else {
    state.value = base + 1;
  }
  return state.value + 2;
}

console.log(compute(true, 40));
