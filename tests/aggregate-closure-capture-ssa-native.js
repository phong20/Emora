function makeCounter(seed) {
  const state = { value: seed };
  return function add(delta) {
    state.value += delta;
    return state.value;
  };
}

const factory = makeCounter;
const counter = factory(40);
console.log(counter(2));
console.log(counter("2"));
