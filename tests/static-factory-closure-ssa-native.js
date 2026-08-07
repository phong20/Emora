function identity(value) {
  return value;
}

function makeCounter(seed) {
  let state = seed;
  return function add(delta) {
    state += delta;
    return state;
  };
}

const counter = makeCounter(identity(40));
console.log(counter(identity(2)));
console.log(counter(identity(1)));
