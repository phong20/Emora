function add(a, b) {
  return a + b;
}

let counter = 1;
const increment = () => {
  counter = counter + 1;
  return counter;
};

function invoke(callback, value) {
  return callback(value);
}

console.log("call", add(2, 3), increment(), counter, invoke(value => value * 3, 4));

Promise.resolve(3)
  .then(value => value + 4)
  .then(value => console.log("then", value));

new Promise((resolve, reject) => resolve(7))
  .then(value => console.log("constructor", value));

Promise.reject("bad")
  .catch(reason => console.log("catch", reason))
  .finally(() => console.log("finally"));

Promise.resolve("start")
  .then(() => {
    throw "callback-error";
  })
  .catch(reason => console.log("callback-throw", reason));

Promise.resolve("kept")
  .finally(() => Promise.resolve("ignored"))
  .then(value => console.log("finally-kept", value));

console.log("sync");
