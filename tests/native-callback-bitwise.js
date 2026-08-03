function onMessage(message) {
  console.log(message);
}
const handlers = { message: onMessage };
function finished() { console.log("done"); }
Promise.resolve(1).then(finished);
function recursiveA() { recursiveB(); }
function recursiveB() { recursiveA(); }
console.log((5 & 3) | (8 ^ 2));
console.log(1 ? 7 : 8);
