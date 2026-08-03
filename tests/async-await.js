async function calculate(value) {
  console.log("before-await");
  const next = await Promise.resolve(value + 1);
  console.log("after-await");
  return next * 2;
}

calculate(2).then(value => console.log("async", value));
console.log("after-call");
