async function failAfterAwait() {
  await Promise.resolve();
  throw "async-error";
}

async function forward() {
  return await Promise.resolve(11);
}

failAfterAwait().catch(reason => console.log("rejected", reason));
forward().then(value => console.log("forward", value));
console.log("scheduled");
