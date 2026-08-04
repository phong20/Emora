// Expected:
// resolved 7
// rejected nope
// thrown executor
// first first
//
// The executor is synchronous and the first resolving-function call wins.

new Promise((resolve, reject) => resolve(7))
    .then(value => console.log("resolved", value));

new Promise((resolve, reject) => reject("nope"))
    .catch(reason => console.log("rejected", reason));

new Promise((resolve, reject) => {
    throw "executor";
}).catch(reason => console.log("thrown", reason));

new Promise((resolve, reject) => {
    resolve("first");
    reject("second");
}).then(value => console.log("first", value));
