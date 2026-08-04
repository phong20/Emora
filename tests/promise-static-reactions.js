// Expected:
// value 3
// reject bad
// finally
// after bad
//
// This exercises static Promise reaction lowering. No runtime Promise callback
// dispatch is required: callbacks become typed SSA calls and PromiseSettle.

function printValue(value) {
    console.log("value", value);
}

function printReject(reason) {
    console.log("reject", reason);
    return reason;
}

function printAfter(reason) {
    console.log("after", reason);
}

const original = Promise.resolve(3);
const identity = Promise.resolve(original);

original
    .then()
    .then(printValue);

Promise.reject("bad")
    .then()
    .catch(printReject)
    .finally(() => console.log("finally"))
    .then(value => {
        // catch fulfilled the chain with its return value.
        console.log("after", value);
    });

// Promise.resolve uses the identity fast path internally.
identity.then();
