// Expected:
// sum 6
// rejected boom
//
// Each await becomes an analysis-owned continuation edge. The second and third
// await are discovered recursively rather than being flattened into one fake
// continuation.

async function sumThree() {
    const first = await Promise.resolve(1);
    const second = await Promise.resolve(2);
    const third = await Promise.resolve(3);
    return first + second + third;
}

async function failsBeforeContinuation() {
    const value = await Promise.reject("boom");
    console.log("unreachable", value);
    return value;
}

sumThree().then(value => console.log("sum", value));
failsBeforeContinuation().catch(reason => console.log("rejected", reason));
