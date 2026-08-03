// Expected stdout: 200000
//
// `step` is devirtualized, forwarded through every recursive call, and must be
// included in the recursive specialization key without occupying an argv slot.
function fold(n, acc, step) {
    if (n === 0) {
        return acc;
    }
    return fold(n - 1, step(acc), step);
}

function increment(value) {
    return value + 1;
}

console.log(fold(200000, 0, increment));
