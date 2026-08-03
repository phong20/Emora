// Expected behavior: process aborts with an Ecmora RangeError mentioning
// maximum native recursion depth, before the operating-system stack overflows.
// This is intentionally a negative runtime fixture and should not be included
// in a success-only test loop.
function nonTail(n) {
    if (n === 0) {
        return 0;
    }
    return 1 + nonTail(n - 1);
}

console.log(nonTail(100000));
