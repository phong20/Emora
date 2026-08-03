// Expected stdout: 7
//
// The recursive call alternates the second parameter between Number and
// String. The compiler should create a finite two-node specialization cycle
// instead of recursively generating functions forever. Both edges are in tail
// position and should reuse the native argv buffer.
function bounce(n, value) {
    if (n === 0) {
        return 7;
    }
    if (typeof value === "number") {
        return bounce(n - 1, "next");
    }
    return bounce(n - 1, 1);
}

console.log(bounce(200000, 1));
