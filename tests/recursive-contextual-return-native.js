// Expected stdout: 42
//
// relay has no direct return-type seed: its base case calls a callback and its
// recursive branch only calls itself. The arithmetic use site should seed a
// Number specialization, while the recursive callback identity remains part
// of the specialization key. The large depth also exercises direct TCO.
function relay(n, thunk) {
    if (n === 0) {
        return thunk();
    }
    return relay(n - 1, thunk);
}

console.log(relay(200000, () => 41) + 1);
