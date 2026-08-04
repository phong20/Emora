// Expected:
// undefined
// object
// number
// boolean
// string
// object
// function
// object
// undefined
//
// choose() has one Number parameter specialization but several return types,
// forcing a Dynamic SSA result. typeof must inspect its runtime tag.

function callback() {
    return 1;
}

function choose(kind) {
    if (kind === 0) return;
    if (kind === 1) return null;
    if (kind === 2) return 42;
    if (kind === 3) return true;
    if (kind === 4) return "value";
    if (kind === 5) return {};
    if (kind === 6) return callback;
    return Promise.resolve(1);
}

function typeOfChoice(kind) {
    return typeof choose(kind);
}

console.log(typeOfChoice(0));
console.log(typeOfChoice(1));
console.log(typeOfChoice(2));
console.log(typeOfChoice(3));
console.log(typeOfChoice(4));
console.log(typeOfChoice(5));
console.log(typeOfChoice(6));
console.log(typeOfChoice(7));

// The special ECMAScript rule for an unresolved identifier remains static.
console.log(typeof completelyUndeclaredName);
