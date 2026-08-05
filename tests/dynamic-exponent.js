function power(base, exponent) {
    return base ** exponent;
}

function branch(flag) {
    const base = flag ? "3" : 2;
    const exponent = flag ? 2 : "3";
    return base ** exponent;
}

console.log(power("2", "10"));
console.log(power(null, false));
console.log(power(NaN, 0));
console.log(power(-1, Infinity));
console.log(branch(true));
console.log(branch(false));
