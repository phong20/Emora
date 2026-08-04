// Expected:
// 1024
// 3
// -8
// 0.125
// true
// true
// true
// true
//
// The operands are parameters, so these expressions cannot be constant-folded.
// They must reach typed SSA BinaryNumberOperator::Exponential and llvm.pow.f64.

function power(base, exponent) {
    return base ** exponent;
}

function isNaNValue(value) {
    return value !== value;
}

console.log(power(2, 10));
console.log(power(9, 0.5));
console.log(power(-2, 3));
console.log(power(2, -3));

// ECMAScript-specific cases that differ from a raw C/LLVM pow in some hosts.
console.log(isNaNValue(power(1, Infinity)));
console.log(power(NaN, 0) === 1);
console.log(isNaNValue(power(1, NaN)));
console.log(power(-0, -3) === -Infinity);
