console.log(5 / 2);
console.log(1 / 0);
console.log(-1 / 0);
console.log(0 / 0);
console.log("x" + 1);
console.log(1 + "x");
console.log(!0, !"", !"x");
console.log("1" == 1, "1" === 1, 2 != 1, 2 !== 2);
console.log(2 <= 2, 2 >= 3, 2 ** 3);
console.log(5 & 3, 5 | 2, 5 ^ 1, 5 << 1, 5 >>> 1);
let value;
console.log(value);
value += "x";
console.log(value);
let x = 1, y = 2;
x *= y + 1;
console.log(x);
console.log(false || "fallback", true && 7, null ?? 9);
{
    let x = 99;
    console.log(x);
}
console.log(x);
