function* inner() { yield 40; yield 42; }
function* outer() { yield* inner(); }
for (const value of outer()) {
  console.log(value);
}
