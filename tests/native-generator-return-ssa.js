function* values() { yield 40; yield 99; }
const it = values();
console.log(it.next().value);
const stopped = it.return(42);
console.log(stopped.value);
console.log(stopped.done);
const after = it.next();
console.log(after.value);
console.log(after.done);
