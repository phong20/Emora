function identity(value) {
  return value;
}

function* seq(limit) {
  let i = identity(0);
  while (i < limit) {
    yield i;
    i += identity(1);
  }
  return i;
}

const it = seq(identity(1));

let r = it.next();
console.log(r.value);
console.log(r.done);

r = it.next();
console.log(r.value);
console.log(r.done);

r = it.next();
console.log(r.value);
console.log(r.done);
