function identity(value) {
  return value;
}

let stored = identity(40);
let reads = 0;
let writes = 0;
const proto = {
  get value() {
    reads += 1;
    return stored;
  },
  set value(next) {
    writes += 1;
    stored = next;
  }
};
const object = Object.create(proto);
object.value += (stored = identity(2));
console.log(stored);
console.log(reads);
console.log(writes);
