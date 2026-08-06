function outer() {
  const read = () => this.value;
  return read.call({ value: 1 });
}
console.log(outer.call({ value: 42 }));
