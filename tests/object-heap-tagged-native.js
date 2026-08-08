function keep(value) {
  return value;
}

let holder = keep({});

console.log(holder.value);

holder.value = keep(2);
console.log(holder.value);

holder.value = keep("x");
console.log(holder.value);

holder.value = keep(1);
holder.value += keep(2);
console.log(holder.value);

holder.value = keep("x");
holder.value += keep(2);
console.log(holder.value);

holder.value = undefined;
console.log(holder.value);
