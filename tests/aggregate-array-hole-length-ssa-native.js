function inspect(left, right) {
  const values = [left, , right];
  console.log(values.length);
  console.log(1 in values);
  return values[0] + values[2];
}

console.log(inspect(10, 32));
