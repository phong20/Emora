let value = 0;
while (value < 10) {
  value++;
  if (value < 3) continue;
  if (value === 5) break;
}
console.log(value);
