let sum = 0;
for (let i = 0; i < 5; i++) {
  if (i < 2) continue;
  sum += i;
}
console.log(sum);
