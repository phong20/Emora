let value = 0;
while (value < 3) {
  value++;
}
let label = value === 3 ? "three" : "other";
switch (value) {
  case 1:
    console.log("one");
    break;
  case 3:
    console.log(label);
    break;
  default:
    console.log("default");
}
