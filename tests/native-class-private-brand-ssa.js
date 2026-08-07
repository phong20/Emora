class Box {
  #value = 1;
  hasBrand() { return #value in this; }
  static has(value) { return #value in value; }
}
class Other { #value = 1; }
const box = new Box();
const other = new Other();
console.log(box.hasBrand());
console.log(Box.has(box));
console.log(Box.has(other));
