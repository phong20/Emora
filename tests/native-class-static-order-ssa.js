function identity(value) { return value; }
class Box {
  static x = identity(1);
  static { Box.x += identity(1); }
  static y = Box.x;
  static add(value) { return value + this.y; }
}
console.log(Box.x);
console.log(Box.y);
console.log(Box.add(identity(40)));
