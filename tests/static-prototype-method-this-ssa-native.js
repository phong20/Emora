function identity(value) {
  return value;
}

let bonus = identity(2);
const proto = {
  add: function add(delta) {
    this.total += delta + bonus;
    return this.total;
  }
};
const object = Object.create(proto);
object.total = identity(38);
console.log(object.add(identity(2)));
