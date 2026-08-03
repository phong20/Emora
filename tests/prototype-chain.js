const base = { inherited: 10 };
const child = Object.create(base);
child.own = 2;
console.log(child.inherited, child.own, "inherited" in child);

const replacement = { inherited: 20 };
Object.setPrototypeOf(child, replacement);
console.log(child.inherited, Object.getPrototypeOf(child) === replacement);

const copied = { ...child };
console.log(copied.own, copied.inherited);
