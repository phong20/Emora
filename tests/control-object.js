let object = { count: 0, label: "start" };
while (object.count < 3) {
  object.count++;
}
let result = object.count === 3 ? "ok" : "bad";
switch (result) {
  case "bad":
    console.log("bad");
    break;
  case "ok":
    console.log(object.count, result);
    break;
  default:
    console.log("default");
}
