// Compatibility-runtime regression fixture.
//
// Expected:
// get value
// 7
// set value 9
// has value
// true
// ownKeys
// value

const target = { value: 7 };
const proxy = new Proxy(target, {
    get(target, key, receiver) {
        console.log("get", key);
        return target[key];
    },
    set(target, key, value, receiver) {
        console.log("set", key, value);
        target[key] = value;
        return true;
    },
    has(target, key) {
        console.log("has", key);
        return key in target;
    },
    ownKeys(target) {
        console.log("ownKeys");
        return ["value"];
    }
});

console.log(proxy.value);
proxy.value = 9;
console.log("value" in proxy);
for (const key in proxy) {
    console.log(key);
}
