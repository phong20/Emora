// Expected:
// value 42
// nested 9
// getter boom

const thenable = {
    then(resolve) {
        resolve(42);
    }
};

const nested = {
    then(resolve) {
        resolve({
            then(innerResolve) {
                innerResolve(9);
            }
        });
    }
};

Promise.resolve(thenable).then(value => console.log("value", value));
Promise.resolve(nested).then(value => console.log("nested", value));

const bad = {
    get then() {
        throw "boom";
    }
};

Promise.resolve(bad).catch(reason => console.log("getter", reason));
