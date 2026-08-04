// Expected:
// caught sync
// after 7

Promise.resolve(1)
    .then(() => {
        throw "sync";
    })
    .catch(reason => {
        console.log("caught", reason);
        return 7;
    })
    .then(value => console.log("after", value));
