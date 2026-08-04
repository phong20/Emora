async function* sequence() {
    var input = yield 1;
    yield input + 1;
    return 9;
}

const iterator = sequence();

iterator.next().then((result) => {
    console.log(result.value, result.done);
});

iterator.next(4).then((result) => {
    console.log(result.value, result.done);
});

iterator.next().then((result) => {
    console.log(result.value, result.done);
});
