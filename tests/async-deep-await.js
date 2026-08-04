// Expected:
// value 7
// branch 9

async function expressionAwait() {
    const value = 1 + (await Promise.resolve(6));
    return value;
}

async function branchAwait(flag) {
    if (flag) {
        const value = await Promise.resolve(9);
        console.log("branch", value);
    } else {
        await Promise.resolve(0);
    }
}

expressionAwait().then(value => console.log("value", value));
branchAwait(true);
