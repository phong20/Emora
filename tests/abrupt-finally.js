function preservedReturn() {
    try {
        return "try";
    } finally {
        console.log("finally-preserve");
    }
}

function overriddenReturn() {
    try {
        return "try";
    } finally {
        return "finally";
    }
}

function caughtThrow() {
    try {
        throw "boom";
    } catch (error) {
        return "caught:" + error;
    } finally {
        console.log("finally-catch");
    }
}

function loopCompletion() {
    let trace = "";
    outer: for (let i = 0; i < 3; i = i + 1) {
        try {
            if (i === 0) continue outer;
            if (i === 1) break outer;
            trace = trace + "bad";
        } finally {
            trace = trace + "f" + i;
        }
    }
    return trace;
}

console.log(preservedReturn());
console.log(overriddenReturn());
console.log(caughtThrow());
console.log(loopCompletion());
