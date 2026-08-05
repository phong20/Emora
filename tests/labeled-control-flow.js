let trace = 0;

outer: for (let i = 0; i < 4; i = i + 1) {
    inner: for (let j = 0; j < 4; j = j + 1) {
        if (j === 1) continue inner;
        if (i === 1 && j === 2) continue outer;
        if (i === 2 && j === 2) break outer;
        trace = trace * 10 + (i * 4 + j + 1);
    }
}

blockExit: {
    trace = trace + 100;
    break blockExit;
    trace = trace + 900;
}

switchExit: switch (2) {
    case 1:
        trace = trace + 10;
        break;
    case 2:
        trace = trace + 1000;
        break switchExit;
    default:
        trace = trace + 10000;
}

console.log(trace);
