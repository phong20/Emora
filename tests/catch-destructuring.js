function objectCatch() {
    try {
        throw { code: 7, message: "boom" };
    } catch ({ code, message }) {
        return code + ":" + message;
    }
}

function arrayCatch() {
    try {
        throw [4, 9];
    } catch ([left, right]) {
        return left + right;
    }
}

function optionalCatchBinding() {
    try {
        throw "ignored";
    } catch {
        return "ok";
    }
}

function throwFromCall() {
    throw "call";
}

function callCatch() {
    try {
        throwFromCall();
    } catch (error) {
        return "caught-" + error;
    }
}

function getterCatch() {
    const object = {
        get value() {
            throw "getter";
        }
    };
    try {
        return object.value;
    } catch (error) {
        return "caught-" + error;
    }
}

function coercionCatch() {
    const object = {
        valueOf() {
            throw "coerce";
        }
    };
    try {
        return object - 1;
    } catch (error) {
        return "caught-" + error;
    }
}

console.log(objectCatch());
console.log(arrayCatch());
console.log(optionalCatchBinding());
console.log(callCatch());
console.log(getterCatch());
console.log(coercionCatch());
