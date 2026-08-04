// Expected:
// true
// species true

class ParentPromise extends Promise {}
class SpeciesPromise extends Promise {}
class ChildPromise extends ParentPromise {
    static get [Symbol.species]() {
        return SpeciesPromise;
    }
}

const original = ChildPromise.resolve(1);
console.log(original instanceof ChildPromise);
const derived = original.then(value => value + 1);
console.log("species", derived instanceof SpeciesPromise);
