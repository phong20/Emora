class TaggedPromise extends Promise {
    constructor(executor, label) {
        super(executor);
        this.label = label;
    }

    getLabel() {
        return this.label;
    }

    static get [Symbol.species]() {
        return Promise;
    }
}

const promise = new TaggedPromise((resolve) => resolve(7), "tagged");
console.log(promise.getLabel());
console.log(promise instanceof TaggedPromise);
console.log(promise instanceof Promise);
promise.then((value) => console.log(value));
