const unusedNumber = 40 + 2;
const onlyUsedByGhost = 999;

function supportedButNeverCalled() {
  console.log(onlyUsedByGhost);
}

function ghostWithPrivateField() {
  class Hidden {
    #value = 99;
  }
  return new Hidden();
}

function used(value) {
  return value * 2;
}

console.log(used(21));
