console.log(value);
var value = 3;
{
    var value = 4;
}
console.log(value);

function echo(parameter) {
    var parameter;
    return parameter;
}

console.log(echo(9));
