use std::path::Path;

use anyhow::Result;
use ecmora_ir::{Function, Instruction, Program, ValueType};

const DIRECT_RECURSION: &str = r#"
function factorial(n) {
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

console.log(factorial(5));
"#;

const MUTUAL_RECURSION: &str = r#"
function isEven(n) {
    if (n === 0) return true;
    return isOdd(n - 1);
}

function isOdd(n) {
    if (n === 0) return false;
    return isEven(n - 1);
}

console.log(isEven(10));
"#;

const UNSEEDED_ARITHMETIC_RECURSION: &str = r#"
function spin(n) {
    return spin(n - 1);
}

console.log(spin(3) + 1);
"#;

const POLYMORPHIC_RECURSION: &str = r#"
function descend(value, depth) {
    if (depth <= 0) return value;
    return descend("done", depth - 1);
}

console.log(descend(1, 1));
"#;

const RECURSIVE_CALLBACK: &str = r#"
function repeat(n, callback) {
    if (n <= 0) return 0;

    return repeat(n - 1, function next(value) {
        return callback(value);
    });
}

console.log(repeat(2, function seed(value) {
    return value;
}));
"#;

const TAIL_RECURSION: &str = r#"
function sumTo(n, acc) {
    if (n <= 0) return acc;
    return sumTo(n - 1, acc + n);
}

console.log(sumTo(1000000, 0));
"#;

const MUTUAL_TAIL_RECURSION: &str = r#"
function evenStep(n) {
    if (n === 0) return true;
    return oddStep(n - 1);
}

function oddStep(n) {
    if (n === 0) return false;
    return evenStep(n - 1);
}

console.log(evenStep(1000000));
"#;

const CALLBACK_TAIL_RECURSION: &str = r#"
function bounce(n, next) {
    if (n <= 0) return 0;
    return next(n - 1, bounce);
}

console.log(bounce(1000000, function step(n, next) {
    if (n <= 0) return 0;
    return next(n - 1, step);
}));
"#;

const DEEP_NON_TAIL_RECURSION: &str = r#"
function count(n) {
    if (n <= 0) return 0;
    return 1 + count(n - 1);
}

console.log(count(1000000));
"#;

const STACK_OVERFLOW: &str = r#"
function overflow() {
    return 1 + overflow();
}

overflow();
"#;

const SPECIALIZATION_BUDGET: &str = r#"
function specialize(depth, callback) {
    if (depth <= 0) return 0;

    return specialize(depth - 1, function nested(value) {
        return callback(value);
    });
}

console.log(specialize(1000000, function identity(value) {
    return value;
}));
"#;

const GENERIC_FALLBACK_BOUNDARY: &str = r#"
function crossBoundary(value, depth) {
    if (depth <= 0) return value;
    if (depth === 1) return crossBoundary({ value: value }, 0);
    return crossBoundary("fallback", depth - 1);
}

console.log(crossBoundary(1, 2));
"#;

fn lower(source: &str) -> Result<Program> {
    let hir = ecmora_frontend_oxc::lower_source(
        Path::new("recursive-semantics.js"),
        source,
    )?;

    ecmora_analysis::analyze(&hir)
}

fn lower_optimized(source: &str) -> Result<Program> {
    let mut program = lower(source)?;
    ecmora_opt::optimize(&mut program)?;
    Ok(program)
}

fn functions_named<'a>(program: &'a Program, fragment: &str) -> Vec<&'a Function> {
    program
        .functions
        .iter()
        .filter(|function| {
            function.return_type.is_some() && function.name.contains(fragment)
        })
        .collect()
}

fn only_function_named<'a>(program: &'a Program, fragment: &str) -> &'a Function {
    let functions = functions_named(program, fragment);

    assert_eq!(
        functions.len(),
        1,
        "expected exactly one generated function containing `{fragment}`, got {:?}",
        functions
            .iter()
            .map(|function| function.name.as_str())
            .collect::<Vec<_>>(),
    );

    functions[0]
}

fn instructions(function: &Function) -> impl Iterator<Item = &Instruction> {
    function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
}

fn has_direct_call(function: &Function, target: &str) -> bool {
    instructions(function).any(|instruction| {
        matches!(
            instruction,
            Instruction::CallDirect {
                function: callee,
                ..
            } if callee == target
        )
    })
}

#[test]
fn direct_recursion_with_number_seed_lowers_to_a_self_call() {
    let program = lower(DIRECT_RECURSION).expect("seeded recursion must lower");
    let factorial = only_function_named(&program, "factorial");

    assert_eq!(factorial.return_type, Some(ValueType::Number));
    assert!(
        has_direct_call(factorial, &factorial.name),
        "factorial specialization must call itself",
    );
}

#[test]
fn mutual_recursion_builds_a_two_function_cycle() {
    let program = lower(MUTUAL_RECURSION).expect("mutual recursion must lower");
    let even = only_function_named(&program, "isEven");
    let odd = only_function_named(&program, "isOdd");

    assert_eq!(even.return_type, Some(ValueType::Bool));
    assert_eq!(odd.return_type, Some(ValueType::Bool));
    assert!(has_direct_call(even, &odd.name));
    assert!(has_direct_call(odd, &even.name));
}

#[test]
fn repeated_calls_with_the_same_types_reuse_one_specialization() {
    let program = lower(
        r#"
function identity(value) {
    return value;
}

console.log(identity(1));
console.log(identity(2));
"#,
    )
    .expect("same-signature calls must lower");

    let specializations = functions_named(&program, "identity");
    assert_eq!(specializations.len(), 1);
    assert_eq!(specializations[0].return_type, Some(ValueType::Number));
}

#[test]
fn ordinary_call_site_polymorphism_creates_distinct_specializations() {
    let program = lower(
        r#"
function identity(value) {
    return value;
}

console.log(identity(1));
console.log(identity("one"));
"#,
    )
    .expect("non-recursive polymorphic calls must lower");

    let specializations = functions_named(&program, "identity");
    let mut return_types = specializations
        .iter()
        .map(|function| function.return_type.expect("JS function return type"))
        .collect::<Vec<_>>();
    return_types.sort_by_key(|value_type| format!("{value_type:?}"));

    assert_eq!(specializations.len(), 2);
    assert!(return_types.contains(&ValueType::Number));
    assert!(return_types.contains(&ValueType::String));
}

#[test]
fn tail_recursive_source_is_currently_still_a_normal_self_call() {
    let program = lower_optimized(TAIL_RECURSION)
        .expect("tail-recursive source must lower before TCO exists");
    let sum_to = only_function_named(&program, "sumTo");

    assert!(
        has_direct_call(sum_to, &sum_to.name),
        "phase 0 baseline: optimizer is not allowed to pretend TCO already exists",
    );
}

#[test]
fn unseeded_recursive_result_in_arithmetic_has_a_stable_baseline_diagnostic() {
    let error = lower(UNSEEDED_ARITHMETIC_RECURSION)
        .expect_err("expected-type propagation is not implemented yet");
    let message = format!("{error:#}");

    assert!(
        message.contains("dynamic/coercing binary operation"),
        "unexpected diagnostic: {message}",
    );
}

#[test]
fn polymorphic_recursion_has_a_stable_baseline_diagnostic() {
    let error = lower(POLYMORPHIC_RECURSION)
        .expect_err("polymorphic recursion is not implemented yet");
    let message = format!("{error:#}");

    assert!(
        message.contains("recursive specialization")
            && message.contains("predeclare")
            && message.contains("return String"),
        "unexpected diagnostic: {message}",
    );
}

#[test]
fn recursive_callback_specialization_has_a_stable_baseline_diagnostic() {
    let error = lower(RECURSIVE_CALLBACK)
        .expect_err("recursive callback specialization is not implemented yet");
    let message = format!("{error:#}");

    assert!(
        message.contains("recursive function")
            && message.contains("devirtualized callback")
            && message.contains("chưa được hỗ trợ"),
        "unexpected diagnostic: {message}",
    );
}

#[test]
fn all_recursive_contract_sources_are_valid_frontend_input() {
    for (name, source) in [
        ("unseeded arithmetic recursion", UNSEEDED_ARITHMETIC_RECURSION),
        ("polymorphic recursion", POLYMORPHIC_RECURSION),
        ("recursive callback", RECURSIVE_CALLBACK),
        ("tail recursion", TAIL_RECURSION),
        ("mutual tail recursion", MUTUAL_TAIL_RECURSION),
        ("callback tail recursion", CALLBACK_TAIL_RECURSION),
        ("deep non-tail recursion", DEEP_NON_TAIL_RECURSION),
        ("stack overflow", STACK_OVERFLOW),
        ("specialization budget", SPECIALIZATION_BUDGET),
        ("generic fallback boundary", GENERIC_FALLBACK_BOUNDARY),
    ] {
        ecmora_frontend_oxc::lower_source(
            Path::new("recursive-contract.js"),
            source,
        )
        .unwrap_or_else(|error| panic!("{name} fixture must parse: {error:#}"));
    }
}

#[test]
#[ignore = "phase 7: expected-type propagation into recursive SCCs"]
fn future_unseeded_recursive_result_uses_arithmetic_expected_type() {
    lower(UNSEEDED_ARITHMETIC_RECURSION)
        .expect("arithmetic context should seed the recursive return as Number");
}

#[test]
#[ignore = "phases 8-9: polymorphic recursion, budget and widening"]
fn future_polymorphic_recursion_builds_multiple_specializations() {
    let program = lower(POLYMORPHIC_RECURSION)
        .expect("polymorphic recursive calls should reach a fixed point");

    assert!(functions_named(&program, "descend").len() >= 2);
}

#[test]
#[ignore = "phases 10-11: first-class callable signatures and recursive callbacks"]
fn future_recursive_callback_specialization_compiles() {
    lower(RECURSIVE_CALLBACK)
        .expect("recursive callbacks should participate in the specialization graph");
}

#[test]
#[ignore = "phases 13-18: tail-position analysis and TailCall lowering"]
fn future_tail_recursion_removes_the_normal_self_call() {
    let program = lower_optimized(TAIL_RECURSION)
        .expect("tail-recursive source must optimize");
    let sum_to = only_function_named(&program, "sumTo");

    assert!(
        !has_direct_call(sum_to, &sum_to.name),
        "optimized tail recursion must not retain a normal recursive call",
    );
}

#[test]
#[ignore = "phase 16: mutual recursive SCC trampoline"]
fn future_mutual_tail_recursion_removes_normal_cycle_calls() {
    let program = lower_optimized(MUTUAL_TAIL_RECURSION)
        .expect("mutual tail-recursive source must optimize");
    let even = only_function_named(&program, "evenStep");
    let odd = only_function_named(&program, "oddStep");

    assert!(!has_direct_call(even, &odd.name));
    assert!(!has_direct_call(odd, &even.name));
}

#[test]
#[ignore = "phase 17: indirect and callback tail calls"]
fn future_callback_tail_recursion_compiles_for_tail_lowering() {
    lower_optimized(CALLBACK_TAIL_RECURSION)
        .expect("callback tail recursion must enter the optimizer");
}
