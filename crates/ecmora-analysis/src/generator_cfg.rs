use anyhow::{Result, bail};
use ecmora_hir::{
    AssignmentOperator, AssignmentTarget, BinaryOperator, CatchClause, Expression, ExpressionKind,
    ForInit, Function, LogicalOperator, MemberProperty, ObjectEntry, ObjectProperty, Program, Span,
    Statement, StatementKind, SwitchCase, UnaryOperator, VariableDeclarator, VariableKind,
};
use std::collections::{HashMap, HashSet};

type StateId = u32;
const FRAME: &str = "@gen_frame";
const INPUT_PARAM: &str = "@gen_value";
const PC: &str = "@gen_pc";
const STARTED: &str = "@gen_started";
const DONE: &str = "@gen_done";
const OUT: &str = "@gen_out";
const OUT_DONE: &str = "@gen_out_done";
const RESUME_KIND: &str = "@gen_resume_kind";
const INPUT: &str = "@gen_input";
const EXCEPTION: &str = "@gen_exception";
const RETURN_VALUE: &str = "@gen_return";
const NEXT_KIND: f64 = 0.0;
const THROW_KIND: f64 = 1.0;
const RETURN_KIND: f64 = 2.0;

#[derive(Clone)]
struct Template {
    source: String,
    factory: String,
    resume: String,
    function: Function,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SeedType {
    Number,
    Bool,
    String,
}

#[derive(Clone)]
struct Slot {
    field: String,
    kind: VariableKind,
    parameter: bool,

    seed: Option<SeedType>,
}

#[derive(Clone, Copy, Debug, Default)]
struct SeedFact {
    value: Option<SeedType>,
    seen: bool,
    poisoned: bool,
}

impl SeedFact {
    fn observe(&mut self, value: Option<SeedType>) {
        self.seen = true;
        match (self.value, value) {
            (_, None) => self.poisoned = true,
            (None, Some(value)) => self.value = Some(value),
            (Some(current), Some(value)) if current == value => {}
            (Some(_), Some(_)) => self.poisoned = true,
        }
    }

    fn resolved(self) -> Option<SeedType> {
        (self.seen && !self.poisoned)
            .then_some(self.value)
            .flatten()
    }
}

struct SeedOracle {
    functions: HashMap<String, Function>,
    closed_generators: HashSet<String>,
    generator_parameters: HashMap<String, Vec<Option<SeedType>>>,
    protocol_throw: HashMap<String, SeedFact>,
    protocol_return: HashMap<String, SeedFact>,
}

impl SeedOracle {
    fn build(program: &Program, templates: &HashMap<String, Template>) -> Self {
        let functions = program
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StatementKind::FunctionDeclaration(function) => function
                    .name
                    .as_ref()
                    .map(|name| (name.clone(), function.clone())),
                _ => None,
            })
            .collect::<HashMap<_, _>>();
        let generator_names = templates.keys().cloned().collect::<HashSet<_>>();
        let wrappers = collect_generator_wrappers(&functions, &generator_names);
        let exported = program
            .exports
            .iter()
            .map(|binding| binding.local.clone())
            .collect::<HashSet<_>>();
        let mut closed_generators = generator_names.clone();
        for source in &generator_names {
            if exported.contains(source) || generator_reference_escapes(program, source) {
                closed_generators.remove(source);
            }
        }
        for (wrapper, source) in &wrappers {
            if exported.contains(wrapper) {
                closed_generators.remove(source);
            }
        }

        let mut parameter_facts = templates
            .iter()
            .map(|(name, template)| {
                (
                    name.clone(),
                    vec![SeedFact::default(); template.function.parameters.len()],
                )
            })
            .collect::<HashMap<_, _>>();
        let env = HashMap::new();
        let mut stack = HashSet::new();
        for statement in &program.statements {
            observe_generator_calls_statement(
                statement,
                &generator_names,
                &functions,
                &env,
                &mut stack,
                &mut parameter_facts,
            );
        }
        let generator_parameters = parameter_facts
            .into_iter()
            .map(|(name, facts)| (name, facts.into_iter().map(SeedFact::resolved).collect()))
            .collect::<HashMap<_, _>>();

        let mut throw_facts = templates
            .keys()
            .map(|name| (name.clone(), SeedFact::default()))
            .collect::<HashMap<_, _>>();
        let mut return_facts = templates
            .keys()
            .map(|name| (name.clone(), SeedFact::default()))
            .collect::<HashMap<_, _>>();
        let mut instances = HashMap::new();
        for statement in &program.statements {
            scan_protocol_statement(
                statement,
                &functions,
                &generator_names,
                &wrappers,
                &mut instances,
                &mut throw_facts,
                &mut return_facts,
            );
        }

        Self {
            functions,
            closed_generators,
            generator_parameters,
            protocol_throw: throw_facts,
            protocol_return: return_facts,
        }
    }

    fn parameter_env(&self, source: &str, function: &Function) -> HashMap<String, SeedType> {
        if !self.closed_generators.contains(source) {
            return HashMap::new();
        }
        let observed = self.generator_parameters.get(source);
        function
            .parameters
            .iter()
            .enumerate()
            .filter_map(|(index, parameter)| {
                observed
                    .and_then(|values| values.get(index))
                    .copied()
                    .flatten()
                    .map(|value| (parameter.clone(), value))
            })
            .collect()
    }

    fn local_slot_seeds(&self, template: &Template) -> HashMap<String, SeedType> {
        if !self.closed_generators.contains(&template.source) {
            return HashMap::new();
        }

        let mut env = self.parameter_env(&template.source, &template.function);
        let mut facts = HashMap::<String, SeedFact>::new();
        collect_local_slot_seed_facts(
            &template.function.body,
            &mut env,
            &self.functions,
            &mut facts,
        );
        let mut seeds = facts
            .into_iter()
            .filter_map(|(name, fact)| fact.resolved().map(|seed| (name, seed)))
            .collect::<HashMap<_, _>>();

        // A catch parameter may be seeded only when every closed-world
        // protocol throw into this generator has one primitive type and the
        // generator body itself has no independent throwing source.
        if let Some(throw_seed) = self
            .protocol_throw
            .get(&template.source)
            .copied()
            .and_then(SeedFact::resolved)
            .filter(|_| generator_protocol_throw_only(&template.function, &self.functions))
        {
            collect_catch_seed_names(&template.function.body, throw_seed, &mut seeds);
        }

        seeds
    }

    fn infer_generator_expression(
        &self,
        template: &Template,
        local_seeds: &HashMap<String, SeedType>,
        expression: &Expression,
    ) -> Option<SeedType> {
        let mut env = self.parameter_env(&template.source, &template.function);
        env.extend(
            local_seeds
                .iter()
                .map(|(name, value)| (name.clone(), *value)),
        );
        let mut stack = HashSet::new();
        infer_seed_expression(expression, &env, &self.functions, &mut stack)
    }

    fn exception_seed(&self, template: &Template) -> Option<SeedType> {
        self.closed_generators
            .contains(&template.source)
            .then(|| {
                self.protocol_throw
                    .get(&template.source)
                    .copied()
                    .and_then(SeedFact::resolved)
                    .filter(|_| generator_protocol_throw_only(&template.function, &self.functions))
            })
            .flatten()
    }

    fn return_seed(
        &self,
        template: &Template,
        local_seeds: &HashMap<String, SeedType>,
    ) -> Option<SeedType> {
        let mut fact = if self.closed_generators.contains(&template.source) {
            self.protocol_return
                .get(&template.source)
                .copied()
                .unwrap_or_default()
        } else {
            SeedFact::default()
        };
        let mut env = self.parameter_env(&template.source, &template.function);
        env.extend(local_seeds.iter().map(|(name, seed)| (name.clone(), *seed)));
        let mut stack = HashSet::new();
        observe_generator_returns(
            &template.function.body,
            &env,
            &self.functions,
            &mut stack,
            &mut fact,
        );
        fact.resolved()
    }
}

fn seed_expression(seed: SeedType, span: Span) -> Expression {
    match seed {
        SeedType::Number => num_expr(0.0, span),
        SeedType::Bool => bool_expr(false, span),
        SeedType::String => Expression {
            kind: ExpressionKind::String(String::new()),
            span,
        },
    }
}

fn infer_seed_expression(
    expression: &Expression,
    env: &HashMap<String, SeedType>,
    functions: &HashMap<String, Function>,
    stack: &mut HashSet<String>,
) -> Option<SeedType> {
    match &expression.kind {
        ExpressionKind::Number(_) => Some(SeedType::Number),
        ExpressionKind::Bool(_) => Some(SeedType::Bool),
        ExpressionKind::String(_) => Some(SeedType::String),
        ExpressionKind::Global(name) => env.get(name).copied(),
        ExpressionKind::Unary { operator, argument } => match operator {
            UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitwiseNot => {
                infer_seed_expression(argument, env, functions, stack)
                    .filter(|value| *value == SeedType::Number)
            }
            UnaryOperator::Not => Some(SeedType::Bool),
            UnaryOperator::Typeof => Some(SeedType::String),
            UnaryOperator::Void | UnaryOperator::Delete => None,
        },
        ExpressionKind::Binary {
            left,
            operator,
            right,
        } => {
            let left = infer_seed_expression(left, env, functions, stack);
            let right = infer_seed_expression(right, env, functions, stack);
            match operator {
                BinaryOperator::Add => match (left, right) {
                    (Some(SeedType::Number), Some(SeedType::Number)) => Some(SeedType::Number),
                    (Some(SeedType::String), Some(_)) | (Some(_), Some(SeedType::String)) => {
                        Some(SeedType::String)
                    }
                    _ => None,
                },
                BinaryOperator::Subtract
                | BinaryOperator::Multiply
                | BinaryOperator::Divide
                | BinaryOperator::Remainder
                | BinaryOperator::Exponential
                | BinaryOperator::ShiftLeft
                | BinaryOperator::ShiftRight
                | BinaryOperator::ShiftRightZeroFill
                | BinaryOperator::BitwiseOr
                | BinaryOperator::BitwiseXor
                | BinaryOperator::BitwiseAnd => (left == Some(SeedType::Number)
                    && right == Some(SeedType::Number))
                .then_some(SeedType::Number),
                BinaryOperator::Equal
                | BinaryOperator::NotEqual
                | BinaryOperator::StrictEqual
                | BinaryOperator::StrictNotEqual
                | BinaryOperator::LessThan
                | BinaryOperator::LessEqual
                | BinaryOperator::GreaterThan
                | BinaryOperator::GreaterEqual
                | BinaryOperator::In
                | BinaryOperator::InstanceOf => Some(SeedType::Bool),
            }
        }
        ExpressionKind::Logical { left, right, .. } => {
            let left = infer_seed_expression(left, env, functions, stack);
            let right = infer_seed_expression(right, env, functions, stack);
            (left == right).then_some(left).flatten()
        }
        ExpressionKind::Conditional {
            consequent,
            alternate,
            ..
        } => {
            let consequent = infer_seed_expression(consequent, env, functions, stack);
            let alternate = infer_seed_expression(alternate, env, functions, stack);
            (consequent == alternate).then_some(consequent).flatten()
        }
        ExpressionKind::Assignment {
            target,
            operator,
            value,
        } => {
            let rhs = infer_seed_expression(value, env, functions, stack);
            match operator {
                AssignmentOperator::Assign => rhs,
                AssignmentOperator::Add => {
                    let left = match target {
                        AssignmentTarget::Identifier(name) => env.get(name).copied(),
                        AssignmentTarget::Member { .. } => None,
                    };
                    match (left, rhs) {
                        (Some(SeedType::Number), Some(SeedType::Number)) => Some(SeedType::Number),
                        (Some(SeedType::String), Some(_)) | (Some(_), Some(SeedType::String)) => {
                            Some(SeedType::String)
                        }
                        _ => None,
                    }
                }
                AssignmentOperator::Subtract
                | AssignmentOperator::Multiply
                | AssignmentOperator::Divide
                | AssignmentOperator::Remainder
                | AssignmentOperator::Exponential
                | AssignmentOperator::ShiftLeft
                | AssignmentOperator::ShiftRight
                | AssignmentOperator::ShiftRightZeroFill
                | AssignmentOperator::BitwiseOr
                | AssignmentOperator::BitwiseXor
                | AssignmentOperator::BitwiseAnd => {
                    let left = match target {
                        AssignmentTarget::Identifier(name) => env.get(name).copied(),
                        AssignmentTarget::Member { .. } => None,
                    };
                    (left == Some(SeedType::Number) && rhs == Some(SeedType::Number))
                        .then_some(SeedType::Number)
                }
                AssignmentOperator::LogicalOr
                | AssignmentOperator::LogicalAnd
                | AssignmentOperator::LogicalNullish => None,
            }
        }
        ExpressionKind::Update { target, .. } => match target {
            AssignmentTarget::Identifier(name) => env
                .get(name)
                .copied()
                .filter(|value| *value == SeedType::Number),
            AssignmentTarget::Member { .. } => None,
        },
        ExpressionKind::Call { callee, arguments } => {
            let ExpressionKind::Global(name) = &callee.kind else {
                return None;
            };
            match name.as_str() {
                "Number" => return Some(SeedType::Number),
                "Boolean" => return Some(SeedType::Bool),
                "String" => return Some(SeedType::String),
                _ => {}
            }
            let function = functions.get(name)?;
            if function.generator || function.r#async || !stack.insert(name.clone()) {
                return None;
            }
            let argument_types = arguments
                .iter()
                .map(|argument| infer_seed_expression(argument, env, functions, stack))
                .collect::<Vec<_>>();
            let result = infer_seed_function(function, &argument_types, functions, stack);
            stack.remove(name);
            result
        }
        ExpressionKind::Null
        | ExpressionKind::BigInt(_)
        | ExpressionKind::This
        | ExpressionKind::Member { .. }
        | ExpressionKind::Object(_)
        | ExpressionKind::Array(_)
        | ExpressionKind::New { .. }
        | ExpressionKind::Function(_)
        | ExpressionKind::Await(_) => None,
    }
}

fn infer_seed_function(
    function: &Function,
    arguments: &[Option<SeedType>],
    functions: &HashMap<String, Function>,
    stack: &mut HashSet<String>,
) -> Option<SeedType> {
    let mut env = function
        .parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| {
            arguments
                .get(index)
                .copied()
                .flatten()
                .map(|value| (parameter.clone(), value))
        })
        .collect::<HashMap<_, _>>();
    let mut returns = Vec::new();
    infer_seed_statements(&function.body, &mut env, functions, stack, &mut returns);
    let mut iter = returns.into_iter();
    let first = iter.next().flatten()?;
    iter.all(|value| value == Some(first)).then_some(first)
}

fn infer_seed_statements(
    statements: &[Statement],
    env: &mut HashMap<String, SeedType>,
    functions: &HashMap<String, Function>,
    stack: &mut HashSet<String>,
    returns: &mut Vec<Option<SeedType>>,
) {
    for statement in statements {
        match &statement.kind {
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    let value = declaration
                        .init
                        .as_ref()
                        .and_then(|value| infer_seed_expression(value, env, functions, stack));
                    if let Some(value) = value {
                        env.insert(declaration.name.clone(), value);
                    } else {
                        env.remove(&declaration.name);
                    }
                }
            }
            StatementKind::Expression(Expression {
                kind:
                    ExpressionKind::Assignment {
                        target: AssignmentTarget::Identifier(name),
                        operator: AssignmentOperator::Assign,
                        value,
                    },
                ..
            }) => {
                let value = infer_seed_expression(value, env, functions, stack);
                if let Some(value) = value {
                    env.insert(name.clone(), value);
                } else {
                    env.remove(name);
                }
            }
            StatementKind::Return(value) => returns.push(
                value
                    .as_ref()
                    .and_then(|value| infer_seed_expression(value, env, functions, stack)),
            ),
            StatementKind::Block(body) => {
                let mut nested = env.clone();
                infer_seed_statements(body, &mut nested, functions, stack, returns);
            }
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                let mut left = env.clone();
                infer_seed_statements(
                    std::slice::from_ref(consequent.as_ref()),
                    &mut left,
                    functions,
                    stack,
                    returns,
                );
                if let Some(alternate) = alternate {
                    let mut right = env.clone();
                    infer_seed_statements(
                        std::slice::from_ref(alternate.as_ref()),
                        &mut right,
                        functions,
                        stack,
                        returns,
                    );
                }
            }
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    let mut nested = env.clone();
                    infer_seed_statements(&case.consequent, &mut nested, functions, stack, returns);
                }
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                let mut nested = env.clone();
                infer_seed_statements(
                    std::slice::from_ref(block.as_ref()),
                    &mut nested,
                    functions,
                    stack,
                    returns,
                );
                if let Some(handler) = handler {
                    let mut nested = env.clone();
                    infer_seed_statements(
                        std::slice::from_ref(handler.body.as_ref()),
                        &mut nested,
                        functions,
                        stack,
                        returns,
                    );
                }
                if let Some(finalizer) = finalizer {
                    let mut nested = env.clone();
                    infer_seed_statements(
                        std::slice::from_ref(finalizer.as_ref()),
                        &mut nested,
                        functions,
                        stack,
                        returns,
                    );
                }
            }
            StatementKind::While { .. }
            | StatementKind::DoWhile { .. }
            | StatementKind::For { .. }
            | StatementKind::ForIn { .. }
            | StatementKind::ForOf { .. }
            | StatementKind::Labeled { .. }
            | StatementKind::FunctionDeclaration(_)
            | StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Expression(_)
            | StatementKind::Throw(_)
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
        }
    }
}

fn observe_generator_calls_statement(
    statement: &Statement,
    generator_names: &HashSet<String>,
    functions: &HashMap<String, Function>,
    env: &HashMap<String, SeedType>,
    stack: &mut HashSet<String>,
    facts: &mut HashMap<String, Vec<SeedFact>>,
) {
    fn expression(
        value: &Expression,
        generator_names: &HashSet<String>,
        functions: &HashMap<String, Function>,
        env: &HashMap<String, SeedType>,
        stack: &mut HashSet<String>,
        facts: &mut HashMap<String, Vec<SeedFact>>,
    ) {
        if let ExpressionKind::Call { callee, arguments } = &value.kind {
            if let ExpressionKind::Global(name) = &callee.kind {
                if generator_names.contains(name) {
                    if let Some(parameter_facts) = facts.get_mut(name) {
                        for (index, fact) in parameter_facts.iter_mut().enumerate() {
                            fact.observe(arguments.get(index).and_then(|argument| {
                                infer_seed_expression(argument, env, functions, stack)
                            }));
                        }
                    }
                }
            }
            expression(callee, generator_names, functions, env, stack, facts);
            for argument in arguments {
                expression(argument, generator_names, functions, env, stack, facts);
            }
            return;
        }
        walk_expression_children(value, |child| {
            expression(child, generator_names, functions, env, stack, facts)
        });
    }

    walk_statement_expressions(statement, |value| {
        expression(value, generator_names, functions, env, stack, facts)
    });
}

fn generator_reference_escapes(program: &Program, source: &str) -> bool {
    fn expression(value: &Expression, source: &str) -> bool {
        match &value.kind {
            ExpressionKind::Global(name) => name == source,
            ExpressionKind::Call { callee, arguments } => {
                let callee_escapes = !matches!(&callee.kind, ExpressionKind::Global(name) if name == source)
                    && expression(callee, source);
                callee_escapes || arguments.iter().any(|value| expression(value, source))
            }
            ExpressionKind::Member { object, property } => {
                expression(object, source)
                    || matches!(
                        property,
                        MemberProperty::Computed(value) if expression(value, source)
                    )
            }
            ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
                ObjectEntry::Property(property) => expression(&property.value, source),
                ObjectEntry::Spread(value) => expression(value, source),
                ObjectEntry::Accessor { get, set, .. } => {
                    get.as_ref().is_some_and(|value| expression(value, source))
                        || set.as_ref().is_some_and(|value| expression(value, source))
                }
            }),
            ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
                ecmora_hir::ArrayElement::Expression(value)
                | ecmora_hir::ArrayElement::Spread(value) => expression(value, source),
                ecmora_hir::ArrayElement::Hole => false,
            }),
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => {
                expression(test, source)
                    || expression(consequent, source)
                    || expression(alternate, source)
            }
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expression(argument, source)
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                expression(left, source) || expression(right, source)
            }
            ExpressionKind::Assignment { target, value, .. } => {
                let target_escape = match target {
                    AssignmentTarget::Identifier(_) => false,
                    AssignmentTarget::Member { object, property } => {
                        expression(object, source)
                            || matches!(
                                property,
                                MemberProperty::Computed(value) if expression(value, source)
                            )
                    }
                };
                target_escape || expression(value, source)
            }
            ExpressionKind::Update { target, .. } => match target {
                AssignmentTarget::Identifier(_) => false,
                AssignmentTarget::Member { object, property } => {
                    expression(object, source)
                        || matches!(
                            property,
                            MemberProperty::Computed(value) if expression(value, source)
                        )
                }
            },
            ExpressionKind::New { callee, arguments } => {
                expression(callee, source)
                    || arguments.iter().any(|value| expression(value, source))
            }
            ExpressionKind::Function(function) => statements(&function.body, source),
            ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This => false,
        }
    }

    fn statement(value: &Statement, source: &str) -> bool {
        match &value.kind {
            StatementKind::Expression(value) | StatementKind::Throw(value) => {
                expression(value, source)
            }
            StatementKind::VariableDeclaration { declarations, .. } => declarations
                .iter()
                .filter_map(|declaration| declaration.init.as_ref())
                .any(|value| expression(value, source)),
            StatementKind::Block(body) => statements(body, source),
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                expression(test, source)
                    || statement(consequent, source)
                    || alternate
                        .as_deref()
                        .is_some_and(|alternate| statement(alternate, source))
            }
            StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
                expression(test, source) || statement(body, source)
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                init.as_ref().is_some_and(|init| match init {
                    ForInit::Expression(value) => expression(value, source),
                    ForInit::VariableDeclaration { declarations, .. } => declarations
                        .iter()
                        .filter_map(|declaration| declaration.init.as_ref())
                        .any(|value| expression(value, source)),
                }) || test.as_ref().is_some_and(|value| expression(value, source))
                    || update
                        .as_ref()
                        .is_some_and(|value| expression(value, source))
                    || statement(body, source)
            }
            StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
                expression(right, source) || statement(body, source)
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                expression(discriminant, source)
                    || cases.iter().any(|case| {
                        case.test
                            .as_ref()
                            .is_some_and(|value| expression(value, source))
                            || statements(&case.consequent, source)
                    })
            }
            StatementKind::Labeled { body, .. } => statement(body, source),
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                statement(block, source)
                    || handler
                        .as_ref()
                        .is_some_and(|handler| statement(&handler.body, source))
                    || finalizer
                        .as_deref()
                        .is_some_and(|finalizer| statement(finalizer, source))
            }
            StatementKind::FunctionDeclaration(function) => {
                if function.name.as_deref() == Some(source) {
                    false
                } else {
                    statements(&function.body, source)
                }
            }
            StatementKind::Return(value) => value
                .as_ref()
                .is_some_and(|value| expression(value, source)),
            StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => false,
        }
    }

    fn statements(values: &[Statement], source: &str) -> bool {
        values.iter().any(|value| statement(value, source))
    }

    statements(&program.statements, source)
}

fn collect_generator_wrappers(
    functions: &HashMap<String, Function>,
    generator_names: &HashSet<String>,
) -> HashMap<String, String> {
    let mut wrappers = HashMap::new();
    loop {
        let mut changed = false;
        for (name, function) in functions {
            if generator_names.contains(name) || wrappers.contains_key(name) {
                continue;
            }
            let [
                Statement {
                    kind:
                        StatementKind::Return(Some(Expression {
                            kind: ExpressionKind::Call { callee, .. },
                            ..
                        })),
                    ..
                },
            ] = function.body.as_slice()
            else {
                continue;
            };
            let ExpressionKind::Global(target) = &callee.kind else {
                continue;
            };
            let source = if generator_names.contains(target) {
                Some(target.clone())
            } else {
                wrappers.get(target).cloned()
            };
            if let Some(source) = source {
                wrappers.insert(name.clone(), source);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    wrappers
}

fn instance_source(
    expression: &Expression,
    instances: &HashMap<String, String>,
    generator_names: &HashSet<String>,
    wrappers: &HashMap<String, String>,
) -> Option<String> {
    match &expression.kind {
        ExpressionKind::Global(name) => instances.get(name).cloned(),
        ExpressionKind::Call { callee, .. } => {
            let ExpressionKind::Global(name) = &callee.kind else {
                return None;
            };
            if generator_names.contains(name) {
                Some(name.clone())
            } else {
                wrappers.get(name).cloned()
            }
        }
        _ => None,
    }
}

fn scan_protocol_statement(
    statement: &Statement,
    functions: &HashMap<String, Function>,
    generator_names: &HashSet<String>,
    wrappers: &HashMap<String, String>,
    instances: &mut HashMap<String, String>,
    throw_facts: &mut HashMap<String, SeedFact>,
    return_facts: &mut HashMap<String, SeedFact>,
) {
    fn scan_expression(
        value: &Expression,
        functions: &HashMap<String, Function>,
        instances: &HashMap<String, String>,
        throw_facts: &mut HashMap<String, SeedFact>,
        return_facts: &mut HashMap<String, SeedFact>,
    ) {
        if let ExpressionKind::Call { callee, arguments } = &value.kind {
            if let ExpressionKind::Member {
                object,
                property: MemberProperty::Static(method),
            } = &callee.kind
            {
                if let ExpressionKind::Global(instance) = &object.kind {
                    if let Some(source) = instances.get(instance) {
                        let env = HashMap::new();
                        let mut stack = HashSet::new();
                        let value = arguments.first().and_then(|argument| {
                            infer_seed_expression(argument, &env, functions, &mut stack)
                        });
                        match method.as_str() {
                            "throw" => {
                                if let Some(fact) = throw_facts.get_mut(source) {
                                    fact.observe(value);
                                }
                            }
                            "return" => {
                                if let Some(fact) = return_facts.get_mut(source) {
                                    fact.observe(value);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        walk_expression_children(value, |child| {
            scan_expression(child, functions, instances, throw_facts, return_facts)
        });
    }

    match &statement.kind {
        StatementKind::VariableDeclaration { declarations, .. } => {
            for declaration in declarations {
                if let Some(initializer) = &declaration.init {
                    scan_expression(initializer, functions, instances, throw_facts, return_facts);
                    if let Some(source) =
                        instance_source(initializer, instances, generator_names, wrappers)
                    {
                        instances.insert(declaration.name.clone(), source);
                    } else {
                        instances.remove(&declaration.name);
                    }
                }
            }
        }
        StatementKind::Expression(expression) => {
            scan_expression(expression, functions, instances, throw_facts, return_facts);
            if let ExpressionKind::Assignment {
                target: AssignmentTarget::Identifier(name),
                operator: AssignmentOperator::Assign,
                value,
            } = &expression.kind
            {
                if let Some(source) = instance_source(value, instances, generator_names, wrappers) {
                    instances.insert(name.clone(), source);
                } else {
                    instances.remove(name);
                }
            }
        }
        StatementKind::Block(body) => {
            for statement in body {
                scan_protocol_statement(
                    statement,
                    functions,
                    generator_names,
                    wrappers,
                    instances,
                    throw_facts,
                    return_facts,
                );
            }
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            scan_expression(test, functions, instances, throw_facts, return_facts);
            let before = instances.clone();
            let mut left = before.clone();
            scan_protocol_statement(
                consequent,
                functions,
                generator_names,
                wrappers,
                &mut left,
                throw_facts,
                return_facts,
            );
            let mut right = before.clone();
            if let Some(alternate) = alternate {
                scan_protocol_statement(
                    alternate,
                    functions,
                    generator_names,
                    wrappers,
                    &mut right,
                    throw_facts,
                    return_facts,
                );
            }
            instances.clear();
            for (name, source) in left {
                if right.get(&name) == Some(&source) {
                    instances.insert(name, source);
                }
            }
        }
        _ => {
            walk_statement_expressions(statement, |value| {
                scan_expression(value, functions, instances, throw_facts, return_facts)
            });
        }
    }
}

fn collect_local_slot_seed_facts(
    statements: &[Statement],
    env: &mut HashMap<String, SeedType>,
    functions: &HashMap<String, Function>,
    facts: &mut HashMap<String, SeedFact>,
) {
    fn merge_env(
        target: &mut HashMap<String, SeedType>,
        left: &HashMap<String, SeedType>,
        right: &HashMap<String, SeedType>,
    ) {
        let names = target.keys().cloned().collect::<Vec<_>>();
        for name in names {
            match (left.get(&name), right.get(&name)) {
                (Some(left), Some(right)) if left == right => {
                    target.insert(name, *left);
                }
                _ => {
                    target.remove(&name);
                }
            }
        }
    }

    for statement in statements {
        match &statement.kind {
            StatementKind::VariableDeclaration { kind, declarations } => {
                for declaration in declarations {
                    // `var` is observable as undefined before its initializer.
                    // A typed dummy would change JS semantics, so poison it.
                    if *kind == VariableKind::Var {
                        facts
                            .entry(declaration.name.clone())
                            .or_default()
                            .observe(None);
                        env.remove(&declaration.name);
                        continue;
                    }
                    let mut stack = HashSet::new();
                    let seed = declaration.init.as_ref().and_then(|initializer| {
                        infer_seed_expression(initializer, env, functions, &mut stack)
                    });
                    facts
                        .entry(declaration.name.clone())
                        .or_default()
                        .observe(seed);
                    if let Some(seed) = seed {
                        env.insert(declaration.name.clone(), seed);
                    } else {
                        env.remove(&declaration.name);
                    }
                }
            }
            StatementKind::Block(body) => {
                let mut nested = env.clone();
                collect_local_slot_seed_facts(body, &mut nested, functions, facts);
            }
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                let before = env.clone();
                let mut left = before.clone();
                collect_local_slot_seed_facts(
                    std::slice::from_ref(consequent.as_ref()),
                    &mut left,
                    functions,
                    facts,
                );
                let mut right = before.clone();
                if let Some(alternate) = alternate {
                    collect_local_slot_seed_facts(
                        std::slice::from_ref(alternate.as_ref()),
                        &mut right,
                        functions,
                        facts,
                    );
                }
                merge_env(env, &left, &right);
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Labeled { body, .. } => {
                let mut nested = env.clone();
                collect_local_slot_seed_facts(
                    std::slice::from_ref(body.as_ref()),
                    &mut nested,
                    functions,
                    facts,
                );
            }
            StatementKind::For { init, body, .. } => {
                let mut nested = env.clone();
                if let Some(ForInit::VariableDeclaration { kind, declarations }) = init {
                    let synthetic = Statement {
                        kind: StatementKind::VariableDeclaration {
                            kind: *kind,
                            declarations: declarations.clone(),
                        },
                        span: body.span,
                    };
                    collect_local_slot_seed_facts(
                        std::slice::from_ref(&synthetic),
                        &mut nested,
                        functions,
                        facts,
                    );
                }
                collect_local_slot_seed_facts(
                    std::slice::from_ref(body.as_ref()),
                    &mut nested,
                    functions,
                    facts,
                );
            }
            StatementKind::ForIn {
                name, kind, body, ..
            }
            | StatementKind::ForOf {
                name, kind, body, ..
            } => {
                // Iterator-produced bindings need iterator element typing, not
                // a guessed scalar seed.
                if *kind == VariableKind::Var {
                    facts.entry(name.clone()).or_default().observe(None);
                } else {
                    facts.entry(name.clone()).or_default().observe(None);
                }
                let mut nested = env.clone();
                nested.remove(name);
                collect_local_slot_seed_facts(
                    std::slice::from_ref(body.as_ref()),
                    &mut nested,
                    functions,
                    facts,
                );
            }
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    let mut nested = env.clone();
                    collect_local_slot_seed_facts(&case.consequent, &mut nested, functions, facts);
                }
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                let mut try_env = env.clone();
                collect_local_slot_seed_facts(
                    std::slice::from_ref(block.as_ref()),
                    &mut try_env,
                    functions,
                    facts,
                );
                if let Some(handler) = handler {
                    let mut catch_env = env.clone();
                    if let Some(parameter) = &handler.parameter {
                        catch_env.remove(parameter);
                    }
                    collect_local_slot_seed_facts(
                        std::slice::from_ref(handler.body.as_ref()),
                        &mut catch_env,
                        functions,
                        facts,
                    );
                }
                if let Some(finalizer) = finalizer {
                    let mut final_env = env.clone();
                    collect_local_slot_seed_facts(
                        std::slice::from_ref(finalizer.as_ref()),
                        &mut final_env,
                        functions,
                        facts,
                    );
                }
            }
            StatementKind::Expression(_)
            | StatementKind::Return(_)
            | StatementKind::Throw(_)
            | StatementKind::Break(_)
            | StatementKind::Continue(_)
            | StatementKind::FunctionDeclaration(_)
            | StatementKind::Empty
            | StatementKind::Debugger => {}
        }
    }
}

fn observe_generator_returns(
    statements: &[Statement],
    env: &HashMap<String, SeedType>,
    functions: &HashMap<String, Function>,
    stack: &mut HashSet<String>,
    fact: &mut SeedFact,
) {
    for statement in statements {
        match &statement.kind {
            StatementKind::Return(value) => {
                fact.observe(
                    value
                        .as_ref()
                        .and_then(|value| infer_seed_expression(value, env, functions, stack)),
                );
            }
            StatementKind::Block(body) => {
                observe_generator_returns(body, env, functions, stack, fact)
            }
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                observe_generator_returns(
                    std::slice::from_ref(consequent.as_ref()),
                    env,
                    functions,
                    stack,
                    fact,
                );
                if let Some(alternate) = alternate {
                    observe_generator_returns(
                        std::slice::from_ref(alternate.as_ref()),
                        env,
                        functions,
                        stack,
                        fact,
                    );
                }
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::For { body, .. }
            | StatementKind::ForIn { body, .. }
            | StatementKind::ForOf { body, .. }
            | StatementKind::Labeled { body, .. } => observe_generator_returns(
                std::slice::from_ref(body.as_ref()),
                env,
                functions,
                stack,
                fact,
            ),
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    observe_generator_returns(&case.consequent, env, functions, stack, fact);
                }
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                observe_generator_returns(
                    std::slice::from_ref(block.as_ref()),
                    env,
                    functions,
                    stack,
                    fact,
                );
                if let Some(handler) = handler {
                    observe_generator_returns(
                        std::slice::from_ref(handler.body.as_ref()),
                        env,
                        functions,
                        stack,
                        fact,
                    );
                }
                if let Some(finalizer) = finalizer {
                    observe_generator_returns(
                        std::slice::from_ref(finalizer.as_ref()),
                        env,
                        functions,
                        stack,
                        fact,
                    );
                }
            }
            StatementKind::FunctionDeclaration(_)
            | StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Expression(_)
            | StatementKind::VariableDeclaration { .. }
            | StatementKind::Throw(_)
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
        }
    }
}

fn collect_catch_seed_names(
    statements: &[Statement],
    seed: SeedType,
    output: &mut HashMap<String, SeedType>,
) {
    for statement in statements {
        match &statement.kind {
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                if let Some(handler) = handler {
                    if let Some(parameter) = &handler.parameter {
                        output.insert(parameter.clone(), seed);
                    }
                    collect_catch_seed_names(
                        std::slice::from_ref(handler.body.as_ref()),
                        seed,
                        output,
                    );
                }
                collect_catch_seed_names(std::slice::from_ref(block.as_ref()), seed, output);
                if let Some(finalizer) = finalizer {
                    collect_catch_seed_names(
                        std::slice::from_ref(finalizer.as_ref()),
                        seed,
                        output,
                    );
                }
            }
            StatementKind::Block(body) => collect_catch_seed_names(body, seed, output),
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                collect_catch_seed_names(std::slice::from_ref(consequent.as_ref()), seed, output);
                if let Some(alternate) = alternate {
                    collect_catch_seed_names(
                        std::slice::from_ref(alternate.as_ref()),
                        seed,
                        output,
                    );
                }
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::For { body, .. }
            | StatementKind::ForIn { body, .. }
            | StatementKind::ForOf { body, .. }
            | StatementKind::Labeled { body, .. } => {
                collect_catch_seed_names(std::slice::from_ref(body.as_ref()), seed, output)
            }
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    collect_catch_seed_names(&case.consequent, seed, output);
                }
            }
            _ => {}
        }
    }
}

fn generator_protocol_throw_only(
    function: &Function,
    functions: &HashMap<String, Function>,
) -> bool {
    let mut stack = HashSet::new();
    !statements_may_throw(&function.body, functions, &mut stack)
}

fn statements_may_throw(
    statements: &[Statement],
    functions: &HashMap<String, Function>,
    stack: &mut HashSet<String>,
) -> bool {
    statements.iter().any(|statement| match &statement.kind {
        StatementKind::Throw(_) => true,
        StatementKind::Expression(value) | StatementKind::Return(Some(value)) => {
            expression_may_throw(value, functions, stack)
        }
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|declaration| declaration.init.as_ref())
            .any(|value| expression_may_throw(value, functions, stack)),
        StatementKind::Block(body) => statements_may_throw(body, functions, stack),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression_may_throw(test, functions, stack)
                || statements_may_throw(std::slice::from_ref(consequent.as_ref()), functions, stack)
                || alternate.as_deref().is_some_and(|alternate| {
                    statements_may_throw(std::slice::from_ref(alternate), functions, stack)
                })
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression_may_throw(test, functions, stack)
                || statements_may_throw(std::slice::from_ref(body.as_ref()), functions, stack)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => expression_may_throw(value, functions, stack),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|declaration| declaration.init.as_ref())
                    .any(|value| expression_may_throw(value, functions, stack)),
            }) || test
                .as_ref()
                .is_some_and(|value| expression_may_throw(value, functions, stack))
                || update
                    .as_ref()
                    .is_some_and(|value| expression_may_throw(value, functions, stack))
                || statements_may_throw(std::slice::from_ref(body.as_ref()), functions, stack)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expression_may_throw(right, functions, stack)
                || statements_may_throw(std::slice::from_ref(body.as_ref()), functions, stack)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expression_may_throw(discriminant, functions, stack)
                || cases.iter().any(|case| {
                    case.test
                        .as_ref()
                        .is_some_and(|value| expression_may_throw(value, functions, stack))
                        || statements_may_throw(&case.consequent, functions, stack)
                })
        }
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statements_may_throw(std::slice::from_ref(block.as_ref()), functions, stack)
                || handler.as_ref().is_some_and(|handler| {
                    statements_may_throw(
                        std::slice::from_ref(handler.body.as_ref()),
                        functions,
                        stack,
                    )
                })
                || finalizer.as_deref().is_some_and(|finalizer| {
                    statements_may_throw(std::slice::from_ref(finalizer), functions, stack)
                })
        }
        StatementKind::Labeled { body, .. } => {
            statements_may_throw(std::slice::from_ref(body.as_ref()), functions, stack)
        }
        StatementKind::FunctionDeclaration(_)
        | StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Return(None)
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    })
}

fn expression_may_throw(
    expression: &Expression,
    functions: &HashMap<String, Function>,
    stack: &mut HashSet<String>,
) -> bool {
    match &expression.kind {
        ExpressionKind::Call { callee, arguments } => {
            if matches!(&callee.kind, ExpressionKind::Global(name) if name == "@yield") {
                return arguments
                    .iter()
                    .any(|value| expression_may_throw(value, functions, stack));
            }
            let ExpressionKind::Global(name) = &callee.kind else {
                return true;
            };
            let Some(function) = functions.get(name) else {
                return true;
            };
            if function.generator || function.r#async || !stack.insert(name.clone()) {
                return true;
            }
            let body_throws = statements_may_throw(&function.body, functions, stack);
            stack.remove(name);
            body_throws
                || arguments
                    .iter()
                    .any(|value| expression_may_throw(value, functions, stack))
        }
        ExpressionKind::Member { .. } | ExpressionKind::New { .. } | ExpressionKind::Await(_) => {
            true
        }
        ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
            ObjectEntry::Property(property) => {
                expression_may_throw(&property.value, functions, stack)
            }
            ObjectEntry::Spread(_) | ObjectEntry::Accessor { .. } => true,
        }),
        ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
            ecmora_hir::ArrayElement::Expression(value) => {
                expression_may_throw(value, functions, stack)
            }
            ecmora_hir::ArrayElement::Spread(_) => true,
            ecmora_hir::ArrayElement::Hole => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            expression_may_throw(test, functions, stack)
                || expression_may_throw(consequent, functions, stack)
                || expression_may_throw(alternate, functions, stack)
        }
        ExpressionKind::Unary { argument, .. } => expression_may_throw(argument, functions, stack),
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            expression_may_throw(left, functions, stack)
                || expression_may_throw(right, functions, stack)
        }
        ExpressionKind::Assignment { value, .. } => expression_may_throw(value, functions, stack),
        ExpressionKind::Update { .. }
        | ExpressionKind::Function(_)
        | ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This
        | ExpressionKind::Global(_) => false,
    }
}

fn walk_statement_expressions(statement: &Statement, mut visit: impl FnMut(&Expression)) {
    fn visit_statement(node: &Statement, visit: &mut dyn FnMut(&Expression)) {
        match &node.kind {
            StatementKind::Expression(value) | StatementKind::Throw(value) => visit(value),
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    if let Some(value) = &declaration.init {
                        visit(value);
                    }
                }
            }
            StatementKind::Block(body) => {
                for statement_value in body {
                    visit_statement(statement_value, visit);
                }
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                visit(test);
                visit_statement(consequent, visit);
                if let Some(alternate) = alternate {
                    visit_statement(alternate, visit);
                }
            }
            StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
                visit(test);
                visit_statement(body, visit);
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                if let Some(init) = init {
                    match init {
                        ForInit::Expression(value) => visit(value),
                        ForInit::VariableDeclaration { declarations, .. } => {
                            for declaration in declarations {
                                if let Some(value) = &declaration.init {
                                    visit(value);
                                }
                            }
                        }
                    }
                }
                if let Some(test) = test {
                    visit(test);
                }
                if let Some(update) = update {
                    visit(update);
                }
                visit_statement(body, visit);
            }
            StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
                visit(right);
                visit_statement(body, visit);
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                visit(discriminant);
                for case in cases {
                    if let Some(test) = &case.test {
                        visit(test);
                    }
                    for statement_value in &case.consequent {
                        visit_statement(statement_value, visit);
                    }
                }
            }
            StatementKind::Labeled { body, .. } => visit_statement(body, visit),
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                visit_statement(block, visit);
                if let Some(handler) = handler {
                    visit_statement(&handler.body, visit);
                }
                if let Some(finalizer) = finalizer {
                    visit_statement(finalizer, visit);
                }
            }
            StatementKind::FunctionDeclaration(_) => {}
            StatementKind::Return(value) => {
                if let Some(value) = value {
                    visit(value);
                }
            }
            StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
        }
    }
    visit_statement(statement, &mut visit);
}

fn walk_expression_children(expression: &Expression, mut visit: impl FnMut(&Expression)) {
    match &expression.kind {
        ExpressionKind::Member { object, property } => {
            visit(object);
            if let MemberProperty::Computed(value) = property {
                visit(value);
            }
        }
        ExpressionKind::Object(entries) => {
            for entry in entries {
                match entry {
                    ObjectEntry::Property(property) => visit(&property.value),
                    ObjectEntry::Spread(value) => visit(value),
                    ObjectEntry::Accessor { get, set, .. } => {
                        if let Some(value) = get {
                            visit(value);
                        }
                        if let Some(value) = set {
                            visit(value);
                        }
                    }
                }
            }
        }
        ExpressionKind::Array(elements) => {
            for element in elements {
                match element {
                    ecmora_hir::ArrayElement::Expression(value)
                    | ecmora_hir::ArrayElement::Spread(value) => visit(value),
                    ecmora_hir::ArrayElement::Hole => {}
                }
            }
        }
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            visit(test);
            visit(consequent);
            visit(alternate);
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => visit(argument),
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            visit(left);
            visit(right);
        }
        ExpressionKind::Assignment { target, value, .. } => {
            if let AssignmentTarget::Member { object, property } = target {
                visit(object);
                if let MemberProperty::Computed(value) = property {
                    visit(value);
                }
            }
            visit(value);
        }
        ExpressionKind::Update { target, .. } => {
            if let AssignmentTarget::Member { object, property } = target {
                visit(object);
                if let MemberProperty::Computed(value) = property {
                    visit(value);
                }
            }
        }
        ExpressionKind::Call { callee, arguments } | ExpressionKind::New { callee, arguments } => {
            visit(callee);
            for argument in arguments {
                visit(argument);
            }
        }
        ExpressionKind::Function(_)
        | ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This
        | ExpressionKind::Global(_) => {}
    }
}

#[derive(Clone)]
struct State {
    id: StateId,
    body: Vec<Statement>,
    term: Term,
    throw_target: Option<StateId>,
}

#[derive(Clone)]
enum Term {
    Goto(StateId),
    Branch {
        test: Expression,
        yes: StateId,
        no: StateId,
    },
    Yield {
        value: Expression,
        resume: StateId,
    },
    Resume {
        normal: StateId,
        throw_target: StateId,
        return_target: StateId,
        assign: Option<AssignmentTarget>,
    },
    Stop,
    Rethrow,
}

#[derive(Clone)]
struct Control {
    label: Option<String>,
    break_target: StateId,
    continue_target: Option<StateId>,
}

#[derive(Clone)]
struct Flow {
    return_target: StateId,
    throw_target: StateId,
    controls: Vec<Control>,
}

impl Flow {
    fn break_target(&self, label: Option<&str>) -> Result<StateId> {
        if let Some(label) = label {
            return self
                .controls
                .iter()
                .rev()
                .find(|c| c.label.as_deref() == Some(label))
                .map(|c| c.break_target)
                .ok_or_else(|| anyhow::anyhow!("unknown break label `{label}`"));
        }
        self.controls
            .iter()
            .rev()
            .next()
            .map(|c| c.break_target)
            .ok_or_else(|| anyhow::anyhow!("break outside control target"))
    }
    fn continue_target(&self, label: Option<&str>) -> Result<StateId> {
        if let Some(label) = label {
            return self
                .controls
                .iter()
                .rev()
                .find(|c| c.label.as_deref() == Some(label))
                .and_then(|c| c.continue_target)
                .ok_or_else(|| anyhow::anyhow!("unknown continue label `{label}`"));
        }
        self.controls
            .iter()
            .rev()
            .find_map(|c| c.continue_target)
            .ok_or_else(|| anyhow::anyhow!("continue outside iteration"))
    }
}

pub(super) fn requires_general(program: &Program) -> bool {
    let generator_names = program
        .statements
        .iter()
        .filter_map(|statement| match &statement.kind {
            StatementKind::FunctionDeclaration(function) if function.generator => {
                function.name.clone()
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    if generator_names.is_empty() {
        return false;
    }
    let has_yield_star = program.statements.iter().any(|statement| {
        matches!(
            &statement.kind,
            StatementKind::FunctionDeclaration(function)
                if function.generator
                    && function.body.iter().any(statement_contains_yield_star)
        )
    });

    // Once a program does not depend on the older yield* fast path, use the
    // resumable state machine for *all* generator objects. This deliberately
    // includes plain local aliases: identity is a static frame object, not a
    // compile-time cursor token, so alias/pass/return flows stay valid.
    if !has_yield_star {
        return true;
    }

    program
        .statements
        .iter()
        .any(|statement| match &statement.kind {
            StatementKind::FunctionDeclaration(function) if function.generator => {
                function.body.iter().any(yield_requires_cfg)
            }
            StatementKind::FunctionDeclaration(function) => {
                function.body.iter().any(protocol_call)
                    || function
                        .body
                        .iter()
                        .any(|statement| statement_calls_generator(statement, &generator_names))
            }
            _ => protocol_under_control(statement, 0),
        })
}

pub(super) fn lower(program: &Program) -> Result<Program> {
    let templates = collect_templates(&program.statements)?;
    if templates.is_empty() {
        return Ok(program.clone());
    }
    if templates.values().any(|t| t.function.r#async) {
        bail!("async generator needs AsyncGenerator request-queue lowering")
    }

    let factories = templates
        .iter()
        .map(|(name, t)| (name.clone(), t.factory.clone()))
        .collect::<HashMap<_, _>>();
    let seed_oracle = SeedOracle::build(program, &templates);

    let mut machines = HashMap::new();
    for template in templates.values() {
        if template
            .function
            .body
            .iter()
            .any(statement_contains_yield_star)
        {
            bail!(
                "yield* mixed with general CFG currently stays on the static generator path; dynamic yield* needs delegate-state composition"
            )
        }
        let machine = Builder::build(template, &factories, &seed_oracle)?;
        machines.insert(template.source.clone(), machine);
    }

    let mut out = Vec::new();
    for statement in &program.statements {
        match &statement.kind {
            StatementKind::FunctionDeclaration(function) if function.generator => {
                let name = function
                    .name
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("generator missing name"))?;
                let machine = &machines[name];
                out.push(render_resume(machine)?);
                out.push(render_factory(machine)?);
            }
            _ => out.push(rewrite_refs_statement(statement, &factories)?),
        }
    }
    validate_erased(&out)?;
    let mut result = program.clone();
    result.statements = out;
    Ok(result)
}

fn collect_templates(statements: &[Statement]) -> Result<HashMap<String, Template>> {
    let mut result = HashMap::new();
    for statement in statements {
        let StatementKind::FunctionDeclaration(function) = &statement.kind else {
            continue;
        };
        if !function.generator {
            continue;
        }
        let source = function
            .name
            .clone()
            .ok_or_else(|| anyhow::anyhow!("generator missing name"))?;
        let safe = sanitize(&source);
        let template = Template {
            source: source.clone(),
            factory: format!("@gen_factory_{safe}"),
            resume: format!("@gen_resume_{safe}"),
            function: function.clone(),
        };
        if result.insert(source.clone(), template).is_some() {
            bail!("duplicate generator `{source}`")
        }
    }
    Ok(result)
}

#[derive(Clone)]
struct Machine {
    factory: String,
    resume: String,
    entry: StateId,
    states: Vec<State>,
    slots: HashMap<String, Slot>,
    order: Vec<String>,
    parameters: Vec<String>,
    span: Span,

    exception_seed: Option<SeedType>,

    return_seed: Option<SeedType>,
}

struct Builder<'a> {
    template: &'a Template,
    factories: &'a HashMap<String, String>,
    states: Vec<Option<State>>,
    slots: HashMap<String, Slot>,
    order: Vec<String>,
    temp: u32,
    finish_undefined: StateId,
    finish_return: StateId,
    unhandled_throw: StateId,

    oracle: &'a SeedOracle,

    seed_env: HashMap<String, SeedType>,
}

impl<'a> Builder<'a> {
    fn build(
        template: &'a Template,
        factories: &'a HashMap<String, String>,
        oracle: &'a SeedOracle,
    ) -> Result<Machine> {
        let span = function_span(&template.function);
        let mut slots = HashMap::new();
        let mut order = Vec::new();
        for parameter in &template.function.parameters {
            if parameter.starts_with("@rest:") {
                bail!("generator rest parameter needs argv tuple lowering")
            }
            add_slot(&mut slots, &mut order, parameter, VariableKind::Let, true);
        }
        collect_slots(&template.function.body, &mut slots, &mut order)?;
        let local_seeds = oracle.local_slot_seeds(template);
        for (name, seed) in &local_seeds {
            if let Some(slot) = slots.get_mut(name) {
                slot.seed = Some(*seed);
            }
        }
        let mut seed_env = oracle.parameter_env(&template.source, &template.function);
        seed_env.extend(local_seeds.iter().map(|(name, seed)| (name.clone(), *seed)));

        let mut b = Self {
            oracle,
            seed_env,
            template,
            factories,
            states: Vec::new(),
            slots,
            order,
            temp: 0,
            finish_undefined: 0,
            finish_return: 0,
            unhandled_throw: 0,
        };
        b.finish_undefined = b.push(
            vec![
                frame_set(DONE, bool_expr(true, span)),
                frame_set(OUT, undefined(span)),
                frame_set(OUT_DONE, bool_expr(true, span)),
            ],
            Term::Stop,
            None,
        );
        b.finish_return = b.push(
            vec![
                frame_set(DONE, bool_expr(true, span)),
                frame_set(OUT, frame_get(RETURN_VALUE, span)),
                frame_set(OUT_DONE, bool_expr(true, span)),
            ],
            Term::Stop,
            None,
        );
        b.unhandled_throw = b.push(
            vec![frame_set(DONE, bool_expr(true, span))],
            Term::Rethrow,
            None,
        );

        let flow = Flow {
            return_target: b.finish_return,
            throw_target: b.unhandled_throw,
            controls: Vec::new(),
        };
        let entry = b.compile_statements(&template.function.body, b.finish_undefined, &flow)?;
        let states = b
            .states
            .into_iter()
            .enumerate()
            .map(|(i, s)| s.ok_or_else(|| anyhow::anyhow!("unfilled generator state {i}")))
            .collect::<Result<Vec<_>>>()?;
        Ok(Machine {
            exception_seed: oracle.exception_seed(template),
            return_seed: oracle.return_seed(template, &local_seeds),
            factory: template.factory.clone(),
            resume: template.resume.clone(),
            entry,
            states,
            slots: b.slots,
            order: b.order,
            parameters: template.function.parameters.clone(),
            span,
        })
    }

    fn reserve(&mut self) -> StateId {
        let id = self.states.len() as StateId;
        self.states.push(None);
        id
    }
    fn fill(
        &mut self,
        id: StateId,
        body: Vec<Statement>,
        term: Term,
        throw_target: Option<StateId>,
    ) {
        self.states[id as usize] = Some(State {
            id,
            body,
            term,
            throw_target,
        });
    }
    fn push(&mut self, body: Vec<Statement>, term: Term, throw_target: Option<StateId>) -> StateId {
        let id = self.reserve();
        self.fill(id, body, term, throw_target);
        id
    }
    fn temp_slot(&mut self, hint: &str, seed: Option<SeedType>) -> String {
        let name = format!("@gen_tmp_{}_{}", sanitize(hint), self.temp);
        self.temp += 1;
        add_slot(
            &mut self.slots,
            &mut self.order,
            &name,
            VariableKind::Let,
            false,
        );
        if let Some(slot) = self.slots.get_mut(&name) {
            slot.seed = seed;
        }
        if let Some(seed) = seed {
            self.seed_env.insert(name.clone(), seed);
        }
        name
    }
    fn expr(&self, value: &Expression) -> Result<Expression> {
        rewrite_machine_expr(value, &self.slots, self.factories)
    }
    fn target(&self, target: &AssignmentTarget) -> Result<AssignmentTarget> {
        rewrite_machine_target(target, &self.slots, self.factories)
    }

    fn compile_statements(
        &mut self,
        statements: &[Statement],
        cont: StateId,
        flow: &Flow,
    ) -> Result<StateId> {
        let mut next = cont;
        for statement in statements.iter().rev() {
            next = self.compile_statement(statement, next, flow)?;
        }
        Ok(next)
    }

    fn compile_statement(
        &mut self,
        statement: &Statement,
        cont: StateId,
        flow: &Flow,
    ) -> Result<StateId> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Empty | StatementKind::Debugger => Ok(self.push(
                vec![statement.clone()],
                Term::Goto(cont),
                Some(flow.throw_target),
            )),
            StatementKind::Expression(value) => {
                if let Some((yielded, delegate)) = yield_marker(value) {
                    if delegate {
                        bail!("yield* requiring general CFG needs delegate-state composition")
                    }
                    return self.compile_yield(yielded, None, cont, flow);
                }
                if let ExpressionKind::Assignment {
                    target,
                    operator: AssignmentOperator::Assign,
                    value,
                } = &value.kind
                {
                    if let Some((yielded, delegate)) = yield_marker(value) {
                        if delegate {
                            bail!("assignment from yield* needs delegate completion state")
                        }
                        return self.compile_yield(yielded, Some(self.target(target)?), cont, flow);
                    }
                }
                if contains_yield_expr(value) {
                    bail!(
                        "compound expression containing yield needs ANF split before resumable CFG"
                    )
                }
                Ok(self.push(
                    vec![expr_stmt(self.expr(value)?)],
                    Term::Goto(cont),
                    Some(flow.throw_target),
                ))
            }
            StatementKind::VariableDeclaration { declarations, .. } => {
                let mut next = cont;
                for declaration in declarations.iter().rev() {
                    let slot = self
                        .slots
                        .get(&declaration.name)
                        .ok_or_else(|| {
                            anyhow::anyhow!("missing generator slot `{}`", declaration.name)
                        })?
                        .clone();
                    if let Some(init) = &declaration.init {
                        if let Some((yielded, delegate)) = yield_marker(init) {
                            if delegate {
                                bail!("declaration from yield* needs delegate completion state")
                            }
                            let target = AssignmentTarget::Member {
                                object: Box::new(global(FRAME, span)),
                                property: MemberProperty::Static(slot.field.clone()),
                            };
                            next = self.compile_yield(yielded, Some(target), next, flow)?;
                        } else {
                            if contains_yield_expr(init) {
                                bail!(
                                    "compound declaration initializer containing yield needs ANF split"
                                )
                            }
                            next = self.push(
                                vec![frame_set(&slot.field, self.expr(init)?)],
                                Term::Goto(next),
                                Some(flow.throw_target),
                            );
                        }
                    }
                }
                Ok(next)
            }
            StatementKind::Block(body) => self.compile_statements(body, cont, flow),
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                let yes = self.compile_statement(consequent, cont, flow)?;
                let no = alternate
                    .as_deref()
                    .map(|alt| self.compile_statement(alt, cont, flow))
                    .transpose()?
                    .unwrap_or(cont);
                if contains_yield_expr(test) {
                    bail!("yield in if condition needs ANF test splitting")
                }
                Ok(self.push(
                    Vec::new(),
                    Term::Branch {
                        test: self.expr(test)?,
                        yes,
                        no,
                    },
                    Some(flow.throw_target),
                ))
            }
            StatementKind::While { test, body } => {
                if contains_yield_expr(test) {
                    bail!("yield in while condition needs ANF test splitting")
                }
                let test_state = self.reserve();
                let mut inner = flow.clone();
                inner.controls.push(Control {
                    label: None,
                    break_target: cont,
                    continue_target: Some(test_state),
                });
                let body_entry = self.compile_statement(body, test_state, &inner)?;
                self.fill(
                    test_state,
                    Vec::new(),
                    Term::Branch {
                        test: self.expr(test)?,
                        yes: body_entry,
                        no: cont,
                    },
                    Some(flow.throw_target),
                );
                Ok(test_state)
            }
            StatementKind::DoWhile { body, test } => {
                if contains_yield_expr(test) {
                    bail!("yield in do-while condition needs ANF test splitting")
                }
                let test_state = self.reserve();
                let mut inner = flow.clone();
                inner.controls.push(Control {
                    label: None,
                    break_target: cont,
                    continue_target: Some(test_state),
                });
                let body_entry = self.compile_statement(body, test_state, &inner)?;
                self.fill(
                    test_state,
                    Vec::new(),
                    Term::Branch {
                        test: self.expr(test)?,
                        yes: body_entry,
                        no: cont,
                    },
                    Some(flow.throw_target),
                );
                Ok(body_entry)
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                let test_state = self.reserve();
                let update_state = if let Some(update) = update {
                    if contains_yield_expr(update) {
                        bail!("yield in for update needs ANF split")
                    }
                    self.push(
                        vec![expr_stmt(self.expr(update)?)],
                        Term::Goto(test_state),
                        Some(flow.throw_target),
                    )
                } else {
                    test_state
                };
                let mut inner = flow.clone();
                inner.controls.push(Control {
                    label: None,
                    break_target: cont,
                    continue_target: Some(update_state),
                });
                let body_entry = self.compile_statement(body, update_state, &inner)?;
                let condition = if let Some(test) = test {
                    if contains_yield_expr(test) {
                        bail!("yield in for condition needs ANF split")
                    }
                    self.expr(test)?
                } else {
                    bool_expr(true, span)
                };
                self.fill(
                    test_state,
                    Vec::new(),
                    Term::Branch {
                        test: condition,
                        yes: body_entry,
                        no: cont,
                    },
                    Some(flow.throw_target),
                );
                match init {
                    None => Ok(test_state),
                    Some(ForInit::Expression(value)) => {
                        if contains_yield_expr(value) {
                            bail!("yield in for initializer needs ANF split")
                        }
                        Ok(self.push(
                            vec![expr_stmt(self.expr(value)?)],
                            Term::Goto(test_state),
                            Some(flow.throw_target),
                        ))
                    }
                    Some(ForInit::VariableDeclaration { kind, declarations }) => self
                        .compile_statement(
                            &Statement {
                                kind: StatementKind::VariableDeclaration {
                                    kind: *kind,
                                    declarations: declarations.clone(),
                                },
                                span,
                            },
                            test_state,
                            flow,
                        ),
                }
            }
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => {
                if statement_contains_yield(statement) {
                    bail!("yield in for-in needs enumerable-key iterator CFG lowering")
                }
                let slot = self
                    .slots
                    .get(name)
                    .ok_or_else(|| anyhow::anyhow!("missing for-in slot `{name}`"))?;
                let temporary = format!(
                    "@gen_forin_{}_{}_{}",
                    sanitize(&self.template.source),
                    sanitize(name),
                    state_tag(span)
                );
                let rewritten_body = rewrite_plain(body, &self.slots, self.factories)?;
                let body = block(
                    vec![
                        frame_set(&slot.field, global(&temporary, span)),
                        rewritten_body,
                    ],
                    span,
                );
                let loop_statement = Statement {
                    kind: StatementKind::ForIn {
                        name: temporary,
                        kind: *kind,
                        right: rewrite_machine_expr(right, &self.slots, self.factories)?,
                        body: Box::new(body),
                    },
                    span,
                };
                Ok(self.push(
                    vec![loop_statement],
                    Term::Goto(cont),
                    Some(flow.throw_target),
                ))
            }
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => {
                if statement_contains_yield(statement) {
                    bail!("yield in generic for-of needs native iterator-state lowering")
                }
                let slot = self
                    .slots
                    .get(name)
                    .ok_or_else(|| anyhow::anyhow!("missing for-of slot `{name}`"))?;
                let temporary = format!(
                    "@gen_forof_{}_{}_{}",
                    sanitize(&self.template.source),
                    sanitize(name),
                    state_tag(span)
                );
                let rewritten_body = rewrite_plain(body, &self.slots, self.factories)?;
                let body = block(
                    vec![
                        frame_set(&slot.field, global(&temporary, span)),
                        rewritten_body,
                    ],
                    span,
                );
                let loop_statement = Statement {
                    kind: StatementKind::ForOf {
                        name: temporary,
                        kind: *kind,
                        right: rewrite_machine_expr(right, &self.slots, self.factories)?,
                        body: Box::new(body),
                    },
                    span,
                };
                Ok(self.push(
                    vec![loop_statement],
                    Term::Goto(cont),
                    Some(flow.throw_target),
                ))
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => self.compile_switch(discriminant, cases, cont, flow, span),
            StatementKind::Labeled { label, body } => {
                let mut inner = flow.clone();
                inner.controls.push(Control {
                    label: Some(label.clone()),
                    break_target: cont,
                    continue_target: None,
                });
                self.compile_statement(body, cont, &inner)
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => self.compile_try(block, handler.as_ref(), finalizer.as_deref(), cont, flow),
            StatementKind::FunctionDeclaration(_) => {
                if statement_contains_yield(statement) {
                    bail!("nested generator yield ownership malformed")
                }
                Ok(self.push(
                    vec![rewrite_plain(statement, &self.slots, self.factories)?],
                    Term::Goto(cont),
                    Some(flow.throw_target),
                ))
            }
            StatementKind::Return(value) => {
                if let Some(value) = value {
                    if let Some((yielded, delegate)) = yield_marker(value) {
                        if delegate {
                            bail!("return yield* needs delegate completion value")
                        }
                        let temp = self.temp_slot("return", None);
                        let field = self.slots[&temp].field.clone();
                        let finish = self.push(
                            vec![frame_set(RETURN_VALUE, frame_get(&field, span))],
                            Term::Goto(flow.return_target),
                            Some(flow.throw_target),
                        );
                        let target = AssignmentTarget::Member {
                            object: Box::new(global(FRAME, span)),
                            property: MemberProperty::Static(field),
                        };
                        return self.compile_yield(yielded, Some(target), finish, flow);
                    }
                    if contains_yield_expr(value) {
                        bail!("compound generator return containing yield needs ANF split")
                    }
                    Ok(self.push(
                        vec![frame_set(RETURN_VALUE, self.expr(value)?)],
                        Term::Goto(flow.return_target),
                        Some(flow.throw_target),
                    ))
                } else {
                    Ok(self.push(
                        vec![frame_set(RETURN_VALUE, undefined(span))],
                        Term::Goto(flow.return_target),
                        Some(flow.throw_target),
                    ))
                }
            }
            StatementKind::Throw(value) => {
                if contains_yield_expr(value) {
                    bail!("yield in throw expression needs ANF split")
                }
                Ok(self.push(
                    vec![frame_set(EXCEPTION, self.expr(value)?)],
                    Term::Goto(flow.throw_target),
                    Some(flow.throw_target),
                ))
            }
            StatementKind::Break(label) => Ok(self.push(
                Vec::new(),
                Term::Goto(flow.break_target(label.as_deref())?),
                Some(flow.throw_target),
            )),
            StatementKind::Continue(label) => Ok(self.push(
                Vec::new(),
                Term::Goto(flow.continue_target(label.as_deref())?),
                Some(flow.throw_target),
            )),
        }
    }

    fn compile_yield(
        &mut self,
        yielded: Expression,
        assign: Option<AssignmentTarget>,
        cont: StateId,
        flow: &Flow,
    ) -> Result<StateId> {
        if contains_yield_expr(&yielded) {
            bail!("yield value contains nested yield")
        }
        let resume = self.push(
            Vec::new(),
            Term::Resume {
                normal: cont,
                throw_target: flow.throw_target,
                return_target: flow.return_target,
                assign,
            },
            Some(flow.throw_target),
        );
        Ok(self.push(
            Vec::new(),
            Term::Yield {
                value: self.expr(&yielded)?,
                resume,
            },
            Some(flow.throw_target),
        ))
    }

    fn compile_switch(
        &mut self,
        discriminant: &Expression,
        cases: &[SwitchCase],
        cont: StateId,
        flow: &Flow,
        span: Span,
    ) -> Result<StateId> {
        if contains_yield_expr(discriminant) {
            bail!("yield in switch discriminant needs ANF split")
        }
        let temp_seed =
            self.oracle
                .infer_generator_expression(self.template, &self.seed_env, discriminant);
        let temp = self.temp_slot("switch", temp_seed);
        let temp_field = self.slots[&temp].field.clone();

        let mut inner = flow.clone();
        inner.controls.push(Control {
            label: None,
            break_target: cont,
            continue_target: None,
        });

        let mut entries = vec![cont; cases.len()];
        let mut fallthrough = cont;
        for i in (0..cases.len()).rev() {
            let entry = self.compile_statements(&cases[i].consequent, fallthrough, &inner)?;
            entries[i] = entry;
            fallthrough = entry;
        }
        let default_target = cases
            .iter()
            .position(|case| case.test.is_none())
            .map(|i| entries[i])
            .unwrap_or(cont);

        let mut next_test = default_target;
        for (i, case) in cases.iter().enumerate().rev() {
            let Some(test) = &case.test else { continue };
            if contains_yield_expr(test) {
                bail!("yield in switch case expression needs ANF split")
            }
            let compare = Expression {
                kind: ExpressionKind::Binary {
                    left: Box::new(frame_get(&temp_field, span)),
                    operator: BinaryOperator::StrictEqual,
                    right: Box::new(self.expr(test)?),
                },
                span,
            };
            next_test = self.push(
                Vec::new(),
                Term::Branch {
                    test: compare,
                    yes: entries[i],
                    no: next_test,
                },
                Some(flow.throw_target),
            );
        }
        Ok(self.push(
            vec![frame_set(&temp_field, self.expr(discriminant)?)],
            Term::Goto(next_test),
            Some(flow.throw_target),
        ))
    }

    fn compile_try(
        &mut self,
        block_stmt: &Statement,
        handler: Option<&CatchClause>,
        finalizer: Option<&Statement>,
        cont: StateId,
        flow: &Flow,
    ) -> Result<StateId> {
        // Clone finalizer per completion edge. An abrupt completion created
        // inside the finalizer is compiled with the outer flow and overrides
        // the old completion, matching ECMAScript completion records.
        let final_normal = if let Some(finalizer) = finalizer {
            self.compile_statement(finalizer, cont, flow)?
        } else {
            cont
        };
        let final_return = if let Some(finalizer) = finalizer {
            self.compile_statement(finalizer, flow.return_target, flow)?
        } else {
            flow.return_target
        };
        let final_throw = if let Some(finalizer) = finalizer {
            self.compile_statement(finalizer, flow.throw_target, flow)?
        } else {
            flow.throw_target
        };

        let mut routed_controls = Vec::new();
        for control in &flow.controls {
            let break_target = if let Some(finalizer) = finalizer {
                self.compile_statement(finalizer, control.break_target, flow)?
            } else {
                control.break_target
            };
            let continue_target = match (finalizer, control.continue_target) {
                (Some(finalizer), Some(target)) => {
                    Some(self.compile_statement(finalizer, target, flow)?)
                }
                (_, target) => target,
            };
            routed_controls.push(Control {
                label: control.label.clone(),
                break_target,
                continue_target,
            });
        }

        let catch_flow = Flow {
            return_target: final_return,
            throw_target: final_throw,
            controls: routed_controls.clone(),
        };
        let catch_entry = if let Some(handler) = handler {
            let catch_body = self.compile_statement(&handler.body, final_normal, &catch_flow)?;
            let mut body = Vec::new();
            if let Some(parameter) = &handler.parameter {
                let slot = self
                    .slots
                    .get(parameter)
                    .ok_or_else(|| anyhow::anyhow!("missing catch slot `{parameter}`"))?;
                body.push(frame_set(&slot.field, frame_get(EXCEPTION, handler.span)));
            }
            self.push(body, Term::Goto(catch_body), Some(final_throw))
        } else {
            final_throw
        };

        let try_flow = Flow {
            return_target: final_return,
            throw_target: catch_entry,
            controls: routed_controls,
        };
        self.compile_statement(block_stmt, final_normal, &try_flow)
    }
}

fn render_resume(machine: &Machine) -> Result<Statement> {
    let mut cases = machine
        .states
        .iter()
        .map(|state| render_case(machine, state))
        .collect::<Result<Vec<_>>>()?;
    cases.push(SwitchCase {
        test: None,
        consequent: vec![
            frame_set(DONE, bool_expr(true, machine.span)),
            frame_set(OUT, undefined(machine.span)),
            frame_set(OUT_DONE, bool_expr(true, machine.span)),
            Statement {
                kind: StatementKind::Return(None),
                span: machine.span,
            },
        ],
        span: machine.span,
    });

    let dispatcher = Statement {
        kind: StatementKind::While {
            test: bool_expr(true, machine.span),
            body: Box::new(block(
                vec![Statement {
                    kind: StatementKind::Switch {
                        discriminant: frame_get(PC, machine.span),
                        cases,
                    },
                    span: machine.span,
                }],
                machine.span,
            )),
        },
        span: machine.span,
    };
    Ok(Statement {
        kind: StatementKind::FunctionDeclaration(Function {
            name: Some(machine.resume.clone()),
            parameters: vec![FRAME.to_owned()],
            body: vec![
                dispatcher,
                Statement {
                    kind: StatementKind::Return(None),
                    span: machine.span,
                },
            ],
            r#async: false,
            generator: false,
            arrow: false,
            lowering_error: None,
        }),
        span: machine.span,
    })
}

fn render_factory(machine: &Machine) -> Result<Statement> {
    let mut entries = vec![
        data(PC, num_expr(machine.entry as f64, machine.span)),
        data(STARTED, bool_expr(false, machine.span)),
        data(DONE, bool_expr(false, machine.span)),
        data(OUT, undefined(machine.span)),
        data(OUT_DONE, bool_expr(false, machine.span)),
        data(RESUME_KIND, num_expr(NEXT_KIND, machine.span)),
        data(INPUT, undefined(machine.span)),
        data(
            EXCEPTION,
            machine
                .exception_seed
                .map(|seed| seed_expression(seed, machine.span))
                .unwrap_or_else(|| undefined(machine.span)),
        ),
        data(
            RETURN_VALUE,
            machine
                .return_seed
                .map(|seed| seed_expression(seed, machine.span))
                .unwrap_or_else(|| undefined(machine.span)),
        ),
    ];
    for name in &machine.order {
        let slot = &machine.slots[name];
        entries.push(data(
            &slot.field,
            if slot.parameter {
                global(name, machine.span)
            } else {
                slot.seed
                    .map(|seed| seed_expression(seed, machine.span))
                    .unwrap_or_else(|| undefined(machine.span))
            },
        ));
    }
    entries.push(data(
        "next",
        Expression {
            kind: ExpressionKind::Function(method(machine, Method::Next)?),
            span: machine.span,
        },
    ));
    entries.push(data(
        "return",
        Expression {
            kind: ExpressionKind::Function(method(machine, Method::Return)?),
            span: machine.span,
        },
    ));
    entries.push(data(
        "throw",
        Expression {
            kind: ExpressionKind::Function(method(machine, Method::Throw)?),
            span: machine.span,
        },
    ));

    Ok(Statement {
        kind: StatementKind::FunctionDeclaration(Function {
            name: Some(machine.factory.clone()),
            parameters: machine.parameters.clone(),
            body: vec![Statement {
                kind: StatementKind::Return(Some(Expression {
                    kind: ExpressionKind::Object(entries),
                    span: machine.span,
                })),
                span: machine.span,
            }],
            r#async: false,
            generator: false,
            arrow: false,
            lowering_error: None,
        }),
        span: machine.span,
    })
}

#[derive(Clone, Copy)]
enum Method {
    Next,
    Return,
    Throw,
}

fn method(machine: &Machine, method: Method) -> Result<Function> {
    let span = machine.span;
    let this = || Expression {
        kind: ExpressionKind::This,
        span,
    };
    let get = |key: &str| member(this(), key, span);
    let set = |key: &str, value: Expression| Statement {
        kind: StatementKind::Expression(Expression {
            kind: ExpressionKind::Assignment {
                target: AssignmentTarget::Member {
                    object: Box::new(this()),
                    property: MemberProperty::Static(key.to_owned()),
                },
                operator: AssignmentOperator::Assign,
                value: Box::new(value),
            },
            span,
        }),
        span,
    };
    let resume = || expr_stmt(call(global(&machine.resume, span), vec![this()], span));
    let result = || Expression {
        kind: ExpressionKind::Object(vec![data("value", get(OUT)), data("done", get(OUT_DONE))]),
        span,
    };
    let not_started = Expression {
        kind: ExpressionKind::Unary {
            operator: UnaryOperator::Not,
            argument: Box::new(get(STARTED)),
        },
        span,
    };

    let body = match method {
        Method::Next => vec![
            Statement {
                kind: StatementKind::If {
                    test: get(DONE),
                    consequent: Box::new(block(
                        vec![
                            set(OUT, undefined(span)),
                            set(OUT_DONE, bool_expr(true, span)),
                        ],
                        span,
                    )),
                    alternate: Some(Box::new(block(
                        vec![
                            Statement {
                                kind: StatementKind::If {
                                    test: not_started.clone(),
                                    consequent: Box::new(block(
                                        vec![
                                            set(STARTED, bool_expr(true, span)),
                                            set(INPUT, undefined(span)),
                                        ],
                                        span,
                                    )),
                                    alternate: Some(Box::new(block(
                                        vec![set(INPUT, global(INPUT_PARAM, span))],
                                        span,
                                    ))),
                                },
                                span,
                            },
                            set(RESUME_KIND, num_expr(NEXT_KIND, span)),
                            resume(),
                        ],
                        span,
                    ))),
                },
                span,
            },
            Statement {
                kind: StatementKind::Return(Some(result())),
                span,
            },
        ],
        Method::Return => vec![
            Statement {
                kind: StatementKind::If {
                    test: get(DONE),
                    consequent: Box::new(block(
                        vec![
                            set(OUT, global(INPUT_PARAM, span)),
                            set(OUT_DONE, bool_expr(true, span)),
                        ],
                        span,
                    )),
                    alternate: Some(Box::new(Statement {
                        kind: StatementKind::If {
                            test: not_started.clone(),
                            consequent: Box::new(block(
                                vec![
                                    set(STARTED, bool_expr(true, span)),
                                    set(DONE, bool_expr(true, span)),
                                    set(OUT, global(INPUT_PARAM, span)),
                                    set(OUT_DONE, bool_expr(true, span)),
                                ],
                                span,
                            )),
                            alternate: Some(Box::new(block(
                                vec![
                                    set(RESUME_KIND, num_expr(RETURN_KIND, span)),
                                    set(INPUT, global(INPUT_PARAM, span)),
                                    resume(),
                                ],
                                span,
                            ))),
                        },
                        span,
                    })),
                },
                span,
            },
            Statement {
                kind: StatementKind::Return(Some(result())),
                span,
            },
        ],
        Method::Throw => vec![
            Statement {
                kind: StatementKind::If {
                    test: Expression {
                        kind: ExpressionKind::Logical {
                            left: Box::new(get(DONE)),
                            operator: LogicalOperator::Or,
                            right: Box::new(not_started),
                        },
                        span,
                    },
                    consequent: Box::new(block(
                        vec![
                            set(STARTED, bool_expr(true, span)),
                            set(DONE, bool_expr(true, span)),
                            Statement {
                                kind: StatementKind::Throw(global(INPUT_PARAM, span)),
                                span,
                            },
                        ],
                        span,
                    )),
                    alternate: Some(Box::new(block(
                        vec![
                            set(RESUME_KIND, num_expr(THROW_KIND, span)),
                            set(INPUT, global(INPUT_PARAM, span)),
                            resume(),
                        ],
                        span,
                    ))),
                },
                span,
            },
            Statement {
                kind: StatementKind::Return(Some(result())),
                span,
            },
        ],
    };

    Ok(Function {
        name: None,
        parameters: vec![INPUT_PARAM.to_owned()],
        body,
        r#async: false,
        generator: false,
        arrow: false,
        lowering_error: None,
    })
}

fn render_case(machine: &Machine, state: &State) -> Result<SwitchCase> {
    let mut protected = state.body.clone();
    protected.extend(render_term(machine, state)?);
    let consequent = if let Some(target) = state.throw_target {
        if matches!(state.term, Term::Rethrow) {
            protected
        } else {
            let error = format!("@gen_error_{}", state.id);
            vec![Statement {
                kind: StatementKind::Try {
                    block: Box::new(block(protected, machine.span)),
                    handler: Some(CatchClause {
                        parameter: Some(error.clone()),
                        body: Box::new(block(
                            vec![
                                frame_set(EXCEPTION, global(&error, machine.span)),
                                frame_set(PC, num_expr(target as f64, machine.span)),
                                Statement {
                                    kind: StatementKind::Continue(None),
                                    span: machine.span,
                                },
                            ],
                            machine.span,
                        )),
                        span: machine.span,
                    }),
                    finalizer: None,
                },
                span: machine.span,
            }]
        }
    } else {
        protected
    };
    Ok(SwitchCase {
        test: Some(num_expr(state.id as f64, machine.span)),
        consequent,
        span: machine.span,
    })
}

fn render_term(machine: &Machine, state: &State) -> Result<Vec<Statement>> {
    let span = machine.span;
    Ok(match &state.term {
        Term::Goto(target) => vec![
            frame_set(PC, num_expr(*target as f64, span)),
            Statement {
                kind: StatementKind::Continue(None),
                span,
            },
        ],
        Term::Branch { test, yes, no } => vec![
            Statement {
                kind: StatementKind::If {
                    test: test.clone(),
                    consequent: Box::new(block(
                        vec![frame_set(PC, num_expr(*yes as f64, span))],
                        span,
                    )),
                    alternate: Some(Box::new(block(
                        vec![frame_set(PC, num_expr(*no as f64, span))],
                        span,
                    ))),
                },
                span,
            },
            Statement {
                kind: StatementKind::Continue(None),
                span,
            },
        ],
        Term::Yield { value, resume } => vec![
            frame_set(PC, num_expr(*resume as f64, span)),
            frame_set(OUT, value.clone()),
            frame_set(OUT_DONE, bool_expr(false, span)),
            Statement {
                kind: StatementKind::Return(None),
                span,
            },
        ],
        Term::Resume {
            normal,
            throw_target,
            return_target,
            assign,
        } => {
            let mut normal_body = Vec::new();
            if let Some(assign) = assign {
                normal_body.push(Statement {
                    kind: StatementKind::Expression(Expression {
                        kind: ExpressionKind::Assignment {
                            target: assign.clone(),
                            operator: AssignmentOperator::Assign,
                            value: Box::new(frame_get(INPUT, span)),
                        },
                        span,
                    }),
                    span,
                });
            }
            normal_body.push(frame_set(PC, num_expr(*normal as f64, span)));
            normal_body.push(Statement {
                kind: StatementKind::Continue(None),
                span,
            });
            vec![Statement {
                kind: StatementKind::If {
                    test: strict_eq(
                        frame_get(RESUME_KIND, span),
                        num_expr(THROW_KIND, span),
                        span,
                    ),
                    consequent: Box::new(block(
                        vec![
                            frame_set(EXCEPTION, frame_get(INPUT, span)),
                            frame_set(PC, num_expr(*throw_target as f64, span)),
                            Statement {
                                kind: StatementKind::Continue(None),
                                span,
                            },
                        ],
                        span,
                    )),
                    alternate: Some(Box::new(Statement {
                        kind: StatementKind::If {
                            test: strict_eq(
                                frame_get(RESUME_KIND, span),
                                num_expr(RETURN_KIND, span),
                                span,
                            ),
                            consequent: Box::new(block(
                                vec![
                                    frame_set(RETURN_VALUE, frame_get(INPUT, span)),
                                    frame_set(PC, num_expr(*return_target as f64, span)),
                                    Statement {
                                        kind: StatementKind::Continue(None),
                                        span,
                                    },
                                ],
                                span,
                            )),
                            alternate: Some(Box::new(block(normal_body, span))),
                        },
                        span,
                    })),
                },
                span,
            }]
        }
        Term::Stop => vec![Statement {
            kind: StatementKind::Return(None),
            span,
        }],
        Term::Rethrow => vec![Statement {
            kind: StatementKind::Throw(frame_get(EXCEPTION, span)),
            span,
        }],
    })
}

fn add_slot(
    slots: &mut HashMap<String, Slot>,
    order: &mut Vec<String>,
    name: &str,
    kind: VariableKind,
    parameter: bool,
) {
    if slots.contains_key(name) {
        return;
    }
    let field = format!("@gen_slot_{}_{}", order.len(), sanitize(name));
    slots.insert(
        name.to_owned(),
        Slot {
            field,
            kind,
            parameter,
            seed: None,
        },
    );
    order.push(name.to_owned());
}

fn collect_slots(
    statements: &[Statement],
    slots: &mut HashMap<String, Slot>,
    order: &mut Vec<String>,
) -> Result<()> {
    for statement in statements {
        match &statement.kind {
            StatementKind::VariableDeclaration { kind, declarations } => {
                for d in declarations {
                    add_slot(slots, order, &d.name, *kind, false);
                }
            }
            StatementKind::Block(body) => collect_slots(body, slots, order)?,
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                collect_slots(std::slice::from_ref(consequent.as_ref()), slots, order)?;
                if let Some(alt) = alternate {
                    collect_slots(std::slice::from_ref(alt.as_ref()), slots, order)?;
                }
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Labeled { body, .. } => {
                collect_slots(std::slice::from_ref(body.as_ref()), slots, order)?;
            }
            StatementKind::For { init, body, .. } => {
                if let Some(ForInit::VariableDeclaration { kind, declarations }) = init {
                    for d in declarations {
                        add_slot(slots, order, &d.name, *kind, false);
                    }
                }
                collect_slots(std::slice::from_ref(body.as_ref()), slots, order)?;
            }
            StatementKind::ForIn {
                name, kind, body, ..
            }
            | StatementKind::ForOf {
                name, kind, body, ..
            } => {
                add_slot(slots, order, name, *kind, false);
                collect_slots(std::slice::from_ref(body.as_ref()), slots, order)?;
            }
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    collect_slots(&case.consequent, slots, order)?;
                }
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                collect_slots(std::slice::from_ref(block.as_ref()), slots, order)?;
                if let Some(handler) = handler {
                    if let Some(parameter) = &handler.parameter {
                        add_slot(slots, order, parameter, VariableKind::Let, false);
                    }
                    collect_slots(std::slice::from_ref(handler.body.as_ref()), slots, order)?;
                }
                if let Some(finalizer) = finalizer {
                    collect_slots(std::slice::from_ref(finalizer.as_ref()), slots, order)?;
                }
            }
            StatementKind::FunctionDeclaration(_)
            | StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Expression(_)
            | StatementKind::Return(_)
            | StatementKind::Throw(_)
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
        }
    }
    Ok(())
}

fn rewrite_plain(
    statement: &Statement,
    slots: &HashMap<String, Slot>,
    factories: &HashMap<String, String>,
) -> Result<Statement> {
    let span = statement.span;
    Ok(Statement {
        kind: match &statement.kind {
            StatementKind::Empty => StatementKind::Empty,
            StatementKind::Debugger => StatementKind::Debugger,
            StatementKind::Expression(value) => {
                StatementKind::Expression(rewrite_machine_expr(value, slots, factories)?)
            }
            StatementKind::VariableDeclaration { declarations, .. } => {
                let mut body = Vec::new();
                for d in declarations {
                    if let Some(init) = &d.init {
                        let slot = &slots[&d.name];
                        body.push(frame_set(
                            &slot.field,
                            rewrite_machine_expr(init, slots, factories)?,
                        ));
                    }
                }
                return Ok(block(body, span));
            }
            StatementKind::Block(body) => StatementKind::Block(
                body.iter()
                    .map(|s| rewrite_plain(s, slots, factories))
                    .collect::<Result<Vec<_>>>()?,
            ),
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => StatementKind::If {
                test: rewrite_machine_expr(test, slots, factories)?,
                consequent: Box::new(rewrite_plain(consequent, slots, factories)?),
                alternate: alternate
                    .as_deref()
                    .map(|s| rewrite_plain(s, slots, factories).map(Box::new))
                    .transpose()?,
            },
            StatementKind::While { test, body } => StatementKind::While {
                test: rewrite_machine_expr(test, slots, factories)?,
                body: Box::new(rewrite_plain(body, slots, factories)?),
            },
            StatementKind::DoWhile { body, test } => StatementKind::DoWhile {
                body: Box::new(rewrite_plain(body, slots, factories)?),
                test: rewrite_machine_expr(test, slots, factories)?,
            },
            StatementKind::FunctionDeclaration(function) => {
                // A nested closure can retain the generator frame by directly
                // referencing FRAME after free-local rewrite. Static graph later
                // either inlines it or diagnoses a real runtime closure escape.
                StatementKind::FunctionDeclaration(Function {
                    name: function.name.clone(),
                    parameters: function.parameters.clone(),
                    body: function
                        .body
                        .iter()
                        .map(|s| rewrite_plain(s, slots, factories))
                        .collect::<Result<Vec<_>>>()?,
                    r#async: function.r#async,
                    generator: function.generator,
                    arrow: function.arrow,
                    lowering_error: function.lowering_error.clone(),
                })
            }
            StatementKind::Return(value) => StatementKind::Return(
                value
                    .as_ref()
                    .map(|v| rewrite_machine_expr(v, slots, factories))
                    .transpose()?,
            ),
            StatementKind::Throw(value) => {
                StatementKind::Throw(rewrite_machine_expr(value, slots, factories)?)
            }
            StatementKind::Break(label) => StatementKind::Break(label.clone()),
            StatementKind::Continue(label) => StatementKind::Continue(label.clone()),
            StatementKind::For { .. }
            | StatementKind::ForIn { .. }
            | StatementKind::ForOf { .. }
            | StatementKind::Switch { .. }
            | StatementKind::Labeled { .. }
            | StatementKind::Try { .. } => {
                bail!("structured generator statement must compile to PC states")
            }
        },
        span,
    })
}

fn rewrite_machine_expr(
    value: &Expression,
    slots: &HashMap<String, Slot>,
    factories: &HashMap<String, String>,
) -> Result<Expression> {
    let span = value.span;
    Ok(Expression {
        kind: match &value.kind {
            ExpressionKind::Global(name) => {
                if let Some(slot) = slots.get(name) {
                    return Ok(frame_get(&slot.field, span));
                }
                ExpressionKind::Global(factories.get(name).cloned().unwrap_or_else(|| name.clone()))
            }
            ExpressionKind::Member { object, property } => ExpressionKind::Member {
                object: Box::new(rewrite_machine_expr(object, slots, factories)?),
                property: match property {
                    MemberProperty::Static(key) => MemberProperty::Static(key.clone()),
                    MemberProperty::Computed(key) =>
                        MemberProperty::Computed(Box::new(rewrite_machine_expr(key, slots, factories)?)),
                },
            },
            ExpressionKind::Object(entries) => ExpressionKind::Object(
                entries.iter().map(|entry| match entry {
                    ObjectEntry::Property(p) => Ok(ObjectEntry::Property(ObjectProperty {
                        key: p.key.clone(),
                        value: rewrite_machine_expr(&p.value, slots, factories)?,
                    })),
                    ObjectEntry::Spread(v) =>
                        Ok(ObjectEntry::Spread(rewrite_machine_expr(v, slots, factories)?)),
                    ObjectEntry::Accessor { .. } =>
                        bail!("accessor literal inside resumable generator needs frame-aware closure lowering"),
                }).collect::<Result<Vec<_>>>()?
            ),
            ExpressionKind::Array(elements) => ExpressionKind::Array(
                elements.iter().map(|element| match element {
                    ecmora_hir::ArrayElement::Expression(v) =>
                        Ok(ecmora_hir::ArrayElement::Expression(rewrite_machine_expr(v, slots, factories)?)),
                    ecmora_hir::ArrayElement::Spread(v) =>
                        Ok(ecmora_hir::ArrayElement::Spread(rewrite_machine_expr(v, slots, factories)?)),
                    ecmora_hir::ArrayElement::Hole => Ok(ecmora_hir::ArrayElement::Hole),
                }).collect::<Result<Vec<_>>>()?
            ),
            ExpressionKind::Conditional { test, consequent, alternate } =>
                ExpressionKind::Conditional {
                    test: Box::new(rewrite_machine_expr(test, slots, factories)?),
                    consequent: Box::new(rewrite_machine_expr(consequent, slots, factories)?),
                    alternate: Box::new(rewrite_machine_expr(alternate, slots, factories)?),
                },
            ExpressionKind::Unary { operator, argument } => ExpressionKind::Unary {
                operator: *operator,
                argument: Box::new(rewrite_machine_expr(argument, slots, factories)?),
            },
            ExpressionKind::Binary { left, operator, right } => ExpressionKind::Binary {
                left: Box::new(rewrite_machine_expr(left, slots, factories)?),
                operator: *operator,
                right: Box::new(rewrite_machine_expr(right, slots, factories)?),
            },
            ExpressionKind::Logical { left, operator, right } => ExpressionKind::Logical {
                left: Box::new(rewrite_machine_expr(left, slots, factories)?),
                operator: *operator,
                right: Box::new(rewrite_machine_expr(right, slots, factories)?),
            },
            ExpressionKind::Assignment { target, operator, value } => {
                if let AssignmentTarget::Identifier(name) = target {
                    if let Some(slot) = slots.get(name) {
                        if slot.kind == VariableKind::Const && !slot.parameter {
                            bail!("assignment to const generator local `{name}`")
                        }
                    }
                }
                ExpressionKind::Assignment {
                    target: rewrite_machine_target(target, slots, factories)?,
                    operator: *operator,
                    value: Box::new(rewrite_machine_expr(value, slots, factories)?),
                }
            }
            ExpressionKind::Update { target, operator, prefix } => {
                if let AssignmentTarget::Identifier(name) = target {
                    if let Some(slot) = slots.get(name) {
                        if slot.kind == VariableKind::Const && !slot.parameter {
                            bail!("update of const generator local `{name}`")
                        }
                    }
                }
                ExpressionKind::Update {
                    target: rewrite_machine_target(target, slots, factories)?,
                    operator: *operator,
                    prefix: *prefix,
                }
            }
            ExpressionKind::Call { callee, arguments } => ExpressionKind::Call {
                callee: Box::new(rewrite_machine_expr(callee, slots, factories)?),
                arguments: arguments.iter()
                    .map(|a| rewrite_machine_expr(a, slots, factories))
                    .collect::<Result<Vec<_>>>()?,
            },
            ExpressionKind::New { callee, arguments } => ExpressionKind::New {
                callee: Box::new(rewrite_machine_expr(callee, slots, factories)?),
                arguments: arguments.iter()
                    .map(|a| rewrite_machine_expr(a, slots, factories))
                    .collect::<Result<Vec<_>>>()?,
            },
            ExpressionKind::Function(_) => {
                bail!("function expression inside general generator needs explicit frame-capture closure lowering")
            }
            ExpressionKind::Await(v) =>
                ExpressionKind::Await(Box::new(rewrite_machine_expr(v, slots, factories)?)),
            ExpressionKind::String(v) => ExpressionKind::String(v.clone()),
            ExpressionKind::Number(v) => ExpressionKind::Number(*v),
            ExpressionKind::BigInt(v) => ExpressionKind::BigInt(v.clone()),
            ExpressionKind::Bool(v) => ExpressionKind::Bool(*v),
            ExpressionKind::Null => ExpressionKind::Null,
            ExpressionKind::This => ExpressionKind::This,
        },
        span,
    })
}

fn rewrite_machine_target(
    target: &AssignmentTarget,
    slots: &HashMap<String, Slot>,
    factories: &HashMap<String, String>,
) -> Result<AssignmentTarget> {
    Ok(match target {
        AssignmentTarget::Identifier(name) => {
            if let Some(slot) = slots.get(name) {
                AssignmentTarget::Member {
                    object: Box::new(global(FRAME, Span::new(0, 0))),
                    property: MemberProperty::Static(slot.field.clone()),
                }
            } else {
                AssignmentTarget::Identifier(name.clone())
            }
        }
        AssignmentTarget::Member { object, property } => AssignmentTarget::Member {
            object: Box::new(rewrite_machine_expr(object, slots, factories)?),
            property: match property {
                MemberProperty::Static(key) => MemberProperty::Static(key.clone()),
                MemberProperty::Computed(key) => {
                    MemberProperty::Computed(Box::new(rewrite_machine_expr(key, slots, factories)?))
                }
            },
        },
    })
}

fn rewrite_refs_statement(
    statement: &Statement,
    factories: &HashMap<String, String>,
) -> Result<Statement> {
    let span = statement.span;
    Ok(Statement {
        kind: match &statement.kind {
            StatementKind::Empty => StatementKind::Empty,
            StatementKind::Debugger => StatementKind::Debugger,
            StatementKind::Expression(v) => {
                StatementKind::Expression(rewrite_refs_expr(v, factories)?)
            }
            StatementKind::VariableDeclaration { kind, declarations } => {
                StatementKind::VariableDeclaration {
                    kind: *kind,
                    declarations: declarations
                        .iter()
                        .map(|d| -> Result<VariableDeclarator> {
                            Ok(VariableDeclarator {
                                name: d.name.clone(),
                                init: d
                                    .init
                                    .as_ref()
                                    .map(|v| rewrite_refs_expr(v, factories))
                                    .transpose()?,
                                span: d.span,
                            })
                        })
                        .collect::<Result<Vec<_>>>()?,
                }
            }
            StatementKind::Block(body) => StatementKind::Block(
                body.iter()
                    .map(|s| rewrite_refs_statement(s, factories))
                    .collect::<Result<Vec<_>>>()?,
            ),
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => StatementKind::If {
                test: rewrite_refs_expr(test, factories)?,
                consequent: Box::new(rewrite_refs_statement(consequent, factories)?),
                alternate: alternate
                    .as_deref()
                    .map(|s| rewrite_refs_statement(s, factories).map(Box::new))
                    .transpose()?,
            },
            StatementKind::While { test, body } => StatementKind::While {
                test: rewrite_refs_expr(test, factories)?,
                body: Box::new(rewrite_refs_statement(body, factories)?),
            },
            StatementKind::DoWhile { body, test } => StatementKind::DoWhile {
                body: Box::new(rewrite_refs_statement(body, factories)?),
                test: rewrite_refs_expr(test, factories)?,
            },
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => StatementKind::For {
                init: init
                    .as_ref()
                    .map(|init| match init {
                        ForInit::Expression(v) => Ok::<ForInit, anyhow::Error>(
                            ForInit::Expression(rewrite_refs_expr(v, factories)?),
                        ),
                        ForInit::VariableDeclaration { kind, declarations } => {
                            Ok(ForInit::VariableDeclaration {
                                kind: *kind,
                                declarations: declarations
                                    .iter()
                                    .map(|d| -> Result<VariableDeclarator> {
                                        Ok(VariableDeclarator {
                                            name: d.name.clone(),
                                            init: d
                                                .init
                                                .as_ref()
                                                .map(|v| rewrite_refs_expr(v, factories))
                                                .transpose()?,
                                            span: d.span,
                                        })
                                    })
                                    .collect::<Result<Vec<_>>>()?,
                            })
                        }
                    })
                    .transpose()?,
                test: test
                    .as_ref()
                    .map(|v| rewrite_refs_expr(v, factories))
                    .transpose()?,
                update: update
                    .as_ref()
                    .map(|v| rewrite_refs_expr(v, factories))
                    .transpose()?,
                body: Box::new(rewrite_refs_statement(body, factories)?),
            },
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => StatementKind::ForIn {
                name: name.clone(),
                kind: *kind,
                right: rewrite_refs_expr(right, factories)?,
                body: Box::new(rewrite_refs_statement(body, factories)?),
            },
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => StatementKind::ForOf {
                name: name.clone(),
                kind: *kind,
                right: rewrite_refs_expr(right, factories)?,
                body: Box::new(rewrite_refs_statement(body, factories)?),
            },
            StatementKind::Switch {
                discriminant,
                cases,
            } => StatementKind::Switch {
                discriminant: rewrite_refs_expr(discriminant, factories)?,
                cases: cases
                    .iter()
                    .map(|case| -> Result<SwitchCase> {
                        Ok(SwitchCase {
                            test: case
                                .test
                                .as_ref()
                                .map(|v| rewrite_refs_expr(v, factories))
                                .transpose()?,
                            consequent: case
                                .consequent
                                .iter()
                                .map(|s| rewrite_refs_statement(s, factories))
                                .collect::<Result<Vec<_>>>()?,
                            span: case.span,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?,
            },
            StatementKind::Labeled { label, body } => StatementKind::Labeled {
                label: label.clone(),
                body: Box::new(rewrite_refs_statement(body, factories)?),
            },
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => StatementKind::Try {
                block: Box::new(rewrite_refs_statement(block, factories)?),
                handler: handler
                    .as_ref()
                    .map(|h| -> Result<CatchClause> {
                        Ok(CatchClause {
                            parameter: h.parameter.clone(),
                            body: Box::new(rewrite_refs_statement(&h.body, factories)?),
                            span: h.span,
                        })
                    })
                    .transpose()?,
                finalizer: finalizer
                    .as_deref()
                    .map(|s| rewrite_refs_statement(s, factories).map(Box::new))
                    .transpose()?,
            },
            StatementKind::FunctionDeclaration(function) => {
                if function.generator {
                    statement.kind.clone()
                } else {
                    StatementKind::FunctionDeclaration(Function {
                        name: function.name.clone(),
                        parameters: function.parameters.clone(),
                        body: function
                            .body
                            .iter()
                            .map(|s| rewrite_refs_statement(s, factories))
                            .collect::<Result<Vec<_>>>()?,
                        r#async: function.r#async,
                        generator: false,
                        arrow: function.arrow,
                        lowering_error: function.lowering_error.clone(),
                    })
                }
            }
            StatementKind::Return(v) => StatementKind::Return(
                v.as_ref()
                    .map(|v| rewrite_refs_expr(v, factories))
                    .transpose()?,
            ),
            StatementKind::Throw(v) => StatementKind::Throw(rewrite_refs_expr(v, factories)?),
            StatementKind::Break(label) => StatementKind::Break(label.clone()),
            StatementKind::Continue(label) => StatementKind::Continue(label.clone()),
        },
        span,
    })
}

fn rewrite_refs_expr(
    value: &Expression,
    factories: &HashMap<String, String>,
) -> Result<Expression> {
    let span = value.span;
    Ok(Expression {
        kind: match &value.kind {
            ExpressionKind::Global(name) => {
                ExpressionKind::Global(factories.get(name).cloned().unwrap_or_else(|| name.clone()))
            }
            ExpressionKind::Member { object, property } => ExpressionKind::Member {
                object: Box::new(rewrite_refs_expr(object, factories)?),
                property: match property {
                    MemberProperty::Static(k) => MemberProperty::Static(k.clone()),
                    MemberProperty::Computed(k) => {
                        MemberProperty::Computed(Box::new(rewrite_refs_expr(k, factories)?))
                    }
                },
            },
            ExpressionKind::Object(entries) => ExpressionKind::Object(
                entries
                    .iter()
                    .map(|entry| match entry {
                        ObjectEntry::Property(p) => Ok(ObjectEntry::Property(ObjectProperty {
                            key: p.key.clone(),
                            value: rewrite_refs_expr(&p.value, factories)?,
                        })),
                        ObjectEntry::Spread(v) => {
                            Ok(ObjectEntry::Spread(rewrite_refs_expr(v, factories)?))
                        }
                        ObjectEntry::Accessor { key, get, set } => Ok(ObjectEntry::Accessor {
                            key: key.clone(),
                            get: get
                                .as_ref()
                                .map(|v| rewrite_refs_expr(v, factories))
                                .transpose()?,
                            set: set
                                .as_ref()
                                .map(|v| rewrite_refs_expr(v, factories))
                                .transpose()?,
                        }),
                    })
                    .collect::<Result<Vec<_>>>()?,
            ),
            ExpressionKind::Array(elements) => ExpressionKind::Array(
                elements
                    .iter()
                    .map(|e| match e {
                        ecmora_hir::ArrayElement::Expression(v) => Ok(
                            ecmora_hir::ArrayElement::Expression(rewrite_refs_expr(v, factories)?),
                        ),
                        ecmora_hir::ArrayElement::Spread(v) => Ok(
                            ecmora_hir::ArrayElement::Spread(rewrite_refs_expr(v, factories)?),
                        ),
                        ecmora_hir::ArrayElement::Hole => Ok(ecmora_hir::ArrayElement::Hole),
                    })
                    .collect::<Result<Vec<_>>>()?,
            ),
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => ExpressionKind::Conditional {
                test: Box::new(rewrite_refs_expr(test, factories)?),
                consequent: Box::new(rewrite_refs_expr(consequent, factories)?),
                alternate: Box::new(rewrite_refs_expr(alternate, factories)?),
            },
            ExpressionKind::Unary { operator, argument } => ExpressionKind::Unary {
                operator: *operator,
                argument: Box::new(rewrite_refs_expr(argument, factories)?),
            },
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => ExpressionKind::Binary {
                left: Box::new(rewrite_refs_expr(left, factories)?),
                operator: *operator,
                right: Box::new(rewrite_refs_expr(right, factories)?),
            },
            ExpressionKind::Logical {
                left,
                operator,
                right,
            } => ExpressionKind::Logical {
                left: Box::new(rewrite_refs_expr(left, factories)?),
                operator: *operator,
                right: Box::new(rewrite_refs_expr(right, factories)?),
            },
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => ExpressionKind::Assignment {
                target: target.clone(),
                operator: *operator,
                value: Box::new(rewrite_refs_expr(value, factories)?),
            },
            ExpressionKind::Update {
                target,
                operator,
                prefix,
            } => ExpressionKind::Update {
                target: target.clone(),
                operator: *operator,
                prefix: *prefix,
            },
            ExpressionKind::Call { callee, arguments } => ExpressionKind::Call {
                callee: Box::new(rewrite_refs_expr(callee, factories)?),
                arguments: arguments
                    .iter()
                    .map(|a| rewrite_refs_expr(a, factories))
                    .collect::<Result<Vec<_>>>()?,
            },
            ExpressionKind::New { callee, arguments } => ExpressionKind::New {
                callee: Box::new(rewrite_refs_expr(callee, factories)?),
                arguments: arguments
                    .iter()
                    .map(|a| rewrite_refs_expr(a, factories))
                    .collect::<Result<Vec<_>>>()?,
            },
            ExpressionKind::Function(function) => ExpressionKind::Function(Function {
                name: function.name.clone(),
                parameters: function.parameters.clone(),
                body: function
                    .body
                    .iter()
                    .map(|s| rewrite_refs_statement(s, factories))
                    .collect::<Result<Vec<_>>>()?,
                r#async: function.r#async,
                generator: function.generator,
                arrow: function.arrow,
                lowering_error: function.lowering_error.clone(),
            }),
            ExpressionKind::Await(v) => {
                ExpressionKind::Await(Box::new(rewrite_refs_expr(v, factories)?))
            }
            ExpressionKind::String(v) => ExpressionKind::String(v.clone()),
            ExpressionKind::Number(v) => ExpressionKind::Number(*v),
            ExpressionKind::BigInt(v) => ExpressionKind::BigInt(v.clone()),
            ExpressionKind::Bool(v) => ExpressionKind::Bool(*v),
            ExpressionKind::Null => ExpressionKind::Null,
            ExpressionKind::This => ExpressionKind::This,
        },
        span,
    })
}

fn yield_marker(value: &Expression) -> Option<(Expression, bool)> {
    let ExpressionKind::Call { callee, arguments } = &value.kind else {
        return None;
    };
    if !matches!(&callee.kind, ExpressionKind::Global(name) if name == "@yield") {
        return None;
    }
    let [value, delegate] = arguments.as_slice() else {
        return None;
    };
    let ExpressionKind::Bool(delegate) = delegate.kind else {
        return None;
    };
    Some((value.clone(), delegate))
}

fn contains_yield_expr(value: &Expression) -> bool {
    if yield_marker(value).is_some() {
        return true;
    }
    match &value.kind {
        ExpressionKind::Member { object, property } => {
            contains_yield_expr(object)
                || matches!(property, MemberProperty::Computed(v) if contains_yield_expr(v))
        }
        ExpressionKind::Object(entries) => entries.iter().any(|e| match e {
            ObjectEntry::Property(p) => contains_yield_expr(&p.value),
            ObjectEntry::Spread(v) => contains_yield_expr(v),
            ObjectEntry::Accessor { get, set, .. } => {
                get.as_ref().is_some_and(contains_yield_expr)
                    || set.as_ref().is_some_and(contains_yield_expr)
            }
        }),
        ExpressionKind::Array(elements) => elements.iter().any(|e| match e {
            ecmora_hir::ArrayElement::Expression(v) | ecmora_hir::ArrayElement::Spread(v) => {
                contains_yield_expr(v)
            }
            ecmora_hir::ArrayElement::Hole => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            contains_yield_expr(test)
                || contains_yield_expr(consequent)
                || contains_yield_expr(alternate)
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            contains_yield_expr(argument)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            contains_yield_expr(left) || contains_yield_expr(right)
        }
        ExpressionKind::Assignment { value, .. } => contains_yield_expr(value),
        ExpressionKind::Call { callee, arguments } | ExpressionKind::New { callee, arguments } => {
            contains_yield_expr(callee) || arguments.iter().any(contains_yield_expr)
        }
        _ => false,
    }
}

fn statement_contains_yield(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Expression(v) | StatementKind::Throw(v) => contains_yield_expr(v),
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|d| d.init.as_ref())
            .any(contains_yield_expr),
        StatementKind::Block(body) => body.iter().any(statement_contains_yield),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            contains_yield_expr(test)
                || statement_contains_yield(consequent)
                || alternate.as_deref().is_some_and(statement_contains_yield)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            contains_yield_expr(test) || statement_contains_yield(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(v) => contains_yield_expr(v),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|d| d.init.as_ref())
                    .any(contains_yield_expr),
            }) || test.as_ref().is_some_and(contains_yield_expr)
                || update.as_ref().is_some_and(contains_yield_expr)
                || statement_contains_yield(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            contains_yield_expr(right) || statement_contains_yield(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            contains_yield_expr(discriminant)
                || cases.iter().any(|c| {
                    c.test.as_ref().is_some_and(contains_yield_expr)
                        || c.consequent.iter().any(statement_contains_yield)
                })
        }
        StatementKind::Labeled { body, .. } => statement_contains_yield(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_contains_yield(block)
                || handler
                    .as_ref()
                    .is_some_and(|h| statement_contains_yield(&h.body))
                || finalizer.as_deref().is_some_and(statement_contains_yield)
        }
        StatementKind::Return(v) => v.as_ref().is_some_and(contains_yield_expr),
        StatementKind::FunctionDeclaration(_) => false,
        _ => false,
    }
}

fn statement_contains_yield_star(statement: &Statement) -> bool {
    fn expr(v: &Expression) -> bool {
        if yield_marker(v).is_some_and(|(_, delegate)| delegate) {
            return true;
        }
        match &v.kind {
            ExpressionKind::Member { object, property } => {
                expr(object) || matches!(property, MemberProperty::Computed(k) if expr(k))
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => expr(left) || expr(right),
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expr(argument)
            }
            ExpressionKind::Assignment { value, .. } => expr(value),
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                expr(callee) || arguments.iter().any(expr)
            }
            _ => false,
        }
    }
    match &statement.kind {
        StatementKind::Expression(v) | StatementKind::Throw(v) => expr(v),
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|d| d.init.as_ref())
            .any(expr),
        StatementKind::Block(body) => body.iter().any(statement_contains_yield_star),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            statement_contains_yield_star(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(statement_contains_yield_star)
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => statement_contains_yield_star(body),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|c| &c.consequent)
            .any(statement_contains_yield_star),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_contains_yield_star(block)
                || handler
                    .as_ref()
                    .is_some_and(|h| statement_contains_yield_star(&h.body))
                || finalizer
                    .as_deref()
                    .is_some_and(statement_contains_yield_star)
        }
        StatementKind::Return(v) => v.as_ref().is_some_and(expr),
        _ => false,
    }
}

fn yield_requires_cfg(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            statement_contains_yield(consequent)
                || alternate.as_deref().is_some_and(statement_contains_yield)
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => statement_contains_yield(body),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|c| &c.consequent)
            .any(statement_contains_yield),
        StatementKind::Try { .. } => statement_contains_yield(statement),
        StatementKind::Block(body) => body.iter().any(yield_requires_cfg),
        _ => false,
    }
}

fn statement_calls_generator(statement: &Statement, names: &HashSet<String>) -> bool {
    fn expr(value: &Expression, names: &HashSet<String>) -> bool {
        if matches!(
            &value.kind,
            ExpressionKind::Call { callee, .. }
                if matches!(&callee.kind, ExpressionKind::Global(name) if names.contains(name))
        ) {
            return true;
        }
        match &value.kind {
            ExpressionKind::Member { object, property } => {
                expr(object, names)
                    || matches!(property, MemberProperty::Computed(key) if expr(key, names))
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                expr(left, names) || expr(right, names)
            }
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expr(argument, names)
            }
            ExpressionKind::Assignment { value, .. } => expr(value, names),
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                expr(callee, names) || arguments.iter().any(|value| expr(value, names))
            }
            _ => false,
        }
    }
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => expr(value, names),
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|d| d.init.as_ref())
            .any(|v| expr(v, names)),
        StatementKind::Block(body) => body.iter().any(|s| statement_calls_generator(s, names)),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expr(test, names)
                || statement_calls_generator(consequent, names)
                || alternate
                    .as_deref()
                    .is_some_and(|s| statement_calls_generator(s, names))
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expr(test, names) || statement_calls_generator(body, names)
        }
        StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => statement_calls_generator(body, names),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|c| &c.consequent)
            .any(|s| statement_calls_generator(s, names)),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_calls_generator(block, names)
                || handler
                    .as_ref()
                    .is_some_and(|h| statement_calls_generator(&h.body, names))
                || finalizer
                    .as_deref()
                    .is_some_and(|s| statement_calls_generator(s, names))
        }
        StatementKind::FunctionDeclaration(function) => function
            .body
            .iter()
            .any(|s| statement_calls_generator(s, names)),
        StatementKind::Return(value) => value.as_ref().is_some_and(|v| expr(v, names)),
        _ => false,
    }
}

fn protocol_call(statement: &Statement) -> bool {
    fn expr(v: &Expression) -> bool {
        if let ExpressionKind::Call { callee, .. } = &v.kind {
            if matches!(
                &callee.kind,
                ExpressionKind::Member { property: MemberProperty::Static(method), .. }
                    if matches!(method.as_str(), "next" | "return" | "throw")
            ) {
                return true;
            }
        }
        match &v.kind {
            ExpressionKind::Member { object, property } => {
                expr(object) || matches!(property, MemberProperty::Computed(k) if expr(k))
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => expr(left) || expr(right),
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expr(argument)
            }
            ExpressionKind::Assignment { value, .. } => expr(value),
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                expr(callee) || arguments.iter().any(expr)
            }
            _ => false,
        }
    }
    match &statement.kind {
        StatementKind::Expression(v) | StatementKind::Throw(v) => expr(v),
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|d| d.init.as_ref())
            .any(expr),
        StatementKind::Block(body) => body.iter().any(protocol_call),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expr(test)
                || protocol_call(consequent)
                || alternate.as_deref().is_some_and(protocol_call)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expr(test) || protocol_call(body)
        }
        StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => protocol_call(body),
        StatementKind::Switch { cases, .. } => {
            cases.iter().flat_map(|c| &c.consequent).any(protocol_call)
        }
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            protocol_call(block)
                || handler.as_ref().is_some_and(|h| protocol_call(&h.body))
                || finalizer.as_deref().is_some_and(protocol_call)
        }
        StatementKind::FunctionDeclaration(function) => function.body.iter().any(protocol_call),
        StatementKind::Return(v) => v.as_ref().is_some_and(expr),
        _ => false,
    }
}

fn protocol_under_control(statement: &Statement, depth: usize) -> bool {
    if depth > 0 && protocol_call(statement) {
        return true;
    }
    match &statement.kind {
        StatementKind::Block(body) => body.iter().any(|s| protocol_under_control(s, depth)),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            protocol_under_control(consequent, depth + 1)
                || alternate
                    .as_deref()
                    .is_some_and(|s| protocol_under_control(s, depth + 1))
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => protocol_under_control(body, depth + 1),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|c| &c.consequent)
            .any(|s| protocol_under_control(s, depth + 1)),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            protocol_under_control(block, depth + 1)
                || handler
                    .as_ref()
                    .is_some_and(|h| protocol_under_control(&h.body, depth + 1))
                || finalizer
                    .as_deref()
                    .is_some_and(|s| protocol_under_control(s, depth + 1))
        }
        _ => false,
    }
}

fn validate_erased(statements: &[Statement]) -> Result<()> {
    for statement in statements {
        if statement_contains_yield(statement) {
            bail!("general generator CFG left @yield in executable HIR")
        }
    }
    Ok(())
}

fn function_span(function: &Function) -> Span {
    function
        .body
        .first()
        .map(|s| s.span)
        .unwrap_or(Span::new(0, 0))
}
fn data(key: &str, value: Expression) -> ObjectEntry {
    ObjectEntry::Property(ObjectProperty {
        key: MemberProperty::Static(key.to_owned()),
        value,
    })
}
fn frame_get(key: &str, span: Span) -> Expression {
    member(global(FRAME, span), key, span)
}
fn frame_set(key: &str, value: Expression) -> Statement {
    let span = value.span;
    Statement {
        kind: StatementKind::Expression(Expression {
            kind: ExpressionKind::Assignment {
                target: AssignmentTarget::Member {
                    object: Box::new(global(FRAME, span)),
                    property: MemberProperty::Static(key.to_owned()),
                },
                operator: AssignmentOperator::Assign,
                value: Box::new(value),
            },
            span,
        }),
        span,
    }
}
fn global(name: &str, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Global(name.to_owned()),
        span,
    }
}
fn undefined(span: Span) -> Expression {
    global("undefined", span)
}
fn bool_expr(value: bool, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Bool(value),
        span,
    }
}
fn num_expr(value: f64, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Number(value),
        span,
    }
}
fn member(object: Expression, key: &str, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Member {
            object: Box::new(object),
            property: MemberProperty::Static(key.to_owned()),
        },
        span,
    }
}
fn call(callee: Expression, arguments: Vec<Expression>, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Call {
            callee: Box::new(callee),
            arguments,
        },
        span,
    }
}
fn expr_stmt(value: Expression) -> Statement {
    Statement {
        span: value.span,
        kind: StatementKind::Expression(value),
    }
}
fn block(body: Vec<Statement>, span: Span) -> Statement {
    Statement {
        kind: StatementKind::Block(body),
        span,
    }
}
fn strict_eq(left: Expression, right: Expression, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Binary {
            left: Box::new(left),
            operator: BinaryOperator::StrictEqual,
            right: Box::new(right),
        },
        span,
    }
}
fn state_tag(span: Span) -> u64 {
    ((span.start as u64) << 32) | span.end as u64
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}
