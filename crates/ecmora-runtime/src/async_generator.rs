use anyhow::{Result, bail};
use ecmora_hir::{AssignmentTarget, Expression, ExpressionKind, Statement, StatementKind};

#[derive(Debug, Clone)]
pub(super) enum GeneratorResumeAction {
    Discard,
    Initialize(String),
    Assign(AssignmentTarget),
    Return,
}

pub(super) fn direct_yield(
    statement: &Statement,
) -> Result<Option<(Option<Expression>, GeneratorResumeAction)>> {
    match &statement.kind {
        StatementKind::Expression(Expression {
            kind:
                ExpressionKind::Assignment {
                    target,
                    operator: ecmora_hir::AssignmentOperator::Assign,
                    value,
                },
            ..
        }) => {
            let Some((argument, delegate)) = yield_call(value) else {
                return reject_nested_yield(statement);
            };
            reject_delegate(delegate)?;
            Ok(Some((
                argument,
                GeneratorResumeAction::Assign(target.clone()),
            )))
        }
        StatementKind::Expression(expression) => {
            if let Some((argument, delegate)) = yield_call(expression) {
                reject_delegate(delegate)?;
                return Ok(Some((argument, GeneratorResumeAction::Discard)));
            }
            reject_nested_yield(statement)
        }
        StatementKind::VariableDeclaration { declarations, .. } if declarations.len() == 1 => {
            let declaration = &declarations[0];
            let Some(initializer) = declaration.init.as_ref() else {
                return Ok(None);
            };
            let Some((argument, delegate)) = yield_call(initializer) else {
                return reject_nested_yield(statement);
            };
            reject_delegate(delegate)?;
            Ok(Some((
                argument,
                GeneratorResumeAction::Initialize(declaration.name.clone()),
            )))
        }
        StatementKind::Return(Some(expression)) => {
            let Some((argument, delegate)) = yield_call(expression) else {
                return reject_nested_yield(statement);
            };
            reject_delegate(delegate)?;
            Ok(Some((argument, GeneratorResumeAction::Return)))
        }
        _ => reject_nested_yield(statement),
    }
}

fn yield_call(expression: &Expression) -> Option<(Option<Expression>, bool)> {
    let ExpressionKind::Call { callee, arguments } = &expression.kind else {
        return None;
    };
    if !matches!(&callee.kind, ExpressionKind::Global(name) if name == "@yield") {
        return None;
    }
    let argument = arguments.first().cloned().and_then(|value| {
        if matches!(&value.kind, ExpressionKind::Global(name) if name == "undefined") {
            None
        } else {
            Some(value)
        }
    });
    let delegate = matches!(
        arguments.get(1),
        Some(Expression {
            kind: ExpressionKind::Bool(true),
            ..
        })
    );
    Some((argument, delegate))
}

fn reject_delegate(delegate: bool) -> Result<()> {
    if delegate {
        bail!("yield* cần iterator delegation state machine")
    }
    Ok(())
}

fn reject_nested_yield(
    statement: &Statement,
) -> Result<Option<(Option<Expression>, GeneratorResumeAction)>> {
    if statement_contains_yield(statement) {
        bail!("yield lồng trong control-flow/expression cần generator CFG continuation lowering")
    }
    Ok(None)
}

pub(super) fn statement_contains_yield(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            expression_contains_yield(value)
        }
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|declaration| declaration.init.as_ref())
            .any(expression_contains_yield),
        StatementKind::Block(body) => body.iter().any(statement_contains_yield),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression_contains_yield(test)
                || statement_contains_yield(consequent)
                || alternate.as_deref().is_some_and(statement_contains_yield)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression_contains_yield(test) || statement_contains_yield(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ecmora_hir::ForInit::Expression(value) => expression_contains_yield(value),
                ecmora_hir::ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|declaration| declaration.init.as_ref())
                    .any(expression_contains_yield),
            }) || test.as_ref().is_some_and(expression_contains_yield)
                || update.as_ref().is_some_and(expression_contains_yield)
                || statement_contains_yield(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expression_contains_yield(right) || statement_contains_yield(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expression_contains_yield(discriminant)
                || cases.iter().any(|case| {
                    case.test.as_ref().is_some_and(expression_contains_yield)
                        || case.consequent.iter().any(statement_contains_yield)
                })
        }
        StatementKind::FunctionDeclaration(_) => false,
        StatementKind::Return(value) => value.as_ref().is_some_and(expression_contains_yield),
        StatementKind::Break | StatementKind::Continue => false,
    }
}

fn expression_contains_yield(expression: &Expression) -> bool {
    if yield_call(expression).is_some() {
        return true;
    }
    match &expression.kind {
        ExpressionKind::Member { object, property } => {
            expression_contains_yield(object)
                || matches!(
                    property,
                    ecmora_hir::MemberProperty::Computed(value)
                        if expression_contains_yield(value)
                )
        }
        ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
            ecmora_hir::ObjectEntry::Property(property) => {
                matches!(
                    &property.key,
                    ecmora_hir::MemberProperty::Computed(value)
                        if expression_contains_yield(value)
                ) || expression_contains_yield(&property.value)
            }
            ecmora_hir::ObjectEntry::Spread(value) => expression_contains_yield(value),
            ecmora_hir::ObjectEntry::Accessor { get, set, .. } => {
                get.as_ref().is_some_and(expression_contains_yield)
                    || set.as_ref().is_some_and(expression_contains_yield)
            }
        }),
        ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
            ecmora_hir::ArrayElement::Expression(value)
            | ecmora_hir::ArrayElement::Spread(value) => expression_contains_yield(value),
            ecmora_hir::ArrayElement::Hole => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            expression_contains_yield(test)
                || expression_contains_yield(consequent)
                || expression_contains_yield(alternate)
        }
        ExpressionKind::Unary { argument, .. } => expression_contains_yield(argument),
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            expression_contains_yield(left) || expression_contains_yield(right)
        }
        ExpressionKind::Assignment { target, value, .. } => {
            target_contains_yield(target) || expression_contains_yield(value)
        }
        ExpressionKind::Update { target, .. } => target_contains_yield(target),
        ExpressionKind::Call { callee, arguments } | ExpressionKind::New { callee, arguments } => {
            expression_contains_yield(callee) || arguments.iter().any(expression_contains_yield)
        }
        ExpressionKind::Await(value) => expression_contains_yield(value),
        ExpressionKind::Function(_)
        | ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This
        | ExpressionKind::Global(_) => false,
    }
}

fn target_contains_yield(target: &AssignmentTarget) -> bool {
    match target {
        AssignmentTarget::Identifier(_) => false,
        AssignmentTarget::Member { object, property } => {
            expression_contains_yield(object)
                || matches!(
                    property,
                    ecmora_hir::MemberProperty::Computed(value)
                        if expression_contains_yield(value)
                )
        }
    }
}
