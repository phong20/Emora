use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentTarget, Expression, ExpressionKind, ForInit, Function, MemberProperty,
    ObjectEntry, Span, Statement, StatementKind, VariableDeclarator, VariableKind,
};

/// Lift nested await expressions into explicit top-level await boundaries.
///
/// The native async lowerer is continuation-oriented. Keeping this transform in
/// HIR preserves evaluation order while allowing ordinary typed specialization
/// to continue after each suspension point.
pub(super) fn normalize_async_function(function: &Function) -> Result<Function> {
    if !function.r#async {
        return Ok(function.clone());
    }
    let mut next_helper = 0_u32;
    let body = normalize_statements(&function.body, &mut next_helper)?;
    let mut function = function.clone();
    function.body = body;
    Ok(function)
}

fn normalize_statements(statements: &[Statement], next_helper: &mut u32) -> Result<Vec<Statement>> {
    let mut output = Vec::new();
    for statement in statements {
        normalize_statement(statement, next_helper, &mut output)?;
    }
    Ok(output)
}

fn normalize_statement(
    statement: &Statement,
    next_helper: &mut u32,
    output: &mut Vec<Statement>,
) -> Result<()> {
    match &statement.kind {
        StatementKind::VariableDeclaration { kind, declarations } => {
            let mut rewritten = Vec::new();
            for declaration in declarations {
                let Some(initializer) = &declaration.init else {
                    rewritten.push(declaration.clone());
                    continue;
                };
                if !contains_await_expression(initializer)
                    || matches!(&initializer.kind, ExpressionKind::Await(_))
                {
                    rewritten.push(declaration.clone());
                    continue;
                }
                let call = make_async_helper_call(
                    vec![Statement {
                        kind: StatementKind::Return(Some(initializer.clone())),
                        span: initializer.span,
                    }],
                    statement.span,
                    next_helper,
                    output,
                );
                rewritten.push(VariableDeclarator {
                    name: declaration.name.clone(),
                    init: Some(Expression {
                        kind: ExpressionKind::Await(Box::new(call)),
                        span: initializer.span,
                    }),
                    span: declaration.span,
                });
            }
            output.push(Statement {
                kind: StatementKind::VariableDeclaration {
                    kind: *kind,
                    declarations: rewritten,
                },
                span: statement.span,
            });
        }
        StatementKind::Return(Some(expression))
            if contains_await_expression(expression)
                && !matches!(&expression.kind, ExpressionKind::Await(_)) =>
        {
            let call = make_async_helper_call(
                vec![Statement {
                    kind: StatementKind::Return(Some(expression.clone())),
                    span: expression.span,
                }],
                statement.span,
                next_helper,
                output,
            );
            output.push(Statement {
                kind: StatementKind::Return(Some(Expression {
                    kind: ExpressionKind::Await(Box::new(call)),
                    span: expression.span,
                })),
                span: statement.span,
            });
        }
        StatementKind::Expression(expression)
            if contains_await_expression(expression)
                && !matches!(&expression.kind, ExpressionKind::Await(_)) =>
        {
            let call = make_async_helper_call(
                vec![Statement {
                    kind: StatementKind::Return(Some(expression.clone())),
                    span: expression.span,
                }],
                statement.span,
                next_helper,
                output,
            );
            output.push(Statement {
                kind: StatementKind::Expression(Expression {
                    kind: ExpressionKind::Await(Box::new(call)),
                    span: expression.span,
                }),
                span: statement.span,
            });
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } if contains_await_statement(statement) => {
            if contains_cross_boundary_abrupt(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(contains_cross_boundary_abrupt)
            {
                bail!(
                    "await trong if có return/break/continue vượt helper boundary; \
                     dùng compatibility interpreter"
                )
            }

            let then_call = make_async_helper_call(
                vec![(**consequent).clone()],
                consequent.span,
                next_helper,
                output,
            );
            let else_call = make_async_helper_call(
                alternate
                    .as_deref()
                    .map(|statement| vec![statement.clone()])
                    .unwrap_or_default(),
                alternate
                    .as_deref()
                    .map_or(statement.span, |value| value.span),
                next_helper,
                output,
            );
            let branch = Expression {
                kind: ExpressionKind::Conditional {
                    test: Box::new(test.clone()),
                    consequent: Box::new(then_call),
                    alternate: Box::new(else_call),
                },
                span: statement.span,
            };
            output.push(Statement {
                kind: StatementKind::Expression(Expression {
                    kind: ExpressionKind::Await(Box::new(branch)),
                    span: statement.span,
                }),
                span: statement.span,
            });
        }
        StatementKind::Block(body) if body.iter().any(contains_await_statement) => {
            if body.iter().any(contains_cross_boundary_abrupt) {
                bail!(
                    "await trong block có abrupt completion vượt helper boundary; \
                     dùng compatibility interpreter"
                )
            }
            let call = make_async_helper_call(body.clone(), statement.span, next_helper, output);
            output.push(Statement {
                kind: StatementKind::Expression(Expression {
                    kind: ExpressionKind::Await(Box::new(call)),
                    span: statement.span,
                }),
                span: statement.span,
            });
        }
        StatementKind::While { .. } | StatementKind::DoWhile { .. } | StatementKind::For { .. }
            if contains_await_statement(statement) =>
        {
            bail!("await trong loop cần compatibility interpreter")
        }
        StatementKind::Labeled { .. } if contains_await_statement(statement) => {
            bail!("await crossing a labeled statement uses compatibility completion state")
        }
        StatementKind::Try { .. } if contains_await_statement(statement) => {
            bail!("await in try/catch/finally uses compatibility completion state")
        }
        _ => output.push(statement.clone()),
    }
    Ok(())
}

fn make_async_helper_call(
    body: Vec<Statement>,
    span: Span,
    next_helper: &mut u32,
    output: &mut Vec<Statement>,
) -> Expression {
    let name = format!("@async.lift.{}", *next_helper);
    *next_helper += 1;
    output.push(Statement {
        kind: StatementKind::VariableDeclaration {
            kind: VariableKind::Const,
            declarations: vec![VariableDeclarator {
                name: name.clone(),
                init: Some(Expression {
                    kind: ExpressionKind::Function(Function {
                        name: None,
                        parameters: Vec::new(),
                        body,
                        r#async: true,
                        generator: false,
                        arrow: true,
                        lowering_error: None,
                    }),
                    span,
                }),
                span,
            }],
        },
        span,
    });
    Expression {
        kind: ExpressionKind::Call {
            callee: Box::new(Expression {
                kind: ExpressionKind::Global(name),
                span,
            }),
            arguments: Vec::new(),
        },
        span,
    }
}

fn contains_cross_boundary_abrupt(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Return(_) | StatementKind::Break(_) | StatementKind::Continue(_) => true,
        StatementKind::Block(body) => body.iter().any(contains_cross_boundary_abrupt),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            contains_cross_boundary_abrupt(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(contains_cross_boundary_abrupt)
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. } => contains_cross_boundary_abrupt(body),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|case| &case.consequent)
            .any(contains_cross_boundary_abrupt),
        StatementKind::Labeled { body, .. } => contains_cross_boundary_abrupt(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            contains_cross_boundary_abrupt(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| contains_cross_boundary_abrupt(&handler.body))
                || finalizer
                    .as_deref()
                    .is_some_and(contains_cross_boundary_abrupt)
        }
        StatementKind::FunctionDeclaration(_) => false,
        _ => false,
    }
}

fn contains_await_statement(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            contains_await_expression(value)
        }
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|declaration| declaration.init.as_ref())
            .any(contains_await_expression),
        StatementKind::Block(body) => body.iter().any(contains_await_statement),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            contains_await_expression(test)
                || contains_await_statement(consequent)
                || alternate.as_deref().is_some_and(contains_await_statement)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            contains_await_expression(test) || contains_await_statement(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => contains_await_expression(value),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|value| value.init.as_ref())
                    .any(contains_await_expression),
            }) || test.as_ref().is_some_and(contains_await_expression)
                || update.as_ref().is_some_and(contains_await_expression)
                || contains_await_statement(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            contains_await_expression(right) || contains_await_statement(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            contains_await_expression(discriminant)
                || cases.iter().any(|case| {
                    case.test.as_ref().is_some_and(contains_await_expression)
                        || case.consequent.iter().any(contains_await_statement)
                })
        }
        StatementKind::Labeled { body, .. } => contains_await_statement(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            contains_await_statement(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| contains_await_statement(&handler.body))
                || finalizer.as_deref().is_some_and(contains_await_statement)
        }
        StatementKind::Return(value) => value.as_ref().is_some_and(contains_await_expression),
        StatementKind::FunctionDeclaration(_) => false,
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn contains_await_expression(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Await(_) => true,
        ExpressionKind::Member { object, property } => {
            contains_await_expression(object)
                || matches!(
                    property,
                    MemberProperty::Computed(value) if contains_await_expression(value)
                )
        }
        ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
            ObjectEntry::Property(property) => {
                matches!(
                    &property.key,
                    MemberProperty::Computed(value) if contains_await_expression(value)
                ) || contains_await_expression(&property.value)
            }
            ObjectEntry::Spread(value) => contains_await_expression(value),
            ObjectEntry::Accessor { get, set, .. } => {
                get.as_ref().is_some_and(contains_await_expression)
                    || set.as_ref().is_some_and(contains_await_expression)
            }
        }),
        ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
            ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                contains_await_expression(value)
            }
            ArrayElement::Hole => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            contains_await_expression(test)
                || contains_await_expression(consequent)
                || contains_await_expression(alternate)
        }
        ExpressionKind::Unary { argument, .. } => contains_await_expression(argument),
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            contains_await_expression(left) || contains_await_expression(right)
        }
        ExpressionKind::Assignment { target, value, .. } => {
            contains_await_target(target) || contains_await_expression(value)
        }
        ExpressionKind::Update { target, .. } => contains_await_target(target),
        ExpressionKind::Call { callee, arguments } | ExpressionKind::New { callee, arguments } => {
            contains_await_expression(callee) || arguments.iter().any(contains_await_expression)
        }
        ExpressionKind::Function(_) => false,
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This
        | ExpressionKind::Global(_) => false,
    }
}

fn contains_await_target(target: &AssignmentTarget) -> bool {
    match target {
        AssignmentTarget::Identifier(_) => false,
        AssignmentTarget::Member { object, property } => {
            contains_await_expression(object)
                || matches!(
                    property,
                    MemberProperty::Computed(value) if contains_await_expression(value)
                )
        }
    }
}
