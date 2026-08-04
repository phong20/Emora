use anyhow::{Result, bail};
use ecmora_hir::{
    AssignmentOperator, AssignmentTarget, Expression, ExpressionKind, ForInit, Function, Program,
    Statement, StatementKind, VariableDeclarator, VariableKind,
};
use std::collections::HashSet;

pub(crate) fn normalize_var_hoisting(mut program: Program) -> Result<Program> {
    let top_level_functions = function_declaration_names(&program.statements);
    normalize_function_scope(&mut program.statements, &top_level_functions)?;
    for subclass in &mut program.promise_subclasses {
        if let Some(constructor) = &mut subclass.constructor {
            normalize_function(constructor)?;
        }
        for method in &mut subclass.methods {
            normalize_function(&mut method.function)?;
        }
    }
    Ok(program)
}

fn normalize_function(function: &mut Function) -> Result<()> {
    let mut existing = function.parameters.iter().cloned().collect::<HashSet<_>>();
    if let Some(name) = &function.name {
        existing.insert(name.clone());
    }
    existing.extend(function_declaration_names(&function.body));
    normalize_function_scope(&mut function.body, &existing)
}

fn function_declaration_names(statements: &[Statement]) -> HashSet<String> {
    statements
        .iter()
        .filter_map(|statement| match &statement.kind {
            StatementKind::FunctionDeclaration(function) => function.name.clone(),
            _ => None,
        })
        .collect()
}

fn normalize_function_scope(
    statements: &mut Vec<Statement>,
    existing_bindings: &HashSet<String>,
) -> Result<()> {
    let mut names = Vec::new();
    let mut seen = HashSet::new();
    collect_var_names(statements, &mut names, &mut seen);

    let lexical = statements
        .iter()
        .filter_map(|statement| match &statement.kind {
            StatementKind::VariableDeclaration {
                kind: VariableKind::Let | VariableKind::Const,
                declarations,
            } => Some(
                declarations
                    .iter()
                    .map(|declaration| declaration.name.clone())
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect::<HashSet<_>>();
    if let Some(conflict) = names.iter().find(|name| lexical.contains(*name)) {
        bail!("`var {conflict}` xung đột lexical declaration cùng function scope")
    }

    let mut counter = 0_u32;
    let original = std::mem::take(statements);
    let mut rewritten = Vec::new();
    for statement in original {
        rewritten.extend(rewrite_statement(statement, &mut counter)?);
    }

    names.retain(|name| !existing_bindings.contains(name));

    if !names.is_empty() {
        let span = rewritten
            .first()
            .map_or(ecmora_hir::Span::new(0, 0), |statement| statement.span);
        let declarations = names
            .into_iter()
            .map(|name| VariableDeclarator {
                name,
                init: Some(Expression {
                    kind: ExpressionKind::Global("undefined".to_owned()),
                    span,
                }),
                span,
            })
            .collect();
        rewritten.insert(
            0,
            Statement {
                kind: StatementKind::VariableDeclaration {
                    kind: VariableKind::Let,
                    declarations,
                },
                span,
            },
        );
    }

    *statements = rewritten;
    Ok(())
}

fn collect_var_names(
    statements: &[Statement],
    names: &mut Vec<String>,
    seen: &mut HashSet<String>,
) {
    for statement in statements {
        match &statement.kind {
            StatementKind::VariableDeclaration {
                kind: VariableKind::Var,
                declarations,
            } => {
                for declaration in declarations {
                    if seen.insert(declaration.name.clone()) {
                        names.push(declaration.name.clone());
                    }
                }
            }
            StatementKind::Block(body) => collect_var_names(body, names, seen),
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                collect_var_names(std::slice::from_ref(consequent.as_ref()), names, seen);
                if let Some(alternate) = alternate {
                    collect_var_names(std::slice::from_ref(alternate.as_ref()), names, seen);
                }
            }
            StatementKind::While { body, .. } | StatementKind::DoWhile { body, .. } => {
                collect_var_names(std::slice::from_ref(body.as_ref()), names, seen)
            }
            StatementKind::For { init, body, .. } => {
                if let Some(ForInit::VariableDeclaration {
                    kind: VariableKind::Var,
                    declarations,
                }) = init
                {
                    for declaration in declarations {
                        if seen.insert(declaration.name.clone()) {
                            names.push(declaration.name.clone());
                        }
                    }
                }
                collect_var_names(std::slice::from_ref(body.as_ref()), names, seen);
            }
            StatementKind::ForIn {
                name,
                kind: VariableKind::Var,
                body,
                ..
            }
            | StatementKind::ForOf {
                name,
                kind: VariableKind::Var,
                body,
                ..
            } => {
                if seen.insert(name.clone()) {
                    names.push(name.clone());
                }
                collect_var_names(std::slice::from_ref(body.as_ref()), names, seen);
            }
            StatementKind::ForIn { body, .. } | StatementKind::ForOf { body, .. } => {
                collect_var_names(std::slice::from_ref(body.as_ref()), names, seen)
            }
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    collect_var_names(&case.consequent, names, seen);
                }
            }
            StatementKind::FunctionDeclaration(_)
            | StatementKind::Expression(_)
            | StatementKind::VariableDeclaration { .. }
            | StatementKind::Return(_)
            | StatementKind::Throw(_)
            | StatementKind::Break
            | StatementKind::Continue => {}
        }
    }
}

fn rewrite_statement(statement: Statement, counter: &mut u32) -> Result<Vec<Statement>> {
    let span = statement.span;
    match statement.kind {
        StatementKind::VariableDeclaration {
            kind: VariableKind::Var,
            declarations,
        } => Ok(declarations
            .into_iter()
            .filter_map(|declaration| {
                declaration
                    .init
                    .map(|value| assignment_statement(declaration.name, value, declaration.span))
            })
            .collect()),
        StatementKind::Block(body) => {
            let mut rewritten = Vec::new();
            for statement in body {
                rewritten.extend(rewrite_statement(statement, counter)?);
            }
            Ok(vec![Statement {
                kind: StatementKind::Block(rewritten),
                span,
            }])
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => Ok(vec![Statement {
            kind: StatementKind::If {
                test,
                consequent: Box::new(pack(rewrite_statement(*consequent, counter)?, span)),
                alternate: alternate
                    .map(|statement| rewrite_statement(*statement, counter))
                    .transpose()?
                    .map(|statements| Box::new(pack(statements, span))),
            },
            span,
        }]),
        StatementKind::While { test, body } => Ok(vec![Statement {
            kind: StatementKind::While {
                test,
                body: Box::new(pack(rewrite_statement(*body, counter)?, span)),
            },
            span,
        }]),
        StatementKind::DoWhile { body, test } => Ok(vec![Statement {
            kind: StatementKind::DoWhile {
                body: Box::new(pack(rewrite_statement(*body, counter)?, span)),
                test,
            },
            span,
        }]),
        StatementKind::For {
            init:
                Some(ForInit::VariableDeclaration {
                    kind: VariableKind::Var,
                    declarations,
                }),
            test,
            update,
            body,
        } => {
            let mut output = declarations
                .into_iter()
                .filter_map(|declaration| {
                    declaration.init.map(|value| {
                        assignment_statement(declaration.name, value, declaration.span)
                    })
                })
                .collect::<Vec<_>>();
            output.push(Statement {
                kind: StatementKind::For {
                    init: None,
                    test,
                    update,
                    body: Box::new(pack(rewrite_statement(*body, counter)?, span)),
                },
                span,
            });
            Ok(vec![Statement {
                kind: StatementKind::Block(output),
                span,
            }])
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => Ok(vec![Statement {
            kind: StatementKind::For {
                init,
                test,
                update,
                body: Box::new(pack(rewrite_statement(*body, counter)?, span)),
            },
            span,
        }]),
        StatementKind::ForIn {
            name,
            kind: VariableKind::Var,
            right,
            body,
        } => rewrite_var_for_each(name, right, *body, false, span, counter),
        StatementKind::ForOf {
            name,
            kind: VariableKind::Var,
            right,
            body,
        } => rewrite_var_for_each(name, right, *body, true, span, counter),
        StatementKind::ForIn {
            name,
            kind,
            right,
            body,
        } => Ok(vec![Statement {
            kind: StatementKind::ForIn {
                name,
                kind,
                right,
                body: Box::new(pack(rewrite_statement(*body, counter)?, span)),
            },
            span,
        }]),
        StatementKind::ForOf {
            name,
            kind,
            right,
            body,
        } => Ok(vec![Statement {
            kind: StatementKind::ForOf {
                name,
                kind,
                right,
                body: Box::new(pack(rewrite_statement(*body, counter)?, span)),
            },
            span,
        }]),
        StatementKind::Switch {
            discriminant,
            mut cases,
        } => {
            for case in &mut cases {
                let original = std::mem::take(&mut case.consequent);
                let mut rewritten = Vec::new();
                for statement in original {
                    rewritten.extend(rewrite_statement(statement, counter)?);
                }
                case.consequent = rewritten;
            }
            Ok(vec![Statement {
                kind: StatementKind::Switch {
                    discriminant,
                    cases,
                },
                span,
            }])
        }
        StatementKind::FunctionDeclaration(mut function) => {
            normalize_function(&mut function)?;
            Ok(vec![Statement {
                kind: StatementKind::FunctionDeclaration(function),
                span,
            }])
        }
        kind => Ok(vec![Statement { kind, span }]),
    }
}

fn rewrite_var_for_each(
    name: String,
    right: Expression,
    body: Statement,
    for_of: bool,
    span: ecmora_hir::Span,
    counter: &mut u32,
) -> Result<Vec<Statement>> {
    let temporary = format!("@var.iter.{}", *counter);
    *counter += 1;
    let mut body_statements = vec![assignment_statement(
        name,
        Expression {
            kind: ExpressionKind::Global(temporary.clone()),
            span,
        },
        span,
    )];
    body_statements.extend(rewrite_statement(body, counter)?);
    let body = Box::new(Statement {
        kind: StatementKind::Block(body_statements),
        span,
    });
    Ok(vec![Statement {
        kind: if for_of {
            StatementKind::ForOf {
                name: temporary,
                kind: VariableKind::Let,
                right,
                body,
            }
        } else {
            StatementKind::ForIn {
                name: temporary,
                kind: VariableKind::Let,
                right,
                body,
            }
        },
        span,
    }])
}

fn assignment_statement(name: String, value: Expression, span: ecmora_hir::Span) -> Statement {
    Statement {
        kind: StatementKind::Expression(Expression {
            kind: ExpressionKind::Assignment {
                target: AssignmentTarget::Identifier(name),
                operator: AssignmentOperator::Assign,
                value: Box::new(value),
            },
            span,
        }),
        span,
    }
}

fn pack(mut statements: Vec<Statement>, span: ecmora_hir::Span) -> Statement {
    match statements.len() {
        0 => Statement {
            kind: StatementKind::Block(Vec::new()),
            span,
        },
        1 => statements.pop().unwrap(),
        _ => Statement {
            kind: StatementKind::Block(statements),
            span,
        },
    }
}
