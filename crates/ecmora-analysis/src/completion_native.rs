use anyhow::{Result, bail};
use ecmora_hir::{
    CatchClause, Expression, ExpressionKind, Program, Span, Statement, StatementKind, SwitchCase,
    VariableDeclarator, VariableKind,
};
use std::collections::HashSet;

/// Erase try/catch/finally into ordinary structured control flow before typed SSA.
///
/// The transform uses **edge cloning**, not a tagged completion runtime:
/// - every syntactic throw into a catch clones the catch body at that throw edge,
///   preserving the exact thrown SSA type;
/// - every abrupt edge that leaves a try/finally clones the finalizer before the
///   original Return/Throw/Break/Continue;
/// - normal completion appends one finalizer clone;
/// - an abrupt finalizer naturally overrides the pending completion because the
///   cloned finalizer terminates before the old completion is reached.
///
/// Exception-bearing local functions are forced through static_graph inlining before
/// this pass, so explicit throws from a called local function are visible at the caller
/// try site. No C unwinder or tagged Completion object is introduced.
pub(super) fn lower(program: &Program) -> Result<Program> {
    let mut lowerer = Lowerer { next_id: 0 };
    let statements = lowerer.statements(&program.statements)?;
    validate_no_try(&statements)?;
    let mut output = program.clone();
    output.statements = statements;
    Ok(output)
}

struct Lowerer {
    next_id: u32,
}

#[derive(Default, Clone)]
struct ControlScope {
    breakable: usize,
    continuable: usize,
    labels: HashSet<String>,
}

impl Lowerer {
    fn fresh(&mut self, hint: &str) -> String {
        let id = self.next_id;
        self.next_id += 1;
        format!("@completion_{}_{}", hint, id)
    }

    fn statements(&mut self, statements: &[Statement]) -> Result<Vec<Statement>> {
        statements
            .iter()
            .map(|statement| self.statement(statement))
            .collect::<Result<Vec<_>>>()
    }

    fn statement(&mut self, statement: &Statement) -> Result<Statement> {
        let span = statement.span;
        Ok(match &statement.kind {
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => self.lower_try(block, handler.as_ref(), finalizer.as_deref(), span)?,
            StatementKind::Block(body) => Statement {
                kind: StatementKind::Block(self.statements(body)?),
                span,
            },
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => Statement {
                kind: StatementKind::If {
                    test: test.clone(),
                    consequent: Box::new(self.statement(consequent)?),
                    alternate: alternate
                        .as_deref()
                        .map(|value| self.statement(value).map(Box::new))
                        .transpose()?,
                },
                span,
            },
            StatementKind::While { test, body } => Statement {
                kind: StatementKind::While {
                    test: test.clone(),
                    body: Box::new(self.statement(body)?),
                },
                span,
            },
            StatementKind::DoWhile { body, test } => Statement {
                kind: StatementKind::DoWhile {
                    body: Box::new(self.statement(body)?),
                    test: test.clone(),
                },
                span,
            },
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => Statement {
                kind: StatementKind::For {
                    init: init.clone(),
                    test: test.clone(),
                    update: update.clone(),
                    body: Box::new(self.statement(body)?),
                },
                span,
            },
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => Statement {
                kind: StatementKind::ForIn {
                    name: name.clone(),
                    kind: *kind,
                    right: right.clone(),
                    body: Box::new(self.statement(body)?),
                },
                span,
            },
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => Statement {
                kind: StatementKind::ForOf {
                    name: name.clone(),
                    kind: *kind,
                    right: right.clone(),
                    body: Box::new(self.statement(body)?),
                },
                span,
            },
            StatementKind::Switch {
                discriminant,
                cases,
            } => Statement {
                kind: StatementKind::Switch {
                    discriminant: discriminant.clone(),
                    cases: cases
                        .iter()
                        .map(|case| {
                            Ok(SwitchCase {
                                test: case.test.clone(),
                                consequent: self.statements(&case.consequent)?,
                                span: case.span,
                            })
                        })
                        .collect::<Result<_>>()?,
                },
                span,
            },
            StatementKind::Labeled { label, body } => Statement {
                kind: StatementKind::Labeled {
                    label: label.clone(),
                    body: Box::new(self.statement(body)?),
                },
                span,
            },
            StatementKind::FunctionDeclaration(function) => {
                let mut function = function.clone();
                function.body = self.statements(&function.body)?;
                Statement {
                    kind: StatementKind::FunctionDeclaration(function),
                    span,
                }
            }
            _ => statement.clone(),
        })
    }

    fn lower_try(
        &mut self,
        block: &Statement,
        handler: Option<&CatchClause>,
        finalizer: Option<&Statement>,
        span: Span,
    ) -> Result<Statement> {
        let exit_label = self.fresh("try_exit");
        let normalized_finalizer = finalizer.map(|value| self.statement(value)).transpose()?;
        let normalized_handler = handler
            .map(|handler| -> Result<CatchClause> {
                Ok(CatchClause {
                    parameter: handler.parameter.clone(),
                    body: Box::new(self.statement(&handler.body)?),
                    span: handler.span,
                })
            })
            .transpose()?;
        let normalized_block = self.statement(block)?;

        let caught = if let Some(handler) = normalized_handler.as_ref() {
            self.replace_caught_throws(
                &normalized_block,
                handler,
                &exit_label,
                &ControlScope::default(),
            )?
        } else {
            normalized_block
        };

        let mut body = if let Some(finalizer) = normalized_finalizer.as_ref() {
            self.instrument_finally(&caught, finalizer, &ControlScope::default())?
        } else {
            caught
        };

        if let Some(finalizer) = normalized_finalizer {
            body = append_on_normal(body, finalizer, span);
        }

        Ok(Statement {
            kind: StatementKind::Labeled {
                label: exit_label,
                body: Box::new(body),
            },
            span,
        })
    }

    fn replace_caught_throws(
        &mut self,
        statement: &Statement,
        handler: &CatchClause,
        exit_label: &str,
        scope: &ControlScope,
    ) -> Result<Statement> {
        let span = statement.span;
        Ok(match &statement.kind {
            StatementKind::Throw(value) => {
                let thrown_name = self.fresh("throw");
                let mut body = vec![variable_statement(
                    VariableKind::Let,
                    thrown_name.clone(),
                    Some(value.clone()),
                    span,
                )];

                let catch_body = if let StatementKind::Block(body) = &handler.body.kind {
                    body.clone()
                } else {
                    vec![(*handler.body).clone()]
                };
                let mut catch_block = Vec::new();
                if let Some(parameter) = &handler.parameter {
                    catch_block.push(variable_statement(
                        VariableKind::Let,
                        parameter.clone(),
                        Some(global_expression(&thrown_name, span)),
                        handler.span,
                    ));
                }
                catch_block.extend(catch_body);
                let catch_statement = Statement {
                    kind: StatementKind::Block(catch_block),
                    span: handler.span,
                };
                // Finally is applied once, structurally, to the whole caught
                // body by lower_try. In particular the synthetic break below is
                // an abrupt edge leaving the try and therefore receives exactly
                // one finalizer clone. Catch-local cloning here would double-run it.
                body.push(catch_statement);
                body.push(Statement {
                    kind: StatementKind::Break(Some(exit_label.to_owned())),
                    span,
                });
                Statement {
                    kind: StatementKind::Block(body),
                    span,
                }
            }
            StatementKind::Block(body) => Statement {
                kind: StatementKind::Block(
                    body.iter()
                        .map(|value| self.replace_caught_throws(value, handler, exit_label, scope))
                        .collect::<Result<_>>()?,
                ),
                span,
            },
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => Statement {
                kind: StatementKind::If {
                    test: test.clone(),
                    consequent: Box::new(
                        self.replace_caught_throws(consequent, handler, exit_label, scope)?,
                    ),
                    alternate: alternate
                        .as_deref()
                        .map(|value| {
                            self.replace_caught_throws(value, handler, exit_label, scope)
                                .map(Box::new)
                        })
                        .transpose()?,
                },
                span,
            },
            StatementKind::While { test, body } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::While {
                        test: test.clone(),
                        body: Box::new(
                            self.replace_caught_throws(body, handler, exit_label, &nested)?,
                        ),
                    },
                    span,
                }
            }
            StatementKind::DoWhile { body, test } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::DoWhile {
                        body: Box::new(
                            self.replace_caught_throws(body, handler, exit_label, &nested)?,
                        ),
                        test: test.clone(),
                    },
                    span,
                }
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::For {
                        init: init.clone(),
                        test: test.clone(),
                        update: update.clone(),
                        body: Box::new(
                            self.replace_caught_throws(body, handler, exit_label, &nested)?,
                        ),
                    },
                    span,
                }
            }
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::ForIn {
                        name: name.clone(),
                        kind: *kind,
                        right: right.clone(),
                        body: Box::new(
                            self.replace_caught_throws(body, handler, exit_label, &nested)?,
                        ),
                    },
                    span,
                }
            }
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::ForOf {
                        name: name.clone(),
                        kind: *kind,
                        right: right.clone(),
                        body: Box::new(
                            self.replace_caught_throws(body, handler, exit_label, &nested)?,
                        ),
                    },
                    span,
                }
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                Statement {
                    kind: StatementKind::Switch {
                        discriminant: discriminant.clone(),
                        cases: cases
                            .iter()
                            .map(|case| {
                                Ok(SwitchCase {
                                    test: case.test.clone(),
                                    consequent: case
                                        .consequent
                                        .iter()
                                        .map(|value| {
                                            self.replace_caught_throws(
                                                value, handler, exit_label, &nested,
                                            )
                                        })
                                        .collect::<Result<_>>()?,
                                    span: case.span,
                                })
                            })
                            .collect::<Result<_>>()?,
                    },
                    span,
                }
            }
            StatementKind::Labeled { label, body } => {
                let mut nested = scope.clone();
                nested.labels.insert(label.clone());
                Statement {
                    kind: StatementKind::Labeled {
                        label: label.clone(),
                        body: Box::new(
                            self.replace_caught_throws(body, handler, exit_label, &nested)?,
                        ),
                    },
                    span,
                }
            }
            StatementKind::Try { .. } => self.statement(statement)?,
            StatementKind::FunctionDeclaration(_) => statement.clone(),
            _ => statement.clone(),
        })
    }

    fn instrument_finally(
        &mut self,
        statement: &Statement,
        finalizer: &Statement,
        scope: &ControlScope,
    ) -> Result<Statement> {
        let span = statement.span;
        Ok(match &statement.kind {
            StatementKind::Return(value) => {
                let mut body = Vec::new();
                let value = if let Some(value) = value {
                    let temp = self.fresh("return");
                    body.push(variable_statement(
                        VariableKind::Let,
                        temp.clone(),
                        Some(value.clone()),
                        span,
                    ));
                    Some(global_expression(&temp, span))
                } else {
                    None
                };
                body.push(finalizer.clone());
                body.push(Statement {
                    kind: StatementKind::Return(value),
                    span,
                });
                Statement {
                    kind: StatementKind::Block(body),
                    span,
                }
            }
            StatementKind::Throw(value) => {
                let temp = self.fresh("throw");
                Statement {
                    kind: StatementKind::Block(vec![
                        variable_statement(
                            VariableKind::Let,
                            temp.clone(),
                            Some(value.clone()),
                            span,
                        ),
                        finalizer.clone(),
                        Statement {
                            kind: StatementKind::Throw(global_expression(&temp, span)),
                            span,
                        },
                    ]),
                    span,
                }
            }
            StatementKind::Break(label) if break_exits_scope(label.as_deref(), scope) => {
                Statement {
                    kind: StatementKind::Block(vec![
                        finalizer.clone(),
                        Statement {
                            kind: StatementKind::Break(label.clone()),
                            span,
                        },
                    ]),
                    span,
                }
            }
            StatementKind::Continue(label) if continue_exits_scope(label.as_deref(), scope) => {
                Statement {
                    kind: StatementKind::Block(vec![
                        finalizer.clone(),
                        Statement {
                            kind: StatementKind::Continue(label.clone()),
                            span,
                        },
                    ]),
                    span,
                }
            }
            StatementKind::Block(body) => Statement {
                kind: StatementKind::Block(
                    body.iter()
                        .map(|value| self.instrument_finally(value, finalizer, scope))
                        .collect::<Result<_>>()?,
                ),
                span,
            },
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => Statement {
                kind: StatementKind::If {
                    test: test.clone(),
                    consequent: Box::new(self.instrument_finally(consequent, finalizer, scope)?),
                    alternate: alternate
                        .as_deref()
                        .map(|value| {
                            self.instrument_finally(value, finalizer, scope)
                                .map(Box::new)
                        })
                        .transpose()?,
                },
                span,
            },
            StatementKind::While { test, body } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::While {
                        test: test.clone(),
                        body: Box::new(self.instrument_finally(body, finalizer, &nested)?),
                    },
                    span,
                }
            }
            StatementKind::DoWhile { body, test } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::DoWhile {
                        body: Box::new(self.instrument_finally(body, finalizer, &nested)?),
                        test: test.clone(),
                    },
                    span,
                }
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::For {
                        init: init.clone(),
                        test: test.clone(),
                        update: update.clone(),
                        body: Box::new(self.instrument_finally(body, finalizer, &nested)?),
                    },
                    span,
                }
            }
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::ForIn {
                        name: name.clone(),
                        kind: *kind,
                        right: right.clone(),
                        body: Box::new(self.instrument_finally(body, finalizer, &nested)?),
                    },
                    span,
                }
            }
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                nested.continuable += 1;
                Statement {
                    kind: StatementKind::ForOf {
                        name: name.clone(),
                        kind: *kind,
                        right: right.clone(),
                        body: Box::new(self.instrument_finally(body, finalizer, &nested)?),
                    },
                    span,
                }
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                let mut nested = scope.clone();
                nested.breakable += 1;
                Statement {
                    kind: StatementKind::Switch {
                        discriminant: discriminant.clone(),
                        cases: cases
                            .iter()
                            .map(|case| {
                                Ok(SwitchCase {
                                    test: case.test.clone(),
                                    consequent: case
                                        .consequent
                                        .iter()
                                        .map(|value| {
                                            self.instrument_finally(value, finalizer, &nested)
                                        })
                                        .collect::<Result<_>>()?,
                                    span: case.span,
                                })
                            })
                            .collect::<Result<_>>()?,
                    },
                    span,
                }
            }
            StatementKind::Labeled { label, body } => {
                let mut nested = scope.clone();
                nested.labels.insert(label.clone());
                Statement {
                    kind: StatementKind::Labeled {
                        label: label.clone(),
                        body: Box::new(self.instrument_finally(body, finalizer, &nested)?),
                    },
                    span,
                }
            }
            StatementKind::Try { .. } => {
                let normalized = self.statement(statement)?;
                self.instrument_finally(&normalized, finalizer, scope)?
            }
            StatementKind::FunctionDeclaration(_) => statement.clone(),
            _ => statement.clone(),
        })
    }
}

fn break_exits_scope(label: Option<&str>, scope: &ControlScope) -> bool {
    match label {
        Some(label) => !scope.labels.contains(label),
        None => scope.breakable == 0,
    }
}

fn continue_exits_scope(label: Option<&str>, scope: &ControlScope) -> bool {
    match label {
        Some(label) => !scope.labels.contains(label),
        None => scope.continuable == 0,
    }
}

fn append_on_normal(statement: Statement, finalizer: Statement, span: Span) -> Statement {
    match statement.kind {
        StatementKind::Block(mut body) => {
            body.push(finalizer);
            Statement {
                kind: StatementKind::Block(body),
                span,
            }
        }
        kind => Statement {
            kind: StatementKind::Block(vec![Statement { kind, span }, finalizer]),
            span,
        },
    }
}

fn variable_statement(
    kind: VariableKind,
    name: String,
    init: Option<Expression>,
    span: Span,
) -> Statement {
    Statement {
        kind: StatementKind::VariableDeclaration {
            kind,
            declarations: vec![VariableDeclarator { name, init, span }],
        },
        span,
    }
}

fn global_expression(name: &str, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Global(name.to_owned()),
        span,
    }
}

fn validate_no_try(statements: &[Statement]) -> Result<()> {
    fn walk_statement(statement: &Statement) -> Result<()> {
        match &statement.kind {
            StatementKind::Try { .. } => bail!("try/catch/finally survived completion lowering"),
            StatementKind::Block(body) => {
                for value in body {
                    walk_statement(value)?;
                }
            }
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                walk_statement(consequent)?;
                if let Some(value) = alternate {
                    walk_statement(value)?;
                }
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::For { body, .. }
            | StatementKind::ForIn { body, .. }
            | StatementKind::ForOf { body, .. }
            | StatementKind::Labeled { body, .. } => walk_statement(body)?,
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    for value in &case.consequent {
                        walk_statement(value)?;
                    }
                }
            }
            StatementKind::FunctionDeclaration(function) => {
                for value in &function.body {
                    walk_statement(value)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    for value in statements {
        walk_statement(value)?;
    }
    Ok(())
}
