use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, ClassDeclaration,
    ClassElement, ClassKey, ClassMethodKind, Expression, ExpressionKind, ForInit, Function,
    MemberProperty, ObjectEntry, ObjectProperty, Program, Span, Statement, StatementKind,
    SwitchCase, VariableDeclarator, VariableKind,
};
use std::collections::{HashMap, HashSet};

/// Erase closed-world JavaScript class identity into the same static object/prototype
/// graph used by `static_graph`. No class/object runtime ABI is introduced here.
///
/// Class declarations become:
/// - one static prototype object,
/// - one static constructor object for static members,
/// - one synthetic prototype initializer method,
/// - one synthetic factory function used for `new C(...)`.
///
/// Private names are class-scoped unforgeable compiler keys (`@class_private_*`).
/// They never enter the runtime property namespace because `static_graph` erases the
/// corresponding objects before ecmora-ir.
pub(super) fn lower(program: &Program) -> Result<Program> {
    if program.classes.is_empty() {
        return Ok(program.clone());
    }

    let mut classes = HashMap::<String, ClassDeclaration>::new();
    for class in &program.classes {
        if classes.insert(class.name.clone(), class.clone()).is_some() {
            bail!("class `{}` được khai báo trùng", class.name)
        }
    }
    validate_class_graph(&classes)?;

    let exported = program
        .exports
        .iter()
        .map(|binding| binding.local.as_str())
        .collect::<HashSet<_>>();
    for class in &program.classes {
        if exported.contains(class.name.as_str()) {
            bail!(
                "exported class `{}` exposes constructor identity; closed-world native class lowering refuses runtime reification",
                class.name
            )
        }
    }

    let definitions = program
        .classes
        .iter()
        .map(|class| Ok((class.name.clone(), lower_class_definition(class, &classes)?)))
        .collect::<Result<HashMap<_, _>>>()?;

    let mut expanded = Vec::new();
    for statement in &program.statements {
        if let Some(name) = class_marker_statement(statement) {
            let definition = definitions
                .get(name)
                .ok_or_else(|| anyhow::anyhow!("class marker `{name}` has no metadata"))?;
            expanded.extend(definition.iter().cloned());
        } else {
            expanded.push(statement.clone());
        }
    }

    let mut rewriter = ClassUseRewriter { classes: &classes };
    let statements = expanded
        .iter()
        .map(|statement| rewriter.statement(statement, None))
        .collect::<Result<Vec<_>>>()?;

    validate_erased(&statements)?;

    let mut output = program.clone();
    output.statements = statements;
    output.classes.clear();
    Ok(output)
}

fn class_marker_statement(statement: &Statement) -> Option<&str> {
    let StatementKind::Expression(Expression {
        kind: ExpressionKind::Global(name),
        ..
    }) = &statement.kind
    else {
        return None;
    };
    name.strip_prefix("@class_declare_")
}

fn validate_class_graph(classes: &HashMap<String, ClassDeclaration>) -> Result<()> {
    for class in classes.values() {
        let mut current = class.parent.as_deref();
        let mut seen = HashSet::new();
        while let Some(name) = current {
            if name == "Object" {
                break;
            }
            if !seen.insert(name.to_owned()) {
                bail!("class inheritance cycle at `{}`", class.name)
            }
            let Some(parent) = classes.get(name) else {
                bail!(
                    "class `{}` extends runtime/unknown `{name}`; native closed-world class graph requires a local static base class",
                    class.name
                )
            };
            current = parent.parent.as_deref();
        }
    }
    Ok(())
}

fn lower_class_definition(
    class: &ClassDeclaration,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Vec<Statement>> {
    let span = class.span;
    let class_prototype_name = prototype_name(&class.name);
    let initializer_name = initializer_key(&class.name);
    let factory = factory_name(&class.name);

    let mut prototype_entries = Vec::new();
    for element in &class.elements {
        let ClassElement::Method {
            key,
            function,
            kind,
            r#static: false,
        } = element
        else {
            continue;
        };
        let key = lowered_key(&class.name, key);
        let function = rewrite_function_for_class(function, &class.name, classes)?;
        match kind {
            ClassMethodKind::Method => {
                prototype_entries.push(ObjectEntry::Property(ObjectProperty {
                    key: MemberProperty::Static(key),
                    value: Expression {
                        kind: ExpressionKind::Function(function),
                        span,
                    },
                }))
            }
            ClassMethodKind::Get => prototype_entries.push(ObjectEntry::Accessor {
                key,
                get: Some(Expression {
                    kind: ExpressionKind::Function(function),
                    span,
                }),
                set: None,
            }),
            ClassMethodKind::Set => prototype_entries.push(ObjectEntry::Accessor {
                key,
                get: None,
                set: Some(Expression {
                    kind: ExpressionKind::Function(function),
                    span,
                }),
            }),
        }
    }

    let initializer = build_initializer(class, classes)?;
    prototype_entries.push(ObjectEntry::Property(ObjectProperty {
        key: MemberProperty::Static(initializer_name.clone()),
        value: Expression {
            kind: ExpressionKind::Function(initializer),
            span,
        },
    }));

    let mut output = vec![variable_statement(
        VariableKind::Const,
        class_prototype_name.clone(),
        Some(Expression {
            kind: ExpressionKind::Object(prototype_entries),
            span,
        }),
        span,
    )];

    if let Some(parent) = &class.parent {
        if parent != "Object" {
            output.push(expression_statement(call_expression(
                member_expression(global_expression("Object", span), "setPrototypeOf", span),
                vec![
                    global_expression(&class_prototype_name, span),
                    global_expression(&prototype_name(parent), span),
                ],
                span,
            )));
        }
    }

    let mut class_entries = vec![ObjectEntry::Property(ObjectProperty {
        key: MemberProperty::Static("prototype".to_owned()),
        value: global_expression(&class_prototype_name, span),
    })];
    for element in &class.elements {
        match element {
            ClassElement::Method {
                key,
                function,
                kind,
                r#static: true,
            } => {
                let key = lowered_key(&class.name, key);
                let function = rewrite_function_for_class(function, &class.name, classes)?;
                match kind {
                    ClassMethodKind::Method => {
                        class_entries.push(ObjectEntry::Property(ObjectProperty {
                            key: MemberProperty::Static(key),
                            value: Expression {
                                kind: ExpressionKind::Function(function),
                                span,
                            },
                        }));
                    }
                    ClassMethodKind::Get => class_entries.push(ObjectEntry::Accessor {
                        key,
                        get: Some(Expression {
                            kind: ExpressionKind::Function(function),
                            span,
                        }),
                        set: None,
                    }),
                    ClassMethodKind::Set => class_entries.push(ObjectEntry::Accessor {
                        key,
                        get: None,
                        set: Some(Expression {
                            kind: ExpressionKind::Function(function),
                            span,
                        }),
                    }),
                }
            }
            _ => {}
        }
    }

    output.push(variable_statement(
        VariableKind::Const,
        class.name.clone(),
        Some(Expression {
            kind: ExpressionKind::Object(class_entries),
            span,
        }),
        span,
    ));

    // Static field initializers and static blocks execute in source order after
    // the constructor object exists. Methods/accessors are installed above as
    // class-definition metadata and do not reorder these observable effects.
    for element in &class.elements {
        match element {
            ClassElement::Field {
                key,
                value,
                r#static: true,
            } => {
                output.push(expression_statement(Expression {
                    kind: ExpressionKind::Assignment {
                        target: AssignmentTarget::Member {
                            object: Box::new(global_expression(&class.name, span)),
                            property: MemberProperty::Static(lowered_key(&class.name, key)),
                        },
                        operator: AssignmentOperator::Assign,
                        value: Box::new(match value {
                            Some(value) => rewrite_expression(value, &class.name, classes)?,
                            None => undefined_expression(span),
                        }),
                    },
                    span,
                }));
            }
            ClassElement::StaticBlock(body) => {
                for statement in body {
                    output.push(rewrite_statement_for_class(
                        statement,
                        &class.name,
                        classes,
                    )?);
                }
            }
            _ => {}
        }
    }

    let factory_function = Function {
        name: Some(factory.clone()),
        parameters: constructor_parameters(class, classes)?,
        body: vec![
            variable_statement(
                VariableKind::Const,
                instance_name(&class.name),
                Some(call_expression(
                    member_expression(global_expression("Object", span), "create", span),
                    vec![global_expression(&class_prototype_name, span)],
                    span,
                )),
                span,
            ),
            expression_statement(call_expression(
                member_expression(
                    global_expression(&instance_name(&class.name), span),
                    &initializer_name,
                    span,
                ),
                constructor_parameters(class, classes)?
                    .into_iter()
                    .map(|name| global_expression(&name, span))
                    .collect(),
                span,
            )),
            Statement {
                kind: StatementKind::Return(Some(global_expression(
                    &instance_name(&class.name),
                    span,
                ))),
                span,
            },
        ],
        r#async: false,
        generator: false,
        arrow: false,
        lowering_error: None,
    };
    output.push(Statement {
        kind: StatementKind::FunctionDeclaration(factory_function),
        span,
    });

    Ok(output)
}

fn constructor_parameters(
    class: &ClassDeclaration,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Vec<String>> {
    if let Some(constructor) = class.constructor.as_ref() {
        return Ok(constructor.parameters.clone());
    }
    if let Some(parent) = class.parent.as_deref().filter(|name| *name != "Object") {
        return constructor_parameters(&classes[parent], classes);
    }
    Ok(Vec::new())
}

fn build_initializer(
    class: &ClassDeclaration,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Function> {
    let span = class.span;
    let parameters = constructor_parameters(class, classes)?;
    let mut body = Vec::new();

    let parent = class.parent.as_deref().filter(|name| *name != "Object");
    let constructor = class.constructor.as_ref();

    if let Some(parent) = parent {
        if let Some(constructor) = constructor {
            let mut saw_super = false;
            for statement in &constructor.body {
                if let Some(arguments) = direct_super_call(statement) {
                    if saw_super {
                        bail!(
                            "derived constructor `{}` has multiple top-level super() calls",
                            class.name
                        )
                    }
                    saw_super = true;
                    body.push(expression_statement(call_expression(
                        member_expression(
                            Expression {
                                kind: ExpressionKind::This,
                                span,
                            },
                            &initializer_key(parent),
                            span,
                        ),
                        arguments
                            .iter()
                            .map(|value| rewrite_expression(value, &class.name, classes))
                            .collect::<Result<Vec<_>>>()?,
                        span,
                    )));
                    body.extend(instance_field_initializers(class, classes)?);
                    continue;
                }
                if statement_contains_super(statement) {
                    bail!(
                        "derived constructor `{}` uses super() in nested control flow; native class lowering requires CFG-aware super initialization",
                        class.name
                    )
                }
                body.push(rewrite_statement_for_class(
                    statement,
                    &class.name,
                    classes,
                )?);
            }
            if !saw_super {
                bail!(
                    "derived constructor `{}` does not execute super()",
                    class.name
                )
            }
        } else {
            body.push(expression_statement(call_expression(
                member_expression(
                    Expression {
                        kind: ExpressionKind::This,
                        span,
                    },
                    &initializer_key(parent),
                    span,
                ),
                parameters
                    .iter()
                    .map(|name| global_expression(name, span))
                    .collect(),
                span,
            )));
            body.extend(instance_field_initializers(class, classes)?);
        }
    } else {
        body.extend(instance_field_initializers(class, classes)?);
        if let Some(constructor) = constructor {
            if constructor.body.iter().any(statement_contains_super) {
                bail!("base constructor `{}` contains super()", class.name)
            }
            for statement in &constructor.body {
                if matches!(statement.kind, StatementKind::Return(Some(_))) {
                    bail!(
                        "constructor `{}` returns an explicit value; replacement-object constructor semantics need constructor-result identity SSA",
                        class.name
                    )
                }
                body.push(rewrite_statement_for_class(
                    statement,
                    &class.name,
                    classes,
                )?);
            }
        }
    }

    Ok(Function {
        name: Some(initializer_key(&class.name)),
        parameters,
        body,
        r#async: false,
        generator: false,
        arrow: false,
        lowering_error: None,
    })
}

fn instance_field_initializers(
    class: &ClassDeclaration,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Vec<Statement>> {
    let mut output = Vec::new();
    let span = class.span;
    output.push(expression_statement(Expression {
        kind: ExpressionKind::Assignment {
            target: AssignmentTarget::Member {
                object: Box::new(Expression {
                    kind: ExpressionKind::This,
                    span,
                }),
                property: MemberProperty::Static(brand_key(&class.name)),
            },
            operator: AssignmentOperator::Assign,
            value: Box::new(Expression {
                kind: ExpressionKind::Bool(true),
                span,
            }),
        },
        span,
    }));
    for element in &class.elements {
        if let ClassElement::Field {
            key,
            value,
            r#static: false,
        } = element
        {
            output.push(expression_statement(Expression {
                kind: ExpressionKind::Assignment {
                    target: AssignmentTarget::Member {
                        object: Box::new(Expression {
                            kind: ExpressionKind::This,
                            span,
                        }),
                        property: MemberProperty::Static(lowered_key(&class.name, key)),
                    },
                    operator: AssignmentOperator::Assign,
                    value: Box::new(match value {
                        Some(value) => rewrite_expression(value, &class.name, classes)?,
                        None => undefined_expression(span),
                    }),
                },
                span,
            }));
        }
    }
    Ok(output)
}

struct ClassUseRewriter<'a> {
    classes: &'a HashMap<String, ClassDeclaration>,
}

impl ClassUseRewriter<'_> {
    fn statement(
        &mut self,
        statement: &Statement,
        class_context: Option<&str>,
    ) -> Result<Statement> {
        rewrite_statement(statement, class_context, self.classes)
    }
}

fn rewrite_function_for_class(
    function: &Function,
    class_name: &str,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Function> {
    let mut function = function.clone();
    function.body = function
        .body
        .iter()
        .map(|statement| rewrite_statement(statement, Some(class_name), classes))
        .collect::<Result<Vec<_>>>()?;
    Ok(function)
}

fn rewrite_statement_for_class(
    statement: &Statement,
    class_name: &str,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Statement> {
    rewrite_statement(statement, Some(class_name), classes)
}

fn rewrite_statement(
    statement: &Statement,
    class_context: Option<&str>,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Statement> {
    let span = statement.span;
    let kind = match &statement.kind {
        StatementKind::Expression(value) => {
            StatementKind::Expression(rewrite_expression_ctx(value, class_context, classes)?)
        }
        StatementKind::VariableDeclaration { kind, declarations } => {
            StatementKind::VariableDeclaration {
                kind: *kind,
                declarations: declarations
                    .iter()
                    .map(|declaration| {
                        Ok(VariableDeclarator {
                            name: declaration.name.clone(),
                            init: declaration
                                .init
                                .as_ref()
                                .map(|value| rewrite_expression_ctx(value, class_context, classes))
                                .transpose()?,
                            span: declaration.span,
                        })
                    })
                    .collect::<Result<_>>()?,
            }
        }
        StatementKind::Block(body) => StatementKind::Block(
            body.iter()
                .map(|statement| rewrite_statement(statement, class_context, classes))
                .collect::<Result<_>>()?,
        ),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => StatementKind::If {
            test: rewrite_expression_ctx(test, class_context, classes)?,
            consequent: Box::new(rewrite_statement(consequent, class_context, classes)?),
            alternate: alternate
                .as_deref()
                .map(|value| rewrite_statement(value, class_context, classes).map(Box::new))
                .transpose()?,
        },
        StatementKind::While { test, body } => StatementKind::While {
            test: rewrite_expression_ctx(test, class_context, classes)?,
            body: Box::new(rewrite_statement(body, class_context, classes)?),
        },
        StatementKind::DoWhile { body, test } => StatementKind::DoWhile {
            body: Box::new(rewrite_statement(body, class_context, classes)?),
            test: rewrite_expression_ctx(test, class_context, classes)?,
        },
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => StatementKind::For {
            init: init
                .as_ref()
                .map(|init| rewrite_for_init(init, class_context, classes))
                .transpose()?,
            test: test
                .as_ref()
                .map(|value| rewrite_expression_ctx(value, class_context, classes))
                .transpose()?,
            update: update
                .as_ref()
                .map(|value| rewrite_expression_ctx(value, class_context, classes))
                .transpose()?,
            body: Box::new(rewrite_statement(body, class_context, classes)?),
        },
        StatementKind::ForIn {
            name,
            kind,
            right,
            body,
        } => StatementKind::ForIn {
            name: name.clone(),
            kind: *kind,
            right: rewrite_expression_ctx(right, class_context, classes)?,
            body: Box::new(rewrite_statement(body, class_context, classes)?),
        },
        StatementKind::ForOf {
            name,
            kind,
            right,
            body,
        } => StatementKind::ForOf {
            name: name.clone(),
            kind: *kind,
            right: rewrite_expression_ctx(right, class_context, classes)?,
            body: Box::new(rewrite_statement(body, class_context, classes)?),
        },
        StatementKind::Switch {
            discriminant,
            cases,
        } => StatementKind::Switch {
            discriminant: rewrite_expression_ctx(discriminant, class_context, classes)?,
            cases: cases
                .iter()
                .map(|case| {
                    Ok(SwitchCase {
                        test: case
                            .test
                            .as_ref()
                            .map(|value| rewrite_expression_ctx(value, class_context, classes))
                            .transpose()?,
                        consequent: case
                            .consequent
                            .iter()
                            .map(|statement| rewrite_statement(statement, class_context, classes))
                            .collect::<Result<_>>()?,
                        span: case.span,
                    })
                })
                .collect::<Result<_>>()?,
        },
        StatementKind::Labeled { label, body } => StatementKind::Labeled {
            label: label.clone(),
            body: Box::new(rewrite_statement(body, class_context, classes)?),
        },
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => StatementKind::Try {
            block: Box::new(rewrite_statement(block, class_context, classes)?),
            handler: handler
                .as_ref()
                .map(|handler| -> Result<ecmora_hir::CatchClause> {
                    Ok(ecmora_hir::CatchClause {
                        parameter: handler.parameter.clone(),
                        body: Box::new(rewrite_statement(&handler.body, class_context, classes)?),
                        span: handler.span,
                    })
                })
                .transpose()?,
            finalizer: finalizer
                .as_deref()
                .map(|value| rewrite_statement(value, class_context, classes).map(Box::new))
                .transpose()?,
        },
        StatementKind::FunctionDeclaration(function) => {
            let mut function = function.clone();
            // Nested ordinary functions do not inherit class private-name lexical access
            // unless they are syntactically created inside a class method. They do, so
            // keep the same class_context while rewriting their body.
            function.body = function
                .body
                .iter()
                .map(|statement| rewrite_statement(statement, class_context, classes))
                .collect::<Result<_>>()?;
            StatementKind::FunctionDeclaration(function)
        }
        StatementKind::Return(value) => StatementKind::Return(
            value
                .as_ref()
                .map(|value| rewrite_expression_ctx(value, class_context, classes))
                .transpose()?,
        ),
        StatementKind::Throw(value) => {
            StatementKind::Throw(rewrite_expression_ctx(value, class_context, classes)?)
        }
        StatementKind::Empty => StatementKind::Empty,
        StatementKind::Debugger => StatementKind::Debugger,
        StatementKind::Break(label) => StatementKind::Break(label.clone()),
        StatementKind::Continue(label) => StatementKind::Continue(label.clone()),
    };
    Ok(Statement { kind, span })
}

fn rewrite_for_init(
    init: &ForInit,
    class_context: Option<&str>,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<ForInit> {
    Ok(match init {
        ForInit::Expression(value) => {
            ForInit::Expression(rewrite_expression_ctx(value, class_context, classes)?)
        }
        ForInit::VariableDeclaration { kind, declarations } => ForInit::VariableDeclaration {
            kind: *kind,
            declarations: declarations
                .iter()
                .map(|declaration| {
                    Ok(VariableDeclarator {
                        name: declaration.name.clone(),
                        init: declaration
                            .init
                            .as_ref()
                            .map(|value| rewrite_expression_ctx(value, class_context, classes))
                            .transpose()?,
                        span: declaration.span,
                    })
                })
                .collect::<Result<_>>()?,
        },
    })
}

fn rewrite_expression(
    expression: &Expression,
    class_name: &str,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Expression> {
    rewrite_expression_ctx(expression, Some(class_name), classes)
}

fn rewrite_expression_ctx(
    expression: &Expression,
    class_context: Option<&str>,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<Expression> {
    let span = expression.span;
    let kind = match &expression.kind {
        ExpressionKind::Binary {
            left,
            operator: BinaryOperator::In,
            right,
        } if unresolved_private_name(left).is_some() => {
            let Some(class_name) = class_context else {
                bail!("private brand check escaped its class lexical scope")
            };
            let private = unresolved_private_name(left).expect("private marker");
            ExpressionKind::Binary {
                left: Box::new(Expression {
                    kind: ExpressionKind::String(private_key(class_name, private)),
                    span,
                }),
                operator: BinaryOperator::In,
                right: Box::new(rewrite_expression_ctx(right, class_context, classes)?),
            }
        }
        ExpressionKind::New { callee, arguments } => {
            if let ExpressionKind::Global(name) = &callee.kind {
                if classes.contains_key(name) {
                    ExpressionKind::Call {
                        callee: Box::new(global_expression(&factory_name(name), span)),
                        arguments: arguments
                            .iter()
                            .map(|value| rewrite_expression_ctx(value, class_context, classes))
                            .collect::<Result<_>>()?,
                    }
                } else {
                    ExpressionKind::New {
                        callee: Box::new(rewrite_expression_ctx(callee, class_context, classes)?),
                        arguments: arguments
                            .iter()
                            .map(|value| rewrite_expression_ctx(value, class_context, classes))
                            .collect::<Result<_>>()?,
                    }
                }
            } else {
                ExpressionKind::New {
                    callee: Box::new(rewrite_expression_ctx(callee, class_context, classes)?),
                    arguments: arguments
                        .iter()
                        .map(|value| rewrite_expression_ctx(value, class_context, classes))
                        .collect::<Result<_>>()?,
                }
            }
        }
        ExpressionKind::Binary {
            left,
            operator: BinaryOperator::InstanceOf,
            right,
        } if matches!(&right.kind, ExpressionKind::Global(name) if classes.contains_key(name)) => {
            let ExpressionKind::Global(name) = &right.kind else {
                unreachable!()
            };
            ExpressionKind::Binary {
                left: Box::new(Expression {
                    kind: ExpressionKind::String(brand_key(name)),
                    span,
                }),
                operator: BinaryOperator::In,
                right: Box::new(rewrite_expression_ctx(left, class_context, classes)?),
            }
        }
        ExpressionKind::Member { object, property } => {
            let property = match property {
                MemberProperty::Static(name) if unresolved_private_key(name).is_some() => {
                    let Some(class_name) = class_context else {
                        bail!("private member escaped its class lexical scope")
                    };
                    MemberProperty::Static(private_key(
                        class_name,
                        unresolved_private_key(name).expect("private marker"),
                    ))
                }
                MemberProperty::Static(name) => MemberProperty::Static(name.clone()),
                MemberProperty::Computed(value) => MemberProperty::Computed(Box::new(
                    rewrite_expression_ctx(value, class_context, classes)?,
                )),
            };
            ExpressionKind::Member {
                object: Box::new(rewrite_expression_ctx(object, class_context, classes)?),
                property,
            }
        }
        ExpressionKind::Assignment {
            target,
            operator,
            value,
        } => ExpressionKind::Assignment {
            target: rewrite_target(target, class_context, classes)?,
            operator: *operator,
            value: Box::new(rewrite_expression_ctx(value, class_context, classes)?),
        },
        ExpressionKind::Update {
            target,
            operator,
            prefix,
        } => ExpressionKind::Update {
            target: rewrite_target(target, class_context, classes)?,
            operator: *operator,
            prefix: *prefix,
        },
        ExpressionKind::Object(entries) => ExpressionKind::Object(
            entries
                .iter()
                .map(|entry| match entry {
                    ObjectEntry::Property(property) => Ok(ObjectEntry::Property(ObjectProperty {
                        key: rewrite_member_property(&property.key, class_context, classes)?,
                        value: rewrite_expression_ctx(&property.value, class_context, classes)?,
                    })),
                    ObjectEntry::Spread(value) => Ok(ObjectEntry::Spread(rewrite_expression_ctx(
                        value,
                        class_context,
                        classes,
                    )?)),
                    ObjectEntry::Accessor { key, get, set } => Ok(ObjectEntry::Accessor {
                        key: key.clone(),
                        get: get
                            .as_ref()
                            .map(|value| rewrite_expression_ctx(value, class_context, classes))
                            .transpose()?,
                        set: set
                            .as_ref()
                            .map(|value| rewrite_expression_ctx(value, class_context, classes))
                            .transpose()?,
                    }),
                })
                .collect::<Result<_>>()?,
        ),
        ExpressionKind::Array(elements) => ExpressionKind::Array(
            elements
                .iter()
                .map(|element| match element {
                    ArrayElement::Expression(value) => Ok(ArrayElement::Expression(
                        rewrite_expression_ctx(value, class_context, classes)?,
                    )),
                    ArrayElement::Spread(value) => Ok(ArrayElement::Spread(
                        rewrite_expression_ctx(value, class_context, classes)?,
                    )),
                    ArrayElement::Hole => Ok(ArrayElement::Hole),
                })
                .collect::<Result<_>>()?,
        ),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => ExpressionKind::Conditional {
            test: Box::new(rewrite_expression_ctx(test, class_context, classes)?),
            consequent: Box::new(rewrite_expression_ctx(consequent, class_context, classes)?),
            alternate: Box::new(rewrite_expression_ctx(alternate, class_context, classes)?),
        },
        ExpressionKind::Unary { operator, argument } => ExpressionKind::Unary {
            operator: *operator,
            argument: Box::new(rewrite_expression_ctx(argument, class_context, classes)?),
        },
        ExpressionKind::Binary {
            left,
            operator,
            right,
        } => ExpressionKind::Binary {
            left: Box::new(rewrite_expression_ctx(left, class_context, classes)?),
            operator: *operator,
            right: Box::new(rewrite_expression_ctx(right, class_context, classes)?),
        },
        ExpressionKind::Logical {
            left,
            operator,
            right,
        } => ExpressionKind::Logical {
            left: Box::new(rewrite_expression_ctx(left, class_context, classes)?),
            operator: *operator,
            right: Box::new(rewrite_expression_ctx(right, class_context, classes)?),
        },
        ExpressionKind::Call { callee, arguments } => {
            if matches!(&callee.kind, ExpressionKind::Global(name) if name == "@super") {
                bail!(
                    "super() must be a top-level derived-constructor statement before class erasure"
                )
            }
            ExpressionKind::Call {
                callee: Box::new(rewrite_expression_ctx(callee, class_context, classes)?),
                arguments: arguments
                    .iter()
                    .map(|value| rewrite_expression_ctx(value, class_context, classes))
                    .collect::<Result<_>>()?,
            }
        }
        ExpressionKind::Function(function) => {
            let mut function = function.clone();
            function.body = function
                .body
                .iter()
                .map(|statement| rewrite_statement(statement, class_context, classes))
                .collect::<Result<_>>()?;
            ExpressionKind::Function(function)
        }
        ExpressionKind::Await(value) => ExpressionKind::Await(Box::new(rewrite_expression_ctx(
            value,
            class_context,
            classes,
        )?)),
        ExpressionKind::String(value) => ExpressionKind::String(value.clone()),
        ExpressionKind::Number(value) => ExpressionKind::Number(*value),
        ExpressionKind::BigInt(value) => ExpressionKind::BigInt(value.clone()),
        ExpressionKind::Bool(value) => ExpressionKind::Bool(*value),
        ExpressionKind::Null => ExpressionKind::Null,
        ExpressionKind::This => ExpressionKind::This,
        ExpressionKind::Global(name) => ExpressionKind::Global(name.clone()),
    };
    Ok(Expression { kind, span })
}

fn rewrite_target(
    target: &AssignmentTarget,
    class_context: Option<&str>,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<AssignmentTarget> {
    Ok(match target {
        AssignmentTarget::Identifier(name) => AssignmentTarget::Identifier(name.clone()),
        AssignmentTarget::Member { object, property } => AssignmentTarget::Member {
            object: Box::new(rewrite_expression_ctx(object, class_context, classes)?),
            property: rewrite_member_property(property, class_context, classes)?,
        },
    })
}

fn rewrite_member_property(
    property: &MemberProperty,
    class_context: Option<&str>,
    classes: &HashMap<String, ClassDeclaration>,
) -> Result<MemberProperty> {
    Ok(match property {
        MemberProperty::Static(name) if unresolved_private_key(name).is_some() => {
            let Some(class_name) = class_context else {
                bail!("private key escaped class lexical scope")
            };
            MemberProperty::Static(private_key(
                class_name,
                unresolved_private_key(name).expect("private marker"),
            ))
        }
        MemberProperty::Static(name) => MemberProperty::Static(name.clone()),
        MemberProperty::Computed(value) => MemberProperty::Computed(Box::new(
            rewrite_expression_ctx(value, class_context, classes)?,
        )),
    })
}

fn direct_super_call(statement: &Statement) -> Option<&[Expression]> {
    let StatementKind::Expression(Expression {
        kind: ExpressionKind::Call { callee, arguments },
        ..
    }) = &statement.kind
    else {
        return None;
    };
    matches!(&callee.kind, ExpressionKind::Global(name) if name == "@super")
        .then_some(arguments.as_slice())
}

fn statement_contains_super(statement: &Statement) -> bool {
    fn expr(value: &Expression) -> bool {
        match &value.kind {
            ExpressionKind::Global(name) => name == "@super",
            ExpressionKind::Member { object, property } => {
                expr(object) || matches!(property, MemberProperty::Computed(value) if expr(value))
            }
            ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
                ObjectEntry::Property(property) => expr(&property.value),
                ObjectEntry::Spread(value) => expr(value),
                ObjectEntry::Accessor { get, set, .. } => {
                    get.as_ref().is_some_and(expr) || set.as_ref().is_some_and(expr)
                }
            }),
            ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
                ArrayElement::Expression(value) | ArrayElement::Spread(value) => expr(value),
                ArrayElement::Hole => false,
            }),
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => expr(test) || expr(consequent) || expr(alternate),
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expr(argument)
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => expr(left) || expr(right),
            ExpressionKind::Assignment { value, .. } => expr(value),
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                expr(callee) || arguments.iter().any(expr)
            }
            ExpressionKind::Function(_)
            | ExpressionKind::Update { .. }
            | ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This => false,
        }
    }
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => expr(value),
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|value| value.init.as_ref())
            .any(expr),
        StatementKind::Block(body) => body.iter().any(statement_contains_super),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expr(test)
                || statement_contains_super(consequent)
                || alternate.as_deref().is_some_and(statement_contains_super)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expr(test) || statement_contains_super(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => expr(value),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|value| value.init.as_ref())
                    .any(expr),
            }) || test.as_ref().is_some_and(expr)
                || update.as_ref().is_some_and(expr)
                || statement_contains_super(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expr(right) || statement_contains_super(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expr(discriminant)
                || cases.iter().any(|case| {
                    case.test.as_ref().is_some_and(expr)
                        || case.consequent.iter().any(statement_contains_super)
                })
        }
        StatementKind::Labeled { body, .. } => statement_contains_super(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_contains_super(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| statement_contains_super(&handler.body))
                || finalizer.as_deref().is_some_and(statement_contains_super)
        }
        StatementKind::Return(value) => value.as_ref().is_some_and(expr),
        StatementKind::FunctionDeclaration(_) => false,
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn validate_erased(statements: &[Statement]) -> Result<()> {
    fn expression(value: &Expression) -> Result<()> {
        match &value.kind {
            ExpressionKind::Member { object, property } => {
                if matches!(property, MemberProperty::Static(name) if unresolved_private_key(name).is_some())
                {
                    bail!("private member marker survived class lowering")
                }
                expression(object)?;
                if let MemberProperty::Computed(value) = property {
                    expression(value)?;
                }
            }
            ExpressionKind::Object(entries) => {
                for entry in entries {
                    match entry {
                        ObjectEntry::Property(property) => expression(&property.value)?,
                        ObjectEntry::Spread(value) => expression(value)?,
                        ObjectEntry::Accessor { get, set, .. } => {
                            if let Some(value) = get {
                                expression(value)?;
                            }
                            if let Some(value) = set {
                                expression(value)?;
                            }
                        }
                    }
                }
            }
            ExpressionKind::Array(elements) => {
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                            expression(value)?
                        }
                        ArrayElement::Hole => {}
                    }
                }
            }
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => {
                expression(test)?;
                expression(consequent)?;
                expression(alternate)?;
            }
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expression(argument)?
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                expression(left)?;
                expression(right)?;
            }
            ExpressionKind::Assignment { target, value, .. } => {
                if let AssignmentTarget::Member { object, property } = target {
                    expression(object)?;
                    if matches!(property, MemberProperty::Static(name) if unresolved_private_key(name).is_some())
                    {
                        bail!("private assignment marker survived class lowering")
                    }
                }
                expression(value)?;
            }
            ExpressionKind::Update { target, .. } => {
                if let AssignmentTarget::Member { property, .. } = target {
                    if matches!(property, MemberProperty::Static(name) if unresolved_private_key(name).is_some())
                    {
                        bail!("private update marker survived class lowering")
                    }
                }
            }
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                expression(callee)?;
                for argument in arguments {
                    expression(argument)?;
                }
            }
            ExpressionKind::Function(function) => {
                for statement in &function.body {
                    statement_check(statement)?;
                }
            }
            ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This
            | ExpressionKind::Global(_) => {}
        }
        Ok(())
    }
    fn statement_check(statement: &Statement) -> Result<()> {
        match &statement.kind {
            StatementKind::Expression(value) | StatementKind::Throw(value) => expression(value)?,
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    if let Some(value) = &declaration.init {
                        expression(value)?;
                    }
                }
            }
            StatementKind::Block(body) => {
                for value in body {
                    statement_check(value)?;
                }
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                expression(test)?;
                statement_check(consequent)?;
                if let Some(value) = alternate {
                    statement_check(value)?;
                }
            }
            StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
                expression(test)?;
                statement_check(body)?;
            }
            StatementKind::For { body, .. }
            | StatementKind::ForIn { body, .. }
            | StatementKind::ForOf { body, .. } => statement_check(body)?,
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                expression(discriminant)?;
                for case in cases {
                    for value in &case.consequent {
                        statement_check(value)?;
                    }
                }
            }
            StatementKind::Labeled { body, .. } => statement_check(body)?,
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                statement_check(block)?;
                if let Some(value) = handler {
                    statement_check(&value.body)?;
                }
                if let Some(value) = finalizer {
                    statement_check(value)?;
                }
            }
            StatementKind::FunctionDeclaration(function) => {
                for value in &function.body {
                    statement_check(value)?;
                }
            }
            StatementKind::Return(value) => {
                if let Some(value) = value {
                    expression(value)?;
                }
            }
            StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
        }
        Ok(())
    }
    for statement in statements {
        statement_check(statement)?;
    }
    Ok(())
}

fn lowered_key(class_name: &str, key: &ClassKey) -> String {
    match key {
        ClassKey::Public(name) => name.clone(),
        ClassKey::Private(name) => private_key(class_name, name),
    }
}

const UNRESOLVED_PRIVATE_PREFIX: &str = "@private_unresolved_";

fn unresolved_private_key(key: &str) -> Option<&str> {
    key.strip_prefix(UNRESOLVED_PRIVATE_PREFIX)
}

fn unresolved_private_name(expression: &Expression) -> Option<&str> {
    let ExpressionKind::String(value) = &expression.kind else {
        return None;
    };
    unresolved_private_key(value)
}

fn private_key(class_name: &str, name: &str) -> String {
    format!("@class_private_{}_{}", sanitize(class_name), sanitize(name))
}

fn brand_key(class_name: &str) -> String {
    format!("@class_brand_{}", sanitize(class_name))
}

fn prototype_name(class_name: &str) -> String {
    format!("@class_proto_{}", sanitize(class_name))
}

fn initializer_key(class_name: &str) -> String {
    format!("@class_init_{}", sanitize(class_name))
}

fn factory_name(class_name: &str) -> String {
    format!("@class_new_{}", sanitize(class_name))
}

fn instance_name(class_name: &str) -> String {
    format!("@class_instance_{}", sanitize(class_name))
}

fn sanitize(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn global_expression(name: &str, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Global(name.to_owned()),
        span,
    }
}

fn undefined_expression(span: Span) -> Expression {
    global_expression("undefined", span)
}

fn member_expression(object: Expression, key: &str, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Member {
            object: Box::new(object),
            property: MemberProperty::Static(key.to_owned()),
        },
        span,
    }
}

fn call_expression(callee: Expression, arguments: Vec<Expression>, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Call {
            callee: Box::new(callee),
            arguments,
        },
        span,
    }
}

fn expression_statement(value: Expression) -> Statement {
    let span = value.span;
    Statement {
        kind: StatementKind::Expression(value),
        span,
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
