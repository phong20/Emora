use anyhow::{Result, anyhow, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, CatchClause, ExportBinding,
    Expression as HirExpression, ExpressionKind, ForInit, Function as HirFunction,
    ImportDeclaration as HirImportDeclaration, ImportSpecifier as HirImportSpecifier,
    LogicalOperator, MemberProperty, ObjectEntry, ObjectProperty, Program as HirProgram, Span,
    Statement as HirStatement, StatementKind, SwitchCase, UnaryOperator, UpdateOperator,
    VariableDeclarator, VariableKind,
};
use oxc_ast::ast::{
    ArrayExpressionElement, ArrowFunctionExpression, AssignmentOperator as OxcAssignmentOperator,
    BinaryOperator as OxcBinaryOperator, BindingPattern, Declaration, ExportDefaultDeclarationKind,
    Expression, ForStatementInit, ForStatementLeft, Function as OxcFunction,
    ImportDeclarationSpecifier, LogicalOperator as OxcLogicalOperator, ObjectPropertyKind, Program,
    SimpleAssignmentTarget, Statement, UnaryOperator as OxcUnaryOperator,
    UpdateOperator as OxcUpdateOperator, VariableDeclaration, VariableDeclarationKind,
};
use oxc_span::Span as OxcSpan;

pub fn lower_program(program: &Program<'_>) -> Result<HirProgram> {
    let mut statements = Vec::new();
    let mut imports = Vec::new();
    let mut exports = Vec::new();
    let mut export_all = Vec::new();
    let mut promise_subclasses = Vec::new();
    for statement in &program.body {
        match statement {
            Statement::ClassDeclaration(class) => {
                promise_subclasses.push(lower_promise_subclass(class)?);
            }
            Statement::ImportDeclaration(declaration) => {
                let specifiers = declaration
                    .specifiers
                    .iter()
                    .flatten()
                    .map(|specifier| match specifier {
                        ImportDeclarationSpecifier::ImportSpecifier(specifier) => {
                            HirImportSpecifier::Named {
                                imported: specifier.imported.name().to_string(),
                                local: specifier.local.name.to_string(),
                            }
                        }
                        ImportDeclarationSpecifier::ImportDefaultSpecifier(specifier) => {
                            HirImportSpecifier::Default {
                                local: specifier.local.name.to_string(),
                            }
                        }
                        ImportDeclarationSpecifier::ImportNamespaceSpecifier(specifier) => {
                            HirImportSpecifier::Namespace {
                                local: specifier.local.name.to_string(),
                            }
                        }
                    })
                    .collect();
                imports.push(HirImportDeclaration {
                    source: declaration.source.value.to_string(),
                    specifiers,
                });
            }
            Statement::ExportNamedDeclaration(declaration) => {
                if let Some(inner) = &declaration.declaration {
                    let lowered = lower_declaration(inner)?;
                    for local in declared_names(&lowered) {
                        exports.push(ExportBinding {
                            exported: local.clone(),
                            local,
                            source: None,
                        });
                    }
                    statements.push(lowered);
                }
                for specifier in &declaration.specifiers {
                    exports.push(ExportBinding {
                        local: specifier.local.name().to_string(),
                        exported: specifier.exported.name().to_string(),
                        source: declaration
                            .source
                            .as_ref()
                            .map(|source| source.value.to_string()),
                    });
                }
                if let Some(source) = &declaration.source {
                    imports.push(HirImportDeclaration {
                        source: source.value.to_string(),
                        specifiers: Vec::new(),
                    });
                }
            }
            Statement::ExportDefaultDeclaration(declaration) => {
                const DEFAULT_LOCAL: &str = "__ecmora_default_export";
                match &declaration.declaration {
                    ExportDefaultDeclarationKind::FunctionDeclaration(function) => {
                        let mut function = lower_function(function, false)?;
                        let local = function
                            .name
                            .clone()
                            .unwrap_or_else(|| DEFAULT_LOCAL.to_owned());
                        function.name = Some(local.clone());
                        statements.push(HirStatement {
                            kind: StatementKind::FunctionDeclaration(function),
                            span: convert_span(declaration.span),
                        });
                        exports.push(ExportBinding {
                            local,
                            exported: "default".to_owned(),
                            source: None,
                        });
                    }
                    ExportDefaultDeclarationKind::ClassDeclaration(_) => {
                        bail!("export default class chưa được native HIR hỗ trợ")
                    }
                    kind => {
                        let value = kind
                            .as_expression()
                            .ok_or_else(|| anyhow!("export default không phải runtime value"))?;
                        statements.push(HirStatement {
                            kind: StatementKind::VariableDeclaration {
                                kind: VariableKind::Const,
                                declarations: vec![VariableDeclarator {
                                    name: DEFAULT_LOCAL.to_owned(),
                                    init: Some(lower_expression(value)?),
                                    span: convert_span(declaration.span),
                                }],
                            },
                            span: convert_span(declaration.span),
                        });
                        exports.push(ExportBinding {
                            local: DEFAULT_LOCAL.to_owned(),
                            exported: "default".to_owned(),
                            source: None,
                        });
                    }
                }
            }
            Statement::ExportAllDeclaration(declaration) => {
                let source = declaration.source.value.to_string();
                export_all.push(source.clone());
                imports.push(HirImportDeclaration {
                    source,
                    specifiers: Vec::new(),
                });
            }
            _ => statements.push(lower_statement(statement)?),
        }
    }
    lower_commonjs_exports(&mut statements, &mut exports);
    lower_static_requires(&mut statements, &mut imports);
    Ok(HirProgram {
        statements,
        strict: program.source_type.is_strict() || program.has_use_strict_directive(),
        imports,
        exports,
        export_all,
        promise_subclasses,
    })
}

fn lower_commonjs_exports(statements: &mut Vec<HirStatement>, exports: &mut Vec<ExportBinding>) {
    for statement in statements.iter_mut() {
        let StatementKind::Expression(HirExpression {
            kind:
                ExpressionKind::Assignment {
                    target: AssignmentTarget::Member { object, property },
                    operator: AssignmentOperator::Assign,
                    value,
                },
            ..
        }) = &mut statement.kind
        else {
            continue;
        };
        let exported = match (&object.kind, property) {
            (ExpressionKind::Global(root), MemberProperty::Static(name)) if root == "exports" => {
                name.clone()
            }
            (ExpressionKind::Global(root), MemberProperty::Static(name))
                if root == "module" && name == "exports" =>
            {
                "default".to_owned()
            }
            _ => continue,
        };
        let local = format!("__ecmora_cjs_{}", sanitize_binding_name(&exported));
        let init = (**value).clone();
        statement.kind = StatementKind::VariableDeclaration {
            kind: VariableKind::Const,
            declarations: vec![VariableDeclarator {
                name: local.clone(),
                init: Some(init),
                span: statement.span,
            }],
        };
        exports.push(ExportBinding {
            local,
            exported,
            source: None,
        });
    }
}

fn lower_static_requires(
    statements: &mut Vec<HirStatement>,
    imports: &mut Vec<HirImportDeclaration>,
) {
    let mut retained = Vec::with_capacity(statements.len());
    for mut statement in statements.drain(..) {
        if let StatementKind::Expression(expression) = &statement.kind {
            if let Some(source) = static_require_source(expression) {
                imports.push(HirImportDeclaration {
                    source,
                    specifiers: Vec::new(),
                });
                continue;
            }
        }
        if let StatementKind::VariableDeclaration { declarations, .. } = &mut statement.kind {
            declarations.retain(|declaration| {
                let Some(init) = &declaration.init else {
                    return true;
                };
                if let Some(source) = static_require_source(init) {
                    imports.push(HirImportDeclaration {
                        source,
                        specifiers: vec![HirImportSpecifier::Default {
                            local: declaration.name.clone(),
                        }],
                    });
                    return false;
                }
                if let ExpressionKind::Member { object, property } = &init.kind {
                    if let (Some(source), MemberProperty::Static(imported)) =
                        (static_require_source(object), property)
                    {
                        imports.push(HirImportDeclaration {
                            source,
                            specifiers: vec![HirImportSpecifier::Named {
                                imported: imported.clone(),
                                local: declaration.name.clone(),
                            }],
                        });
                        return false;
                    }
                }
                true
            });
            if declarations.is_empty() {
                continue;
            }
        }
        retained.push(statement);
    }
    *statements = retained;
    let constants = statements
        .iter()
        .flat_map(|statement| match &statement.kind {
            StatementKind::VariableDeclaration { declarations, .. } => declarations,
            _ => &[] as &[VariableDeclarator],
        })
        .filter_map(|declaration| match &declaration.init {
            Some(HirExpression {
                kind: ExpressionKind::String(value),
                ..
            }) => Some((declaration.name.clone(), value.clone())),
            _ => None,
        })
        .collect::<std::collections::HashMap<_, _>>();
    let snapshot = statements.clone();
    for statement in &snapshot {
        collect_static_modules_statement(statement, imports, &constants);
    }
}

fn collect_static_modules_statement(
    statement: &HirStatement,
    imports: &mut Vec<HirImportDeclaration>,
    constants: &std::collections::HashMap<String, String>,
) {
    fn add(source: &str, imports: &mut Vec<HirImportDeclaration>) {
        if !imports.iter().any(|import| import.source == source) {
            imports.push(HirImportDeclaration {
                source: source.to_owned(),
                specifiers: Vec::new(),
            });
        }
    }
    fn walk_expression(
        expression: &HirExpression,
        imports: &mut Vec<HirImportDeclaration>,
        constants: &std::collections::HashMap<String, String>,
    ) {
        match &expression.kind {
            ExpressionKind::Call { callee, arguments } if matches!(&callee.kind, ExpressionKind::Global(name) if name == "require" || name == "__ecmora_dynamic_import") =>
            {
                if let [argument] = arguments.as_slice() {
                    match &argument.kind {
                        ExpressionKind::String(source) => add(source, imports),
                        ExpressionKind::Global(name) => {
                            if let Some(source) = constants.get(name) {
                                add(source, imports);
                            }
                        }
                        _ => {}
                    }
                }
                for argument in arguments {
                    walk_expression(argument, imports, constants);
                }
            }
            ExpressionKind::Member { object, property } => {
                walk_expression(object, imports, constants);
                if let MemberProperty::Computed(value) = property {
                    walk_expression(value, imports, constants);
                }
            }
            ExpressionKind::Object(entries) => {
                for entry in entries {
                    match entry {
                        ObjectEntry::Property(property) => {
                            walk_expression(&property.value, imports, constants)
                        }
                        ObjectEntry::Spread(value) => walk_expression(value, imports, constants),
                        ObjectEntry::Accessor { get, set, .. } => {
                            if let Some(get) = get {
                                walk_expression(get, imports, constants);
                            }
                            if let Some(set) = set {
                                walk_expression(set, imports, constants);
                            }
                        }
                    }
                }
            }
            ExpressionKind::Array(elements) => {
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                            walk_expression(value, imports, constants)
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
                walk_expression(test, imports, constants);
                walk_expression(consequent, imports, constants);
                walk_expression(alternate, imports, constants);
            }
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                walk_expression(argument, imports, constants)
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                walk_expression(left, imports, constants);
                walk_expression(right, imports, constants);
            }
            ExpressionKind::Assignment { value, .. } => walk_expression(value, imports, constants),
            ExpressionKind::Update { .. } => {}
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                walk_expression(callee, imports, constants);
                for argument in arguments {
                    walk_expression(argument, imports, constants);
                }
            }
            // Do not resolve modules from every function body here: a dead
            // function may intentionally contain a dynamic import of a file
            // that does not exist. Reachability analysis resolves a called
            // function later; top-level static module edges are enough for
            // this frontend pass.
            ExpressionKind::Function(_) => {}
            _ => {}
        }
    }
    fn statement_walk(
        statement: &HirStatement,
        imports: &mut Vec<HirImportDeclaration>,
        constants: &std::collections::HashMap<String, String>,
    ) {
        match &statement.kind {
            StatementKind::Expression(value) | StatementKind::Throw(value) => {
                walk_expression(value, imports, constants)
            }
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    if let Some(value) = &declaration.init {
                        walk_expression(value, imports, constants);
                    }
                }
            }
            StatementKind::Block(body) => {
                for statement in body {
                    statement_walk(statement, imports, constants);
                }
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                walk_expression(test, imports, constants);
                statement_walk(consequent, imports, constants);
                if let Some(alternate) = alternate {
                    statement_walk(alternate, imports, constants);
                }
            }
            StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
                walk_expression(test, imports, constants);
                statement_walk(body, imports, constants);
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                if let Some(init) = init {
                    match init {
                        ForInit::VariableDeclaration { declarations, .. } => {
                            for declaration in declarations {
                                if let Some(value) = &declaration.init {
                                    walk_expression(value, imports, constants);
                                }
                            }
                        }
                        ForInit::Expression(value) => walk_expression(value, imports, constants),
                    }
                }
                if let Some(test) = test {
                    walk_expression(test, imports, constants);
                }
                if let Some(update) = update {
                    walk_expression(update, imports, constants);
                }
                statement_walk(body, imports, constants);
            }
            StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
                walk_expression(right, imports, constants);
                statement_walk(body, imports, constants);
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                walk_expression(discriminant, imports, constants);
                for case in cases {
                    if let Some(test) = &case.test {
                        walk_expression(test, imports, constants);
                    }
                    for statement in &case.consequent {
                        statement_walk(statement, imports, constants);
                    }
                }
            }
            StatementKind::Labeled { body, .. } => {
                statement_walk(body, imports, constants);
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                statement_walk(block, imports, constants);
                if let Some(handler) = handler {
                    statement_walk(&handler.body, imports, constants);
                }
                if let Some(finalizer) = finalizer {
                    statement_walk(finalizer, imports, constants);
                }
            }
            StatementKind::FunctionDeclaration(_) => {}
            StatementKind::Return(value) => {
                if let Some(value) = value {
                    walk_expression(value, imports, constants);
                }
            }
            StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
        }
    }
    statement_walk(statement, imports, constants);
}

fn static_require_source(expression: &HirExpression) -> Option<String> {
    let ExpressionKind::Call { callee, arguments } = &expression.kind else {
        return None;
    };
    if !matches!(&callee.kind, ExpressionKind::Global(name) if name == "require") {
        return None;
    }
    match arguments.as_slice() {
        [
            HirExpression {
                kind: ExpressionKind::String(source),
                ..
            },
        ] => Some(source.clone()),
        _ => None,
    }
}

fn sanitize_binding_name(name: &str) -> String {
    name.chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect()
}

fn lower_promise_subclass(class: &oxc_ast::ast::Class<'_>) -> Result<ecmora_hir::PromiseSubclass> {
    use oxc_ast::ast::{ClassElement, MethodDefinitionKind};

    let name = class
        .id
        .as_ref()
        .ok_or_else(|| anyhow!("Promise subclass declaration phải có tên"))?
        .name
        .to_string();

    let parent = match class.super_class.as_ref() {
        Some(Expression::Identifier(identifier)) => identifier.name.to_string(),
        Some(_) => bail!("Promise subclass extends expression phải là identifier tĩnh"),
        None => bail!("class `{name}` không extends Promise/subclass"),
    };

    let mut species = None;
    let mut constructor = None;
    let mut methods = Vec::new();
    for element in &class.body.body {
        let ClassElement::MethodDefinition(method) = element else {
            bail!(
                "Promise subclass `{name}` hiện hỗ trợ constructor/method/getter/setter; \
                 class field/static block cần field-initializer lowering"
            )
        };

        let mut function = lower_function(&method.value, false)?;
        function.name = method
            .key
            .static_name()
            .map(|name| name.into_owned())
            .or_else(|| function.name.clone());

        if method.kind == MethodDefinitionKind::Constructor {
            if constructor.replace(function).is_some() {
                bail!("Promise subclass `{name}` có nhiều constructor")
            }
            continue;
        }

        let is_species = method.r#static
            && method.kind == MethodDefinitionKind::Get
            && method.computed
            && method.key.as_expression().is_some_and(|key| {
                matches!(
                    key,
                    Expression::StaticMemberExpression(member)
                        if matches!(
                            &member.object,
                            Expression::Identifier(identifier)
                                if identifier.name == "Symbol"
                        ) && member.property.name == "species"
                )
            });

        let key = if is_species {
            "@@species".to_owned()
        } else if method.computed {
            bail!("computed class method key chưa được hỗ trợ ngoài Symbol.species")
        } else {
            method
                .key
                .static_name()
                .ok_or_else(|| anyhow!("class method key chưa được hỗ trợ"))?
                .into_owned()
        };

        let kind = match method.kind {
            MethodDefinitionKind::Method => ecmora_hir::ClassMethodKind::Method,
            MethodDefinitionKind::Get => ecmora_hir::ClassMethodKind::Get,
            MethodDefinitionKind::Set => ecmora_hir::ClassMethodKind::Set,
            MethodDefinitionKind::Constructor => unreachable!(),
        };

        if is_species {
            let body = method
                .value
                .body
                .as_ref()
                .ok_or_else(|| anyhow!("@@species getter thiếu body"))?;
            let [Statement::ReturnStatement(statement)] = body.statements.as_slice() else {
                bail!("@@species getter phải chỉ chứa `return Constructor`")
            };
            let Some(Expression::Identifier(identifier)) = statement.argument.as_ref() else {
                bail!("@@species getter phải return identifier constructor")
            };
            species = Some(identifier.name.to_string());
        }

        methods.push(ecmora_hir::ClassMethod {
            key,
            function,
            kind,
            r#static: method.r#static,
        });
    }

    Ok(ecmora_hir::PromiseSubclass {
        name,
        parent,
        species,
        constructor,
        methods,
    })
}

fn lower_declaration(declaration: &Declaration<'_>) -> Result<HirStatement> {
    match declaration {
        Declaration::VariableDeclaration(declaration) => {
            let (kind, declarations) = lower_variable_declaration(declaration)?;
            Ok(HirStatement {
                kind: StatementKind::VariableDeclaration { kind, declarations },
                span: convert_span(declaration.span),
            })
        }
        Declaration::FunctionDeclaration(function) => Ok(HirStatement {
            kind: StatementKind::FunctionDeclaration(lower_function(function, false)?),
            span: convert_span(function.span),
        }),
        unsupported => bail!("export declaration chưa được native HIR hỗ trợ: {unsupported:#?}"),
    }
}

fn declared_names(statement: &HirStatement) -> Vec<String> {
    match &statement.kind {
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .map(|value| value.name.clone())
            .collect(),
        StatementKind::FunctionDeclaration(function) => function.name.iter().cloned().collect(),
        _ => Vec::new(),
    }
}

fn lower_statement(statement: &Statement<'_>) -> Result<HirStatement> {
    let (kind, span) = match statement {
        Statement::EmptyStatement(statement) => (StatementKind::Empty, statement.span),
        Statement::DebuggerStatement(statement) => (StatementKind::Debugger, statement.span),
        Statement::ExpressionStatement(statement) => (
            StatementKind::Expression(lower_expression(&statement.expression)?),
            statement.span,
        ),
        Statement::BlockStatement(block) => (
            StatementKind::Block(
                block
                    .body
                    .iter()
                    .map(lower_statement)
                    .collect::<Result<_>>()?,
            ),
            block.span,
        ),
        Statement::IfStatement(statement) => (
            StatementKind::If {
                test: lower_expression(&statement.test)?,
                consequent: Box::new(lower_statement(&statement.consequent)?),
                alternate: statement
                    .alternate
                    .as_ref()
                    .map(lower_statement)
                    .transpose()?
                    .map(Box::new),
            },
            statement.span,
        ),
        Statement::WhileStatement(statement) => (
            StatementKind::While {
                test: lower_expression(&statement.test)?,
                body: Box::new(lower_statement(&statement.body)?),
            },
            statement.span,
        ),
        Statement::DoWhileStatement(statement) => (
            StatementKind::DoWhile {
                body: Box::new(lower_statement(&statement.body)?),
                test: lower_expression(&statement.test)?,
            },
            statement.span,
        ),
        Statement::ForStatement(statement) => {
            let init = match &statement.init {
                Some(ForStatementInit::VariableDeclaration(declaration)) => {
                    let (kind, declarations) = lower_variable_declaration(declaration)?;
                    Some(ForInit::VariableDeclaration { kind, declarations })
                }
                Some(init) => Some(ForInit::Expression(lower_expression(
                    init.as_expression()
                        .ok_or_else(|| anyhow!("for initializer không hợp lệ"))?,
                )?)),
                None => None,
            };
            (
                StatementKind::For {
                    init,
                    test: statement.test.as_ref().map(lower_expression).transpose()?,
                    update: statement
                        .update
                        .as_ref()
                        .map(lower_expression)
                        .transpose()?,
                    body: Box::new(lower_statement(&statement.body)?),
                },
                statement.span,
            )
        }
        Statement::ForInStatement(statement) => {
            let (name, kind) = lower_for_left(&statement.left)?;
            (
                StatementKind::ForIn {
                    name,
                    kind,
                    right: lower_expression(&statement.right)?,
                    body: Box::new(lower_statement(&statement.body)?),
                },
                statement.span,
            )
        }
        Statement::ForOfStatement(statement) => {
            if statement.r#await {
                bail!("for await...of chưa được hỗ trợ")
            }
            let (name, kind) = lower_for_left(&statement.left)?;
            (
                StatementKind::ForOf {
                    name,
                    kind,
                    right: lower_expression(&statement.right)?,
                    body: Box::new(lower_statement(&statement.body)?),
                },
                statement.span,
            )
        }
        Statement::SwitchStatement(statement) => (
            StatementKind::Switch {
                discriminant: lower_expression(&statement.discriminant)?,
                cases: statement
                    .cases
                    .iter()
                    .map(|case| {
                        Ok(SwitchCase {
                            test: case.test.as_ref().map(lower_expression).transpose()?,
                            consequent: case
                                .consequent
                                .iter()
                                .map(lower_statement)
                                .collect::<Result<_>>()?,
                            span: convert_span(case.span),
                        })
                    })
                    .collect::<Result<_>>()?,
            },
            statement.span,
        ),
        Statement::LabeledStatement(statement) => (
            StatementKind::Labeled {
                label: statement.label.name.to_string(),
                body: Box::new(lower_statement(&statement.body)?),
            },
            statement.span,
        ),
        Statement::TryStatement(statement) => {
            let block = lower_block_statement(&statement.block)?;
            let handler = statement
                .handler
                .as_ref()
                .map(|handler| lower_catch_clause(handler))
                .transpose()?;
            let finalizer = statement
                .finalizer
                .as_ref()
                .map(|block| lower_block_statement(block))
                .transpose()?
                .map(Box::new);
            if handler.is_none() && finalizer.is_none() {
                bail!("try statement cần catch hoặc finally")
            }
            (
                StatementKind::Try {
                    block: Box::new(block),
                    handler,
                    finalizer,
                },
                statement.span,
            )
        }
        Statement::FunctionDeclaration(function) => {
            let span = function.span;
            let function = lower_function(function, false)?;
            if function.name.is_none() {
                bail!("function declaration phải có tên")
            }
            (StatementKind::FunctionDeclaration(function), span)
        }
        Statement::ReturnStatement(statement) => (
            StatementKind::Return(
                statement
                    .argument
                    .as_ref()
                    .map(lower_expression)
                    .transpose()?,
            ),
            statement.span,
        ),
        Statement::ThrowStatement(statement) => (
            StatementKind::Throw(lower_expression(&statement.argument)?),
            statement.span,
        ),
        Statement::BreakStatement(statement) => (
            StatementKind::Break(statement.label.as_ref().map(|label| label.name.to_string())),
            statement.span,
        ),
        Statement::ContinueStatement(statement) => (
            StatementKind::Continue(statement.label.as_ref().map(|label| label.name.to_string())),
            statement.span,
        ),
        Statement::VariableDeclaration(declaration) => {
            let (kind, declarations) = lower_variable_declaration(declaration)?;
            (
                StatementKind::VariableDeclaration { kind, declarations },
                declaration.span,
            )
        }
        unsupported => bail!("statement chưa được hỗ trợ trong HIR: {unsupported:#?}"),
    };
    Ok(HirStatement {
        kind,
        span: convert_span(span),
    })
}

fn lower_block_statement(block: &oxc_ast::ast::BlockStatement<'_>) -> Result<HirStatement> {
    Ok(HirStatement {
        kind: StatementKind::Block(
            block
                .body
                .iter()
                .map(lower_statement)
                .collect::<Result<_>>()?,
        ),
        span: convert_span(block.span),
    })
}

fn lower_catch_clause(clause: &oxc_ast::ast::CatchClause<'_>) -> Result<CatchClause> {
    let span = convert_span(clause.span);
    let mut body = clause
        .body
        .body
        .iter()
        .map(lower_statement)
        .collect::<Result<Vec<_>>>()?;

    let parameter = match &clause.param {
        None => None,
        Some(parameter) => match &parameter.pattern {
            BindingPattern::BindingIdentifier(identifier) => Some(identifier.name.to_string()),
            pattern => {
                let hidden = format!("@catch.{}.{}", span.start, span.end);
                let mut declarations = Vec::new();
                lower_binding_pattern(
                    pattern,
                    HirExpression {
                        kind: ExpressionKind::Global(hidden.clone()),
                        span,
                    },
                    span,
                    &mut declarations,
                )?;
                if !declarations.is_empty() {
                    body.insert(
                        0,
                        HirStatement {
                            kind: StatementKind::VariableDeclaration {
                                kind: VariableKind::Let,
                                declarations,
                            },
                            span,
                        },
                    );
                }
                Some(hidden)
            }
        },
    };

    Ok(CatchClause {
        parameter,
        body: Box::new(HirStatement {
            kind: StatementKind::Block(body),
            span: convert_span(clause.body.span),
        }),
        span,
    })
}

fn lower_variable_declaration(
    declaration: &VariableDeclaration<'_>,
) -> Result<(VariableKind, Vec<VariableDeclarator>)> {
    let kind = match declaration.kind {
        VariableDeclarationKind::Const => VariableKind::Const,
        VariableDeclarationKind::Let => VariableKind::Let,
        VariableDeclarationKind::Var => VariableKind::Var,
        _ => bail!("declaration kind chưa được hỗ trợ"),
    };
    let mut declarations = Vec::with_capacity(declaration.declarations.len());
    for declarator in &declaration.declarations {
        if kind == VariableKind::Const && declarator.init.is_none() {
            bail!("const phải có initializer")
        }
        match &declarator.id {
            BindingPattern::BindingIdentifier(identifier) => {
                declarations.push(VariableDeclarator {
                    name: identifier.name.to_string(),
                    init: declarator.init.as_ref().map(lower_expression).transpose()?,
                    span: convert_span(declarator.span),
                })
            }
            pattern => {
                let init = declarator
                    .init
                    .as_ref()
                    .ok_or_else(|| anyhow!("destructuring declaration cần initializer"))?;
                let span = convert_span(declarator.span);
                let root = fresh_destructure_name(span, declarations.len());
                declarations.push(VariableDeclarator {
                    name: root.clone(),
                    init: Some(lower_expression(init)?),
                    span,
                });
                lower_binding_pattern(
                    pattern,
                    HirExpression {
                        kind: ExpressionKind::Global(root),
                        span,
                    },
                    span,
                    &mut declarations,
                )?;
            }
        }
    }
    Ok((kind, declarations))
}

fn lower_binding_pattern(
    pattern: &BindingPattern<'_>,
    source: HirExpression,
    span: Span,
    declarations: &mut Vec<VariableDeclarator>,
) -> Result<()> {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => declarations.push(VariableDeclarator {
            name: identifier.name.to_string(),
            init: Some(source),
            span,
        }),
        BindingPattern::AssignmentPattern(assignment) => {
            let temp = fresh_destructure_name(span, declarations.len());
            declarations.push(VariableDeclarator {
                name: temp.clone(),
                init: Some(source),
                span,
            });
            let temp_expression = || HirExpression {
                kind: ExpressionKind::Global(temp.clone()),
                span,
            };
            let value = HirExpression {
                kind: ExpressionKind::Conditional {
                    test: Box::new(HirExpression {
                        kind: ExpressionKind::Binary {
                            left: Box::new(temp_expression()),
                            operator: BinaryOperator::StrictEqual,
                            right: Box::new(HirExpression {
                                kind: ExpressionKind::Global("undefined".to_owned()),
                                span,
                            }),
                        },
                        span,
                    }),
                    consequent: Box::new(lower_expression(&assignment.right)?),
                    alternate: Box::new(temp_expression()),
                },
                span,
            };
            lower_binding_pattern(&assignment.left, value, span, declarations)?;
        }
        BindingPattern::ArrayPattern(array) => {
            if array.rest.is_some() {
                bail!("array rest destructuring cần slice IR")
            }
            for (index, element) in array.elements.iter().enumerate() {
                let Some(element) = element else { continue };
                lower_binding_pattern(
                    element,
                    HirExpression {
                        kind: ExpressionKind::Member {
                            object: Box::new(source.clone()),
                            property: MemberProperty::Computed(Box::new(HirExpression {
                                kind: ExpressionKind::Number(index as f64),
                                span,
                            })),
                        },
                        span,
                    },
                    span,
                    declarations,
                )?;
            }
        }
        BindingPattern::ObjectPattern(object) => {
            if object.rest.is_some() {
                bail!("object rest destructuring cần copy-data-properties IR")
            }
            for property in &object.properties {
                let key = if property.computed {
                    MemberProperty::Computed(Box::new(lower_expression(
                        property
                            .key
                            .as_expression()
                            .ok_or_else(|| anyhow!("computed destructuring key không hợp lệ"))?,
                    )?))
                } else {
                    MemberProperty::Static(
                        property
                            .key
                            .static_name()
                            .ok_or_else(|| anyhow!("destructuring key không hợp lệ"))?
                            .into_owned(),
                    )
                };
                lower_binding_pattern(
                    &property.value,
                    HirExpression {
                        kind: ExpressionKind::Member {
                            object: Box::new(source.clone()),
                            property: key,
                        },
                        span,
                    },
                    span,
                    declarations,
                )?;
            }
        }
    }
    Ok(())
}

fn fresh_destructure_name(span: Span, index: usize) -> String {
    format!("@destructure.{}.{}.{}", span.start, span.end, index)
}

fn lower_for_left(left: &ForStatementLeft<'_>) -> Result<(String, VariableKind)> {
    match left {
        ForStatementLeft::VariableDeclaration(declaration) => {
            if declaration.declarations.len() != 1 {
                bail!("for-in/of cần đúng một binding")
            }
            let declarator = &declaration.declarations[0];
            if declarator.init.is_some() {
                bail!("for-in/of binding không được có initializer")
            }
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                bail!("for-in/of chỉ hỗ trợ identifier")
            };
            let kind = match declaration.kind {
                VariableDeclarationKind::Const => VariableKind::Const,
                VariableDeclarationKind::Let => VariableKind::Let,
                VariableDeclarationKind::Var => VariableKind::Var,
                _ => bail!("for-in/of declaration kind chưa được hỗ trợ"),
            };
            Ok((identifier.name.to_string(), kind))
        }
        ForStatementLeft::AssignmentTargetIdentifier(identifier) => {
            Ok((identifier.name.to_string(), VariableKind::Let))
        }
        _ => bail!("for-in/of chỉ hỗ trợ identifier target"),
    }
}

fn lower_expression(expression: &Expression<'_>) -> Result<HirExpression> {
    let (kind, span) = match expression {
        Expression::StringLiteral(literal) => (
            ExpressionKind::String(literal.value.as_str().to_owned()),
            literal.span,
        ),
        Expression::NumericLiteral(literal) => {
            (ExpressionKind::Number(literal.value), literal.span)
        }
        Expression::BigIntLiteral(literal) => (
            ExpressionKind::BigInt(literal.value.as_str().to_owned()),
            literal.span,
        ),
        Expression::BooleanLiteral(literal) => (ExpressionKind::Bool(literal.value), literal.span),
        Expression::NullLiteral(literal) => (ExpressionKind::Null, literal.span),
        Expression::ThisExpression(expression) => (ExpressionKind::This, expression.span),
        Expression::Super(expression) => {
            (ExpressionKind::Global("@super".to_owned()), expression.span)
        }
        Expression::Identifier(identifier) => (
            ExpressionKind::Global(identifier.name.to_string()),
            identifier.span,
        ),
        Expression::ParenthesizedExpression(expression) => {
            return lower_expression(&expression.expression);
        }
        Expression::StaticMemberExpression(member) => (
            ExpressionKind::Member {
                object: Box::new(lower_expression(&member.object)?),
                property: MemberProperty::Static(member.property.name.to_string()),
            },
            member.span,
        ),
        Expression::ComputedMemberExpression(member) => (
            ExpressionKind::Member {
                object: Box::new(lower_expression(&member.object)?),
                property: MemberProperty::Computed(Box::new(lower_expression(&member.expression)?)),
            },
            member.span,
        ),
        Expression::ObjectExpression(object) => {
            let mut properties = Vec::with_capacity(object.properties.len());
            for item in &object.properties {
                let ObjectPropertyKind::ObjectProperty(property) = item else {
                    let ObjectPropertyKind::SpreadProperty(spread) = item else {
                        unreachable!()
                    };
                    properties.push(ObjectEntry::Spread(lower_expression(&spread.argument)?));
                    continue;
                };
                let key = if property.computed {
                    MemberProperty::Computed(Box::new(lower_expression(
                        property
                            .key
                            .as_expression()
                            .ok_or_else(|| anyhow!("computed key không hợp lệ"))?,
                    )?))
                } else {
                    MemberProperty::Static(
                        property
                            .key
                            .static_name()
                            .ok_or_else(|| anyhow!("property key chưa được hỗ trợ"))?
                            .into_owned(),
                    )
                };
                if property.kind != oxc_ast::ast::PropertyKind::Init {
                    let value = lower_expression(&property.value)?;
                    let (get, set) = match property.kind {
                        oxc_ast::ast::PropertyKind::Get => (Some(value), None),
                        oxc_ast::ast::PropertyKind::Set => (None, Some(value)),
                        oxc_ast::ast::PropertyKind::Init => unreachable!(),
                    };
                    let MemberProperty::Static(key) = key else {
                        bail!("computed accessor key chưa được hỗ trợ")
                    };
                    properties.push(ObjectEntry::Accessor { key, get, set });
                    continue;
                }
                // OXC represents object methods with a function-valued
                // property expression. Retaining that function is required by
                // the Promise resolution procedure for arbitrary thenables.
                properties.push(ObjectEntry::Property(ObjectProperty {
                    key,
                    value: lower_expression(&property.value)?,
                }));
            }
            (ExpressionKind::Object(properties), object.span)
        }
        Expression::ArrayExpression(array) => (
            ExpressionKind::Array(
                array
                    .elements
                    .iter()
                    .map(|element| match element {
                        ArrayExpressionElement::SpreadElement(spread) => {
                            Ok(ArrayElement::Spread(lower_expression(&spread.argument)?))
                        }
                        ArrayExpressionElement::Elision(_) => Ok(ArrayElement::Hole),
                        element => Ok(ArrayElement::Expression(lower_expression(
                            element
                                .as_expression()
                                .ok_or_else(|| anyhow!("array element không hợp lệ"))?,
                        )?)),
                    })
                    .collect::<Result<_>>()?,
            ),
            array.span,
        ),
        Expression::ConditionalExpression(expression) => (
            ExpressionKind::Conditional {
                test: Box::new(lower_expression(&expression.test)?),
                consequent: Box::new(lower_expression(&expression.consequent)?),
                alternate: Box::new(lower_expression(&expression.alternate)?),
            },
            expression.span,
        ),
        Expression::UnaryExpression(expression) => (
            ExpressionKind::Unary {
                operator: lower_unary_operator(expression.operator)?,
                argument: Box::new(lower_expression(&expression.argument)?),
            },
            expression.span,
        ),
        Expression::BinaryExpression(expression) => (
            ExpressionKind::Binary {
                left: Box::new(lower_expression(&expression.left)?),
                operator: lower_binary_operator(expression.operator)?,
                right: Box::new(lower_expression(&expression.right)?),
            },
            expression.span,
        ),
        Expression::LogicalExpression(expression) => (
            ExpressionKind::Logical {
                left: Box::new(lower_expression(&expression.left)?),
                operator: lower_logical_operator(expression.operator),
                right: Box::new(lower_expression(&expression.right)?),
            },
            expression.span,
        ),
        Expression::AssignmentExpression(expression) => (
            ExpressionKind::Assignment {
                target: lower_assignment_target(
                    expression
                        .left
                        .as_simple_assignment_target()
                        .ok_or_else(|| anyhow!("destructuring assignment chưa được hỗ trợ"))?,
                )?,
                operator: lower_assignment_operator(expression.operator),
                value: Box::new(lower_expression(&expression.right)?),
            },
            expression.span,
        ),
        Expression::UpdateExpression(expression) => (
            ExpressionKind::Update {
                target: lower_assignment_target(&expression.argument)?,
                operator: match expression.operator {
                    OxcUpdateOperator::Increment => UpdateOperator::Increment,
                    OxcUpdateOperator::Decrement => UpdateOperator::Decrement,
                },
                prefix: expression.prefix,
            },
            expression.span,
        ),
        Expression::CallExpression(call) => (
            ExpressionKind::Call {
                callee: Box::new(lower_expression(&call.callee)?),
                arguments: call
                    .arguments
                    .iter()
                    .map(lower_call_argument)
                    .collect::<Result<_>>()?,
            },
            call.span,
        ),
        Expression::ImportExpression(import) => (
            ExpressionKind::Call {
                callee: Box::new(HirExpression {
                    kind: ExpressionKind::Global("__ecmora_dynamic_import".to_owned()),
                    span: convert_span(import.span),
                }),
                arguments: vec![lower_expression(&import.source)?],
            },
            import.span,
        ),
        Expression::NewExpression(call) => (
            ExpressionKind::New {
                callee: Box::new(lower_expression(&call.callee)?),
                arguments: call
                    .arguments
                    .iter()
                    .map(lower_call_argument)
                    .collect::<Result<_>>()?,
            },
            call.span,
        ),
        Expression::FunctionExpression(function) => (
            ExpressionKind::Function(lower_function(function, false)?),
            function.span,
        ),
        Expression::ArrowFunctionExpression(function) => (
            ExpressionKind::Function(lower_arrow_function(function)?),
            function.span,
        ),
        Expression::AwaitExpression(expression) => (
            ExpressionKind::Await(Box::new(lower_expression(&expression.argument)?)),
            expression.span,
        ),
        Expression::YieldExpression(expression) => (
            ExpressionKind::Call {
                callee: Box::new(HirExpression {
                    kind: ExpressionKind::Global("@yield".to_owned()),
                    span: convert_span(expression.span),
                }),
                arguments: vec![
                    expression
                        .argument
                        .as_ref()
                        .map(lower_expression)
                        .transpose()?
                        .unwrap_or(HirExpression {
                            kind: ExpressionKind::Global("undefined".to_owned()),
                            span: convert_span(expression.span),
                        }),
                    HirExpression {
                        kind: ExpressionKind::Bool(expression.delegate),
                        span: convert_span(expression.span),
                    },
                ],
            },
            expression.span,
        ),
        unsupported => bail!("expression chưa được hỗ trợ trong HIR: {unsupported:#?}"),
    };
    Ok(HirExpression {
        kind,
        span: convert_span(span),
    })
}

fn lower_call_argument(argument: &oxc_ast::ast::Argument<'_>) -> Result<HirExpression> {
    match argument {
        oxc_ast::ast::Argument::SpreadElement(spread) => Ok(HirExpression {
            kind: ExpressionKind::Call {
                callee: Box::new(HirExpression {
                    kind: ExpressionKind::Global("@spread".to_owned()),
                    span: convert_span(spread.span),
                }),
                arguments: vec![lower_expression(&spread.argument)?],
            },
            span: convert_span(spread.span),
        }),
        _ => lower_expression(
            argument
                .as_expression()
                .ok_or_else(|| anyhow!("call argument không phải expression"))?,
        ),
    }
}
fn lower_function(function: &OxcFunction<'_>, arrow: bool) -> Result<HirFunction> {
    let mut lowering_error = None;
    let parameters = match lower_parameters(&function.params) {
        Ok(parameters) => parameters,
        Err(error) => {
            lowering_error.get_or_insert_with(|| format!("{error:#}"));
            Vec::new()
        }
    };
    let body = match function.body.as_ref() {
        Some(body) => match body
            .statements
            .iter()
            .map(lower_statement)
            .collect::<Result<Vec<_>>>()
        {
            Ok(body) => body,
            Err(error) => {
                lowering_error.get_or_insert_with(|| format!("{error:#}"));
                Vec::new()
            }
        },
        None => {
            lowering_error.get_or_insert_with(|| "function không có body".to_owned());
            Vec::new()
        }
    };
    Ok(HirFunction {
        name: function.id.as_ref().map(|id| id.name.to_string()),
        parameters,
        body,
        r#async: function.r#async,
        generator: function.generator,
        arrow,
        lowering_error,
    })
}

fn lower_arrow_function(function: &ArrowFunctionExpression<'_>) -> Result<HirFunction> {
    let parameters = lower_parameters(&function.params);
    let lowered_body = function
        .body
        .statements
        .iter()
        .map(lower_statement)
        .collect::<Result<Vec<_>>>();
    let mut lowering_error = parameters
        .as_ref()
        .err()
        .map(|error| format!("{error:#}"))
        .or_else(|| {
            lowered_body
                .as_ref()
                .err()
                .map(|error| format!("{error:#}"))
        });
    let parameters = parameters.unwrap_or_default();
    let mut body = lowered_body.unwrap_or_default();
    if lowering_error.is_none() && function.expression {
        if body.len() != 1 {
            lowering_error = Some("arrow expression body không hợp lệ".to_owned());
            body.clear();
        } else {
            let statement = body.pop().unwrap();
            if let StatementKind::Expression(expression) = statement.kind {
                body.push(HirStatement {
                    kind: StatementKind::Return(Some(expression)),
                    span: statement.span,
                });
            } else {
                lowering_error = Some("arrow expression body không phải expression".to_owned());
                body.clear();
            }
        }
    }
    Ok(HirFunction {
        name: None,
        parameters,
        body,
        r#async: function.r#async,
        generator: false,
        arrow: true,
        lowering_error,
    })
}

fn lower_parameters(parameters: &oxc_ast::ast::FormalParameters<'_>) -> Result<Vec<String>> {
    let mut output = parameters
        .items
        .iter()
        .map(|parameter| {
            if parameter.initializer.is_some() {
                bail!("default parameter chưa được hỗ trợ")
            }
            let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                bail!("destructuring parameter chưa được hỗ trợ")
            };
            Ok(identifier.name.to_string())
        })
        .collect::<Result<Vec<_>>>()?;

    if let Some(rest) = &parameters.rest {
        let BindingPattern::BindingIdentifier(identifier) = &rest.rest.argument else {
            bail!("destructuring rest parameter chưa được hỗ trợ")
        };
        output.push(format!("@rest:{}", identifier.name));
    }

    Ok(output)
}
fn lower_assignment_target(target: &SimpleAssignmentTarget<'_>) -> Result<AssignmentTarget> {
    match target {
        SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) => {
            Ok(AssignmentTarget::Identifier(identifier.name.to_string()))
        }
        SimpleAssignmentTarget::StaticMemberExpression(member) => Ok(AssignmentTarget::Member {
            object: Box::new(lower_expression(&member.object)?),
            property: MemberProperty::Static(member.property.name.to_string()),
        }),
        SimpleAssignmentTarget::ComputedMemberExpression(member) => Ok(AssignmentTarget::Member {
            object: Box::new(lower_expression(&member.object)?),
            property: MemberProperty::Computed(Box::new(lower_expression(&member.expression)?)),
        }),
        _ => bail!("assignment target chưa được hỗ trợ"),
    }
}

fn lower_unary_operator(operator: OxcUnaryOperator) -> Result<UnaryOperator> {
    match operator {
        OxcUnaryOperator::UnaryPlus => Ok(UnaryOperator::Plus),
        OxcUnaryOperator::UnaryNegation => Ok(UnaryOperator::Minus),
        OxcUnaryOperator::LogicalNot => Ok(UnaryOperator::Not),
        OxcUnaryOperator::BitwiseNot => Ok(UnaryOperator::BitwiseNot),
        OxcUnaryOperator::Typeof => Ok(UnaryOperator::Typeof),
        OxcUnaryOperator::Void => Ok(UnaryOperator::Void),
        OxcUnaryOperator::Delete => Ok(UnaryOperator::Delete),
    }
}

fn lower_binary_operator(operator: OxcBinaryOperator) -> Result<BinaryOperator> {
    Ok(match operator {
        OxcBinaryOperator::Addition => BinaryOperator::Add,
        OxcBinaryOperator::Subtraction => BinaryOperator::Subtract,
        OxcBinaryOperator::Multiplication => BinaryOperator::Multiply,
        OxcBinaryOperator::Division => BinaryOperator::Divide,
        OxcBinaryOperator::Remainder => BinaryOperator::Remainder,
        OxcBinaryOperator::Exponential => BinaryOperator::Exponential,
        OxcBinaryOperator::Equality => BinaryOperator::Equal,
        OxcBinaryOperator::Inequality => BinaryOperator::NotEqual,
        OxcBinaryOperator::StrictEquality => BinaryOperator::StrictEqual,
        OxcBinaryOperator::StrictInequality => BinaryOperator::StrictNotEqual,
        OxcBinaryOperator::LessThan => BinaryOperator::LessThan,
        OxcBinaryOperator::LessEqualThan => BinaryOperator::LessEqual,
        OxcBinaryOperator::GreaterThan => BinaryOperator::GreaterThan,
        OxcBinaryOperator::GreaterEqualThan => BinaryOperator::GreaterEqual,
        OxcBinaryOperator::ShiftLeft => BinaryOperator::ShiftLeft,
        OxcBinaryOperator::ShiftRight => BinaryOperator::ShiftRight,
        OxcBinaryOperator::ShiftRightZeroFill => BinaryOperator::ShiftRightZeroFill,
        OxcBinaryOperator::BitwiseOR => BinaryOperator::BitwiseOr,
        OxcBinaryOperator::BitwiseXOR => BinaryOperator::BitwiseXor,
        OxcBinaryOperator::BitwiseAnd => BinaryOperator::BitwiseAnd,
        OxcBinaryOperator::In => BinaryOperator::In,
        OxcBinaryOperator::Instanceof => BinaryOperator::InstanceOf,
    })
}

fn lower_logical_operator(operator: OxcLogicalOperator) -> LogicalOperator {
    match operator {
        OxcLogicalOperator::Or => LogicalOperator::Or,
        OxcLogicalOperator::And => LogicalOperator::And,
        OxcLogicalOperator::Coalesce => LogicalOperator::Nullish,
    }
}

fn lower_assignment_operator(operator: OxcAssignmentOperator) -> AssignmentOperator {
    match operator {
        OxcAssignmentOperator::Assign => AssignmentOperator::Assign,
        OxcAssignmentOperator::Addition => AssignmentOperator::Add,
        OxcAssignmentOperator::Subtraction => AssignmentOperator::Subtract,
        OxcAssignmentOperator::Multiplication => AssignmentOperator::Multiply,
        OxcAssignmentOperator::Division => AssignmentOperator::Divide,
        OxcAssignmentOperator::Remainder => AssignmentOperator::Remainder,
        OxcAssignmentOperator::Exponential => AssignmentOperator::Exponential,
        OxcAssignmentOperator::ShiftLeft => AssignmentOperator::ShiftLeft,
        OxcAssignmentOperator::ShiftRight => AssignmentOperator::ShiftRight,
        OxcAssignmentOperator::ShiftRightZeroFill => AssignmentOperator::ShiftRightZeroFill,
        OxcAssignmentOperator::BitwiseOR => AssignmentOperator::BitwiseOr,
        OxcAssignmentOperator::BitwiseXOR => AssignmentOperator::BitwiseXor,
        OxcAssignmentOperator::BitwiseAnd => AssignmentOperator::BitwiseAnd,
        OxcAssignmentOperator::LogicalOr => AssignmentOperator::LogicalOr,
        OxcAssignmentOperator::LogicalAnd => AssignmentOperator::LogicalAnd,
        OxcAssignmentOperator::LogicalNullish => AssignmentOperator::LogicalNullish,
    }
}

fn convert_span(span: OxcSpan) -> Span {
    Span::new(span.start, span.end)
}
