use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, Expression, ExpressionKind, ForInit,
    Function, MemberProperty, ObjectEntry, ObjectProperty, Program, Span, Statement, StatementKind,
    VariableDeclarator, VariableKind,
};
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct GeneratorTemplate {
    function: Function,
}

#[derive(Debug, Clone)]
struct GeneratorInstance {
    name: String,
    body: Vec<Statement>,
    cursor: usize,
    started: bool,
    done: bool,
    pending_resume: Option<AssignmentTarget>,
    delegate: Option<Box<GeneratorInstance>>,
}

#[derive(Debug, Clone)]
struct IterResult {
    value: Expression,
    done: bool,
    span: Span,
}

#[derive(Debug, Clone)]
enum StaticValue {
    Runtime(Expression),
    IterResult(IterResult),
}

#[derive(Debug, Clone)]
struct Lowered {
    prefix: Vec<Statement>,
    value: StaticValue,
}

/// Closed-world generator/iterator normalization.
///
/// Generator functions are never materialized as runtime generator objects. A local
/// generator call becomes a compile-time `GeneratorInstance`; each `.next()` / `.return()`
/// / `.throw()` resumes the source generator during HIR rewriting and emits only the
/// ordinary statements required by that suspension segment. IteratorResult objects are
/// similarly compile-time values and scalarize before ecmora-ir.
///
/// This pass deliberately rejects generator identities that escape or a yield nested under
/// runtime control flow. Those require the general resumable-CFG extension, not a C runtime
/// fallback. Straight-line generators, sent values, `yield*` over a local generator, and
/// statically finite `for..of` generator consumption are fully erased here.
pub(super) fn lower(program: &Program) -> Result<Program> {
    let templates = collect_templates(&program.statements)?;
    if templates.is_empty() {
        return Ok(program.clone());
    }

    let mut lowerer = GeneratorLowerer {
        templates,
        instances: HashMap::new(),
        results: HashMap::new(),
        next_instance: 0,
        next_name: 0,
        control_depth: 0,
    };
    let statements = lowerer.lower_statements(&program.statements)?;
    validate_erased(&statements)?;

    let mut output = program.clone();
    output.statements = statements;
    Ok(output)
}

fn collect_templates(statements: &[Statement]) -> Result<HashMap<String, GeneratorTemplate>> {
    let mut templates = HashMap::new();
    for statement in statements {
        if let StatementKind::FunctionDeclaration(function) = &statement.kind {
            if function.generator {
                let Some(name) = &function.name else {
                    bail!("generator declaration thiếu tên")
                };
                if templates
                    .insert(
                        name.clone(),
                        GeneratorTemplate {
                            function: function.clone(),
                        },
                    )
                    .is_some()
                {
                    bail!("generator `{name}` được khai báo trùng")
                }
            }
        }
    }
    Ok(templates)
}

struct GeneratorLowerer {
    templates: HashMap<String, GeneratorTemplate>,
    instances: HashMap<String, GeneratorInstance>,
    results: HashMap<String, IterResult>,
    next_instance: u32,
    next_name: u32,
    control_depth: usize,
}

impl GeneratorLowerer {
    fn fresh_name(&mut self, hint: &str) -> String {
        let id = self.next_name;
        self.next_name += 1;
        let hint: String = hint
            .chars()
            .map(|ch| {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    ch
                } else {
                    '_'
                }
            })
            .collect();
        format!("@gen_{hint}_{id}")
    }

    fn lower_statements(&mut self, statements: &[Statement]) -> Result<Vec<Statement>> {
        let mut output = Vec::new();
        for statement in statements {
            output.extend(self.lower_statement(statement)?);
        }
        Ok(output)
    }

    fn lower_statement(&mut self, statement: &Statement) -> Result<Vec<Statement>> {
        let span = statement.span;
        Ok(match &statement.kind {
            StatementKind::FunctionDeclaration(function) if function.generator => Vec::new(),
            StatementKind::VariableDeclaration { kind, declarations } => {
                let mut output = Vec::new();
                for declaration in declarations {
                    if let Some(init) = &declaration.init {
                        if let Some((template, arguments)) = self.generator_call(init) {
                            if self.control_depth != 0 {
                                bail!(
                                    "generator instance `{}` created under runtime control flow needs resumable identity SSA",
                                    declaration.name
                                )
                            }
                            let (instance, mut prefix) = self.instantiate(
                                &declaration.name,
                                &template,
                                &arguments,
                                declaration.span,
                            )?;
                            output.append(&mut prefix);
                            self.instances.insert(declaration.name.clone(), instance);
                            self.results.remove(&declaration.name);
                            continue;
                        }
                    }

                    let lowered = match &declaration.init {
                        Some(value) => Some(self.lower_expression(value)?),
                        None => None,
                    };
                    if let Some(Lowered {
                        mut prefix,
                        value: StaticValue::IterResult(result),
                    }) = lowered
                    {
                        output.append(&mut prefix);
                        self.results.insert(declaration.name.clone(), result);
                        self.instances.remove(&declaration.name);
                        continue;
                    }
                    let init = match lowered {
                        Some(mut lowered) => {
                            output.append(&mut lowered.prefix);
                            Some(require_runtime(lowered.value, "variable initializer")?)
                        }
                        None => None,
                    };
                    self.results.remove(&declaration.name);
                    self.instances.remove(&declaration.name);
                    output.push(variable_statement(
                        *kind,
                        declaration.name.clone(),
                        init,
                        declaration.span,
                    ));
                }
                output
            }
            StatementKind::Expression(expression) => {
                if let ExpressionKind::Assignment {
                    target: AssignmentTarget::Identifier(name),
                    operator: AssignmentOperator::Assign,
                    value,
                } = &expression.kind
                {
                    if let Some((template, arguments)) = self.generator_call(value) {
                        if self.control_depth != 0 {
                            bail!("generator identity reassignment under runtime control flow")
                        }
                        let (instance, prefix) =
                            self.instantiate(name, &template, &arguments, expression.span)?;
                        self.instances.insert(name.clone(), instance);
                        self.results.remove(name);
                        return Ok(prefix);
                    }
                    let lowered = self.lower_expression(value)?;
                    if let StaticValue::IterResult(result) = lowered.value {
                        self.results.insert(name.clone(), result);
                        self.instances.remove(name);
                        return Ok(lowered.prefix);
                    }
                }

                let mut lowered = self.lower_expression(expression)?;
                let mut output = Vec::new();
                output.append(&mut lowered.prefix);
                if let StaticValue::Runtime(value) = lowered.value {
                    output.push(expression_statement(value));
                }
                output
            }
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => {
                if let Some((template, arguments)) = self.generator_call(right) {
                    if self.control_depth != 0 {
                        bail!("nested generator for-of requires runtime resumable CFG fusion")
                    }
                    let temp_name = self.fresh_name("forof");
                    let (mut instance, mut output) =
                        self.instantiate(&temp_name, &template, &arguments, span)?;
                    let mut iterations = 0usize;
                    loop {
                        if iterations > 4096 {
                            bail!("generator for-of exceeded 4096 static suspension steps")
                        }
                        iterations += 1;
                        let (result, mut prefix) =
                            self.resume_instance(&mut instance, None, span)?;
                        output.append(&mut prefix);
                        if result.done {
                            break;
                        }
                        output.push(Statement {
                            kind: StatementKind::Block({
                                let mut block = vec![variable_statement(
                                    *kind,
                                    name.clone(),
                                    Some(result.value),
                                    span,
                                )];
                                self.control_depth += 1;
                                let lowered = self.lower_statement(body)?;
                                self.control_depth -= 1;
                                block.extend(lowered);
                                block
                            }),
                            span,
                        });
                    }
                    output
                } else if let ExpressionKind::Global(instance_name) = &right.kind {
                    if let Some(mut instance) = self.instances.remove(instance_name) {
                        if self.control_depth != 0 {
                            bail!("generator instance for-of under runtime control flow")
                        }
                        let mut output = Vec::new();
                        let mut iterations = 0usize;
                        loop {
                            if iterations > 4096 {
                                bail!("generator for-of exceeded 4096 static suspension steps")
                            }
                            iterations += 1;
                            let (result, mut prefix) =
                                self.resume_instance(&mut instance, None, span)?;
                            output.append(&mut prefix);
                            if result.done {
                                break;
                            }
                            output.push(Statement {
                                kind: StatementKind::Block({
                                    let mut block = vec![variable_statement(
                                        *kind,
                                        name.clone(),
                                        Some(result.value),
                                        span,
                                    )];
                                    self.control_depth += 1;
                                    let lowered = self.lower_statement(body)?;
                                    self.control_depth -= 1;
                                    block.extend(lowered);
                                    block
                                }),
                                span,
                            });
                        }
                        self.instances.insert(instance_name.clone(), instance);
                        output
                    } else {
                        self.lower_runtime_for_of(name, *kind, right, body, span)?
                    }
                } else {
                    self.lower_runtime_for_of(name, *kind, right, body, span)?
                }
            }
            StatementKind::Block(body) => {
                self.control_depth += 1;
                let body = self.lower_statements(body)?;
                self.control_depth -= 1;
                vec![Statement {
                    kind: StatementKind::Block(body),
                    span,
                }]
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                let test = self.lower_expression(test)?;
                if !test.prefix.is_empty() || !matches!(test.value, StaticValue::Runtime(_)) {
                    bail!(
                        "generator/static iterator side effects in if condition need CFG normalization"
                    )
                }
                self.control_depth += 1;
                let consequent = single(self.lower_statement(consequent)?, span);
                let alternate = alternate
                    .as_deref()
                    .map(|value| {
                        self.lower_statement(value)
                            .map(|body| Box::new(single(body, span)))
                    })
                    .transpose()?;
                self.control_depth -= 1;
                vec![Statement {
                    kind: StatementKind::If {
                        test: require_runtime(test.value, "if test")?,
                        consequent: Box::new(consequent),
                        alternate,
                    },
                    span,
                }]
            }
            StatementKind::While { test, body } => {
                if statement_contains_yield(body) {
                    bail!(
                        "yield nested in while needs general resumable CFG state-machine lowering"
                    )
                }
                let test = require_runtime(self.lower_expression(test)?.value, "while test")?;
                self.control_depth += 1;
                let body = single(self.lower_statement(body)?, span);
                self.control_depth -= 1;
                vec![Statement {
                    kind: StatementKind::While {
                        test,
                        body: Box::new(body),
                    },
                    span,
                }]
            }
            StatementKind::DoWhile { body, test } => {
                if statement_contains_yield(body) {
                    bail!(
                        "yield nested in do-while needs general resumable CFG state-machine lowering"
                    )
                }
                self.control_depth += 1;
                let body = single(self.lower_statement(body)?, span);
                self.control_depth -= 1;
                let test = require_runtime(self.lower_expression(test)?.value, "do-while test")?;
                vec![Statement {
                    kind: StatementKind::DoWhile {
                        body: Box::new(body),
                        test,
                    },
                    span,
                }]
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                if statement_contains_yield(body) {
                    bail!("yield nested in for needs general resumable CFG state-machine lowering")
                }
                let init = init.clone();
                let test = test.clone();
                let update = update.clone();
                self.control_depth += 1;
                let body = single(self.lower_statement(body)?, span);
                self.control_depth -= 1;
                vec![Statement {
                    kind: StatementKind::For {
                        init,
                        test,
                        update,
                        body: Box::new(body),
                    },
                    span,
                }]
            }
            StatementKind::ForIn { .. } => vec![statement.clone()],
            StatementKind::Switch { cases, .. }
                if cases
                    .iter()
                    .flat_map(|case| &case.consequent)
                    .any(statement_contains_yield) =>
            {
                bail!("yield nested in switch needs general resumable CFG state-machine lowering")
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => vec![Statement {
                kind: StatementKind::Switch {
                    discriminant: require_runtime(
                        self.lower_expression(discriminant)?.value,
                        "switch discriminant",
                    )?,
                    cases: cases.clone(),
                },
                span,
            }],
            StatementKind::Labeled { body, .. } if statement_contains_yield(body) => {
                bail!("yield nested in labeled statement needs resumable CFG lowering")
            }
            StatementKind::Try { .. } if statement_contains_yield(statement) => {
                bail!("yield crossing try/catch/finally needs generator completion-state lowering")
            }
            StatementKind::FunctionDeclaration(function) => {
                let mut function = function.clone();
                function.body = self.lower_nested_function_body(&function.body)?;
                vec![Statement {
                    kind: StatementKind::FunctionDeclaration(function),
                    span,
                }]
            }
            StatementKind::Return(value) => {
                let value = value
                    .as_ref()
                    .map(|value| self.lower_expression(value))
                    .transpose()?;
                let mut output = Vec::new();
                let value = match value {
                    Some(mut value) => {
                        output.append(&mut value.prefix);
                        Some(require_runtime(value.value, "return value")?)
                    }
                    None => None,
                };
                output.push(Statement {
                    kind: StatementKind::Return(value),
                    span,
                });
                output
            }
            StatementKind::Throw(value) => {
                let value = self.lower_expression(value)?;
                let mut output = value.prefix;
                output.push(Statement {
                    kind: StatementKind::Throw(require_runtime(value.value, "throw value")?),
                    span,
                });
                output
            }
            StatementKind::Try { .. }
            | StatementKind::Labeled { .. }
            | StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => vec![statement.clone()],
        })
    }

    fn lower_runtime_for_of(
        &mut self,
        name: &str,
        kind: VariableKind,
        right: &Expression,
        body: &Statement,
        span: Span,
    ) -> Result<Vec<Statement>> {
        let right = self.lower_expression(right)?;
        if !right.prefix.is_empty() {
            bail!("iterator side effects in runtime for-of source need normalization")
        }
        self.control_depth += 1;
        let body = single(self.lower_statement(body)?, span);
        self.control_depth -= 1;
        Ok(vec![Statement {
            kind: StatementKind::ForOf {
                name: name.to_owned(),
                kind,
                right: require_runtime(right.value, "for-of source")?,
                body: Box::new(body),
            },
            span,
        }])
    }

    fn lower_nested_function_body(&mut self, body: &[Statement]) -> Result<Vec<Statement>> {
        // Generator instances are lexical compile-time identities. Do not leak the outer
        // instance table into an independently called nested function.
        let saved_instances = std::mem::take(&mut self.instances);
        let saved_results = std::mem::take(&mut self.results);
        let result = self.lower_statements(body);
        self.instances = saved_instances;
        self.results = saved_results;
        result
    }

    fn generator_call(
        &self,
        expression: &Expression,
    ) -> Option<(GeneratorTemplate, Vec<Expression>)> {
        let ExpressionKind::Call { callee, arguments } = &expression.kind else {
            return None;
        };
        let ExpressionKind::Global(name) = &callee.kind else {
            return None;
        };
        self.templates
            .get(name)
            .cloned()
            .map(|template| (template, arguments.clone()))
    }

    fn instantiate(
        &mut self,
        binding_name: &str,
        template: &GeneratorTemplate,
        arguments: &[Expression],
        span: Span,
    ) -> Result<(GeneratorInstance, Vec<Statement>)> {
        if template.function.r#async {
            bail!("async generator needs async-generator request queue state machine")
        }
        if let Some(error) = &template.function.lowering_error {
            bail!("generator frontend lowering failed: {error}")
        }
        let id = self.next_instance;
        self.next_instance += 1;
        let mut mapping = HashMap::new();
        for parameter in &template.function.parameters {
            if parameter.starts_with("@rest:") {
                bail!("generator rest parameter needs tuple argv lowering")
            }
            mapping.insert(
                parameter.clone(),
                self.fresh_name(&format!("{binding_name}_{parameter}")),
            );
        }
        collect_local_names(&template.function.body, &mut |name| {
            mapping.entry(name.to_owned()).or_insert_with(|| {
                format!(
                    "@gen_local_{}_{}_{}",
                    id,
                    sanitize(binding_name),
                    sanitize(name)
                )
            });
        });
        let body = template
            .function
            .body
            .iter()
            .map(|statement| rename_statement(statement, &mapping))
            .collect::<Result<Vec<_>>>()?;
        validate_generator_body(&body)?;

        let mut prefix = Vec::new();
        for (index, parameter) in template.function.parameters.iter().enumerate() {
            let renamed = mapping[parameter].clone();
            let argument = arguments
                .get(index)
                .map(|value| self.lower_expression(value))
                .transpose()?;
            let value = match argument {
                Some(mut value) => {
                    prefix.append(&mut value.prefix);
                    require_runtime(value.value, "generator argument")?
                }
                None => undefined_expression(span),
            };
            prefix.push(variable_statement(
                VariableKind::Let,
                renamed,
                Some(value),
                span,
            ));
        }
        for extra in arguments.iter().skip(template.function.parameters.len()) {
            let mut extra = self.lower_expression(extra)?;
            prefix.append(&mut extra.prefix);
            if let StaticValue::Runtime(value) = extra.value {
                prefix.push(expression_statement(value));
            }
        }

        Ok((
            GeneratorInstance {
                name: binding_name.to_owned(),
                body,
                cursor: 0,
                started: false,
                done: false,
                pending_resume: None,
                delegate: None,
            },
            prefix,
        ))
    }

    fn resume_instance(
        &mut self,
        instance: &mut GeneratorInstance,
        sent: Option<Expression>,
        span: Span,
    ) -> Result<(IterResult, Vec<Statement>)> {
        let mut prefix = Vec::new();
        let sent = match sent {
            Some(value) => {
                let mut value = self.lower_expression(&value)?;
                prefix.append(&mut value.prefix);
                require_runtime(value.value, "generator next argument")?
            }
            None => undefined_expression(span),
        };

        if instance.done {
            return Ok((
                IterResult {
                    value: undefined_expression(span),
                    done: true,
                    span,
                },
                prefix,
            ));
        }

        if instance.started {
            if let Some(target) = instance.pending_resume.take() {
                prefix.push(Statement {
                    kind: StatementKind::Expression(Expression {
                        kind: ExpressionKind::Assignment {
                            target,
                            operator: AssignmentOperator::Assign,
                            value: Box::new(sent.clone()),
                        },
                        span,
                    }),
                    span,
                });
            }
        } else {
            // Per ECMAScript, the argument to the first next() is ignored by the generator body.
            instance.started = true;
        }

        loop {
            if let Some(delegate) = instance.delegate.as_mut() {
                let (result, mut delegated_prefix) =
                    self.resume_instance(delegate, Some(sent.clone()), span)?;
                prefix.append(&mut delegated_prefix);
                if !result.done {
                    return Ok((
                        IterResult {
                            value: result.value,
                            done: false,
                            span,
                        },
                        prefix,
                    ));
                }
                instance.delegate = None;
                instance.cursor += 1;
                continue;
            }

            if instance.cursor >= instance.body.len() {
                instance.done = true;
                return Ok((
                    IterResult {
                        value: undefined_expression(span),
                        done: true,
                        span,
                    },
                    prefix,
                ));
            }

            let statement = instance.body[instance.cursor].clone();
            match classify_suspension(&statement)? {
                Suspension::None => {
                    if statement_contains_yield(&statement) {
                        bail!(
                            "generator `{}` has yield nested under runtime control flow; general resumable CFG state machine is required",
                            instance.name
                        )
                    }
                    prefix.extend(self.lower_statement(&statement)?);
                    instance.cursor += 1;
                }
                Suspension::Yield { value, resume } => {
                    // `const/let x = yield value` creates the lexical binding before
                    // suspension, but its initializer completes only on resume. HIR
                    // has no explicit uninitialized lexical slot, so use an internal
                    // mutable slot that is written exactly once by pending_resume.
                    // The renamed generator-local binding never escapes this pass.
                    if let StatementKind::VariableDeclaration { declarations, .. } = &statement.kind
                    {
                        if declarations.len() == 1 && resume.is_some() {
                            prefix.push(variable_statement(
                                VariableKind::Let,
                                declarations[0].name.clone(),
                                None,
                                statement.span,
                            ));
                        }
                    }
                    let mut value = self.lower_expression(&value)?;
                    prefix.append(&mut value.prefix);
                    let value = require_runtime(value.value, "yield value")?;
                    instance.pending_resume = resume;
                    instance.cursor += 1;
                    return Ok((
                        IterResult {
                            value,
                            done: false,
                            span,
                        },
                        prefix,
                    ));
                }
                Suspension::YieldDelegate { value } => {
                    let Some((template, arguments)) = self.generator_call(&value) else {
                        bail!("yield* source must be a local statically known generator")
                    };
                    let delegate_name = self.fresh_name("delegate");
                    let (delegate, mut delegate_prefix) =
                        self.instantiate(&delegate_name, &template, &arguments, value.span)?;
                    prefix.append(&mut delegate_prefix);
                    instance.delegate = Some(Box::new(delegate));
                }
                Suspension::Return(value) => {
                    let value = match value {
                        Some(value) => {
                            let mut value = self.lower_expression(&value)?;
                            prefix.append(&mut value.prefix);
                            require_runtime(value.value, "generator return")?
                        }
                        None => undefined_expression(span),
                    };
                    instance.done = true;
                    instance.cursor = instance.body.len();
                    return Ok((
                        IterResult {
                            value,
                            done: true,
                            span,
                        },
                        prefix,
                    ));
                }
                Suspension::Throw(value) => {
                    let mut value = self.lower_expression(&value)?;
                    prefix.append(&mut value.prefix);
                    prefix.push(Statement {
                        kind: StatementKind::Throw(require_runtime(
                            value.value,
                            "generator throw",
                        )?),
                        span,
                    });
                    instance.done = true;
                    instance.cursor = instance.body.len();
                    return Ok((
                        IterResult {
                            value: undefined_expression(span),
                            done: true,
                            span,
                        },
                        prefix,
                    ));
                }
            }
        }
    }

    fn lower_expression(&mut self, expression: &Expression) -> Result<Lowered> {
        let span = expression.span;
        if let ExpressionKind::Call { callee, arguments } = &expression.kind {
            if let ExpressionKind::Member {
                object,
                property: MemberProperty::Static(method),
            } = &callee.kind
            {
                if let ExpressionKind::Global(name) = &object.kind {
                    if self.instances.contains_key(name)
                        && matches!(method.as_str(), "next" | "return" | "throw")
                    {
                        if self.control_depth != 0 {
                            bail!(
                                "generator `{name}` resumed under runtime control flow; closed-world resume needs a general PC SSA state machine"
                            )
                        }
                        let mut instance = self.instances.remove(name).expect("generator instance");
                        let result = match method.as_str() {
                            "next" => {
                                if arguments.len() > 1 {
                                    bail!("Generator.next accepts at most one value")
                                }
                                self.resume_instance(
                                    &mut instance,
                                    arguments.first().cloned(),
                                    span,
                                )?
                            }
                            "return" => {
                                if arguments.len() > 1 {
                                    bail!("Generator.return accepts at most one value")
                                }
                                let mut prefix = Vec::new();
                                let value = match arguments.first() {
                                    Some(value) => {
                                        let mut value = self.lower_expression(value)?;
                                        prefix.append(&mut value.prefix);
                                        require_runtime(value.value, "Generator.return value")?
                                    }
                                    None => undefined_expression(span),
                                };
                                instance.done = true;
                                instance.cursor = instance.body.len();
                                (
                                    IterResult {
                                        value,
                                        done: true,
                                        span,
                                    },
                                    prefix,
                                )
                            }
                            "throw" => {
                                if arguments.len() != 1 {
                                    bail!("Generator.throw requires one value")
                                }
                                let value = self.lower_expression(&arguments[0])?;
                                let mut prefix = value.prefix;
                                prefix.push(Statement {
                                    kind: StatementKind::Throw(require_runtime(
                                        value.value,
                                        "Generator.throw value",
                                    )?),
                                    span,
                                });
                                instance.done = true;
                                instance.cursor = instance.body.len();
                                (
                                    IterResult {
                                        value: undefined_expression(span),
                                        done: true,
                                        span,
                                    },
                                    prefix,
                                )
                            }
                            _ => unreachable!(),
                        };
                        self.instances.insert(name.clone(), instance);
                        return Ok(Lowered {
                            prefix: result.1,
                            value: StaticValue::IterResult(result.0),
                        });
                    }
                }
            }
        }

        match &expression.kind {
            ExpressionKind::Global(name) => {
                if let Some(result) = self.results.get(name).cloned() {
                    return Ok(Lowered {
                        prefix: Vec::new(),
                        value: StaticValue::IterResult(result),
                    });
                }
                if self.instances.contains_key(name) {
                    bail!(
                        "generator object `{name}` identity escaped; no runtime generator object is emitted"
                    )
                }
                Ok(runtime(expression.clone()))
            }
            ExpressionKind::Member { object, property } => {
                let mut object = self.lower_expression(object)?;
                if let StaticValue::IterResult(result) = object.value {
                    let MemberProperty::Static(key) = property else {
                        bail!("computed IteratorResult property needs object materialization")
                    };
                    let value = match key.as_str() {
                        "value" => result.value,
                        "done" => Expression {
                            kind: ExpressionKind::Bool(result.done),
                            span,
                        },
                        _ => bail!(
                            "IteratorResult has no static property `{key}` in native scalar form"
                        ),
                    };
                    return Ok(Lowered {
                        prefix: object.prefix,
                        value: StaticValue::Runtime(value),
                    });
                }
                let object_value = require_runtime(object.value, "member object")?;
                let property = match property {
                    MemberProperty::Static(key) => MemberProperty::Static(key.clone()),
                    MemberProperty::Computed(value) => {
                        let mut value = self.lower_expression(value)?;
                        object.prefix.append(&mut value.prefix);
                        MemberProperty::Computed(Box::new(require_runtime(
                            value.value,
                            "computed key",
                        )?))
                    }
                };
                Ok(Lowered {
                    prefix: object.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Member {
                            object: Box::new(object_value),
                            property,
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Call { callee, arguments } => {
                if let Some((_, _)) = self.generator_call(expression) {
                    bail!(
                        "generator call result must be bound locally or consumed by static for-of"
                    )
                }
                let callee = self.lower_expression(callee)?;
                let mut prefix = callee.prefix;
                let callee = require_runtime(callee.value, "call callee")?;
                let mut args = Vec::new();
                for argument in arguments {
                    let mut argument = self.lower_expression(argument)?;
                    prefix.append(&mut argument.prefix);
                    args.push(require_runtime(argument.value, "call argument")?);
                }
                Ok(Lowered {
                    prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Call {
                            callee: Box::new(callee),
                            arguments: args,
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Assignment {
                target: AssignmentTarget::Identifier(name),
                operator: AssignmentOperator::Assign,
                value,
            } => {
                let value = self.lower_expression(value)?;
                if let StaticValue::IterResult(result) = value.value {
                    self.results.insert(name.clone(), result.clone());
                    return Ok(Lowered {
                        prefix: value.prefix,
                        value: StaticValue::IterResult(result),
                    });
                }
                self.results.remove(name);
                let runtime_value = require_runtime(value.value, "assignment value")?;
                Ok(Lowered {
                    prefix: value.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Assignment {
                            target: AssignmentTarget::Identifier(name.clone()),
                            operator: AssignmentOperator::Assign,
                            value: Box::new(runtime_value),
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Object(entries) => self.lower_object(entries, span),
            ExpressionKind::Array(elements) => {
                let mut prefix = Vec::new();
                let mut out = Vec::new();
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) => {
                            let mut value = self.lower_expression(value)?;
                            prefix.append(&mut value.prefix);
                            out.push(ArrayElement::Expression(require_runtime(
                                value.value,
                                "array element",
                            )?));
                        }
                        ArrayElement::Spread(value) => {
                            let mut value = self.lower_expression(value)?;
                            prefix.append(&mut value.prefix);
                            out.push(ArrayElement::Spread(require_runtime(
                                value.value,
                                "array spread",
                            )?));
                        }
                        ArrayElement::Hole => out.push(ArrayElement::Hole),
                    }
                }
                Ok(Lowered {
                    prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Array(out),
                        span,
                    }),
                })
            }
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => {
                let test = self.lower_expression(test)?;
                let consequent = self.lower_expression(consequent)?;
                let alternate = self.lower_expression(alternate)?;
                if !consequent.prefix.is_empty()
                    || !alternate.prefix.is_empty()
                    || !matches!(consequent.value, StaticValue::Runtime(_))
                    || !matches!(alternate.value, StaticValue::Runtime(_))
                {
                    bail!(
                        "iterator result across conditional expression needs value-phi normalization"
                    )
                }
                Ok(Lowered {
                    prefix: test.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Conditional {
                            test: Box::new(require_runtime(test.value, "conditional test")?),
                            consequent: Box::new(require_runtime(
                                consequent.value,
                                "conditional consequent",
                            )?),
                            alternate: Box::new(require_runtime(
                                alternate.value,
                                "conditional alternate",
                            )?),
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Unary { operator, argument } => {
                let argument = self.lower_expression(argument)?;
                Ok(Lowered {
                    prefix: argument.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Unary {
                            operator: *operator,
                            argument: Box::new(require_runtime(argument.value, "unary")?),
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => self.binary(left, *operator, right, span),
            ExpressionKind::Logical {
                left,
                operator,
                right,
            } => {
                let left = self.lower_expression(left)?;
                let right = self.lower_expression(right)?;
                if !right.prefix.is_empty() {
                    bail!("iterator side effects in logical RHS need CFG normalization")
                }
                Ok(Lowered {
                    prefix: left.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Logical {
                            left: Box::new(require_runtime(left.value, "logical left")?),
                            operator: *operator,
                            right: Box::new(require_runtime(right.value, "logical right")?),
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => {
                let value = self.lower_expression(value)?;
                Ok(Lowered {
                    prefix: value.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Assignment {
                            target: target.clone(),
                            operator: *operator,
                            value: Box::new(require_runtime(value.value, "assignment")?),
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Update { .. }
            | ExpressionKind::New { .. }
            | ExpressionKind::Function(_)
            | ExpressionKind::Await(_)
            | ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This => Ok(runtime(expression.clone())),
        }
    }

    fn lower_object(&mut self, entries: &[ObjectEntry], span: Span) -> Result<Lowered> {
        let mut prefix = Vec::new();
        let mut out = Vec::new();
        for entry in entries {
            match entry {
                ObjectEntry::Property(property) => {
                    let mut value = self.lower_expression(&property.value)?;
                    prefix.append(&mut value.prefix);
                    out.push(ObjectEntry::Property(ObjectProperty {
                        key: property.key.clone(),
                        value: materialize(value.value)?,
                    }));
                }
                ObjectEntry::Spread(value) => {
                    let mut value = self.lower_expression(value)?;
                    prefix.append(&mut value.prefix);
                    out.push(ObjectEntry::Spread(materialize(value.value)?));
                }
                ObjectEntry::Accessor { .. } => out.push(entry.clone()),
            }
        }
        Ok(Lowered {
            prefix,
            value: StaticValue::Runtime(Expression {
                kind: ExpressionKind::Object(out),
                span,
            }),
        })
    }

    fn binary(
        &mut self,
        left: &Expression,
        operator: ecmora_hir::BinaryOperator,
        right: &Expression,
        span: Span,
    ) -> Result<Lowered> {
        let left = self.lower_expression(left)?;
        let mut right = self.lower_expression(right)?;
        let mut prefix = left.prefix;
        prefix.append(&mut right.prefix);
        Ok(Lowered {
            prefix,
            value: StaticValue::Runtime(Expression {
                kind: ExpressionKind::Binary {
                    left: Box::new(require_runtime(left.value, "binary left")?),
                    operator,
                    right: Box::new(require_runtime(right.value, "binary right")?),
                },
                span,
            }),
        })
    }
}

fn yield_marker(expression: &Expression) -> Option<(Expression, bool)> {
    let ExpressionKind::Call { callee, arguments } = &expression.kind else {
        return None;
    };
    if !matches!(&callee.kind, ExpressionKind::Global(name) if name == "@yield") {
        return None;
    }
    let [value, delegate] = arguments.as_slice() else {
        return None;
    };
    let ExpressionKind::Bool(delegate) = &delegate.kind else {
        return None;
    };
    Some((value.clone(), *delegate))
}

#[derive(Debug)]
enum Suspension {
    None,
    Yield {
        value: Expression,
        resume: Option<AssignmentTarget>,
    },
    YieldDelegate {
        value: Expression,
    },
    Return(Option<Expression>),
    Throw(Expression),
}

fn classify_suspension(statement: &Statement) -> Result<Suspension> {
    match &statement.kind {
        StatementKind::Expression(value) if yield_marker(value).is_some() => {
            let (value, delegate) = yield_marker(value).expect("yield marker");
            Ok(if delegate {
                Suspension::YieldDelegate { value }
            } else {
                Suspension::Yield {
                    value,
                    resume: None,
                }
            })
        }
        StatementKind::VariableDeclaration { declarations, .. } if declarations.len() == 1 => {
            let declaration = &declarations[0];
            if let Some(init) = &declaration.init {
                if let Some((value, delegate)) = yield_marker(init) {
                    if delegate {
                        bail!("`let x = yield* ...` needs delegate completion-value lowering")
                    }
                    return Ok(Suspension::Yield {
                        value,
                        resume: Some(AssignmentTarget::Identifier(declaration.name.clone())),
                    });
                }
            }
            Ok(Suspension::None)
        }
        StatementKind::Expression(Expression {
            kind:
                ExpressionKind::Assignment {
                    target,
                    operator: AssignmentOperator::Assign,
                    value,
                },
            ..
        }) => {
            if let Some((yielded, delegate)) = yield_marker(value) {
                if delegate {
                    bail!("assignment from yield* needs delegate completion-value lowering")
                }
                return Ok(Suspension::Yield {
                    value: yielded,
                    resume: Some(target.clone()),
                });
            }
            Ok(Suspension::None)
        }
        StatementKind::Return(value) => Ok(Suspension::Return(value.clone())),
        StatementKind::Throw(value) => Ok(Suspension::Throw(value.clone())),
        _ => Ok(Suspension::None),
    }
}

fn validate_generator_body(body: &[Statement]) -> Result<()> {
    for statement in body {
        if statement_contains_yield(statement) && !is_direct_suspension(statement) {
            bail!(
                "yield nested under runtime control flow is not yet representable by the static-resume generator path; general PC/phi resumable CFG is required"
            )
        }
    }
    Ok(())
}

fn is_direct_suspension(statement: &Statement) -> bool {
    matches!(
        classify_suspension(statement),
        Ok(Suspension::Yield { .. } | Suspension::YieldDelegate { .. })
    )
}

fn statement_contains_yield(statement: &Statement) -> bool {
    fn expression(value: &Expression) -> bool {
        match &value.kind {
            ExpressionKind::Call { callee, .. } if matches!(&callee.kind, ExpressionKind::Global(name) if name == "@yield") => {
                true
            }
            ExpressionKind::Member { object, property } => {
                expression(object)
                    || matches!(property, MemberProperty::Computed(value) if expression(value))
            }
            ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
                ObjectEntry::Property(property) => expression(&property.value),
                ObjectEntry::Spread(value) => expression(value),
                ObjectEntry::Accessor { get, set, .. } => {
                    get.as_ref().is_some_and(expression) || set.as_ref().is_some_and(expression)
                }
            }),
            ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
                ArrayElement::Expression(value) | ArrayElement::Spread(value) => expression(value),
                ArrayElement::Hole => false,
            }),
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => expression(test) || expression(consequent) || expression(alternate),
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expression(argument)
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => expression(left) || expression(right),
            ExpressionKind::Assignment { value, .. } => expression(value),
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                expression(callee) || arguments.iter().any(expression)
            }
            ExpressionKind::Function(_)
            | ExpressionKind::Update { .. }
            | ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This
            | ExpressionKind::Global(_) => false,
        }
    }
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => expression(value),
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|value| value.init.as_ref())
            .any(expression),
        StatementKind::Block(body) => body.iter().any(statement_contains_yield),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression(test)
                || statement_contains_yield(consequent)
                || alternate.as_deref().is_some_and(statement_contains_yield)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression(test) || statement_contains_yield(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => expression(value),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|value| value.init.as_ref())
                    .any(expression),
            }) || test.as_ref().is_some_and(expression)
                || update.as_ref().is_some_and(expression)
                || statement_contains_yield(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expression(right) || statement_contains_yield(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expression(discriminant)
                || cases.iter().any(|case| {
                    case.test.as_ref().is_some_and(expression)
                        || case.consequent.iter().any(statement_contains_yield)
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
                    .is_some_and(|value| statement_contains_yield(&value.body))
                || finalizer.as_deref().is_some_and(statement_contains_yield)
        }
        StatementKind::FunctionDeclaration(_) => false,
        StatementKind::Return(value) => value.as_ref().is_some_and(expression),
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn collect_local_names(body: &[Statement], f: &mut impl FnMut(&str)) {
    for statement in body {
        match &statement.kind {
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    f(&declaration.name);
                }
            }
            StatementKind::Block(body) => collect_local_names(body, f),
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                collect_local_names(std::slice::from_ref(consequent.as_ref()), f);
                if let Some(value) = alternate {
                    collect_local_names(std::slice::from_ref(value.as_ref()), f);
                }
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Labeled { body, .. } => {
                collect_local_names(std::slice::from_ref(body.as_ref()), f)
            }
            StatementKind::For { init, body, .. } => {
                if let Some(ForInit::VariableDeclaration { declarations, .. }) = init {
                    for declaration in declarations {
                        f(&declaration.name);
                    }
                }
                collect_local_names(std::slice::from_ref(body.as_ref()), f);
            }
            StatementKind::ForIn { name, body, .. } | StatementKind::ForOf { name, body, .. } => {
                f(name);
                collect_local_names(std::slice::from_ref(body.as_ref()), f);
            }
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    collect_local_names(&case.consequent, f);
                }
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                collect_local_names(std::slice::from_ref(block.as_ref()), f);
                if let Some(handler) = handler {
                    if let Some(name) = &handler.parameter {
                        f(name);
                    }
                    collect_local_names(std::slice::from_ref(handler.body.as_ref()), f);
                }
                if let Some(finalizer) = finalizer {
                    collect_local_names(std::slice::from_ref(finalizer.as_ref()), f);
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
}

fn rename_statement(statement: &Statement, mapping: &HashMap<String, String>) -> Result<Statement> {
    let mut statement = statement.clone();
    rename_statement_mut(&mut statement, mapping)?;
    Ok(statement)
}

fn rename_statement_mut(
    statement: &mut Statement,
    mapping: &HashMap<String, String>,
) -> Result<()> {
    match &mut statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            rename_expression_mut(value, mapping)?
        }
        StatementKind::VariableDeclaration { declarations, .. } => {
            for declaration in declarations {
                if let Some(name) = mapping.get(&declaration.name) {
                    declaration.name = name.clone();
                }
                if let Some(value) = &mut declaration.init {
                    rename_expression_mut(value, mapping)?;
                }
            }
        }
        StatementKind::Block(body) => {
            for value in body {
                rename_statement_mut(value, mapping)?;
            }
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            rename_expression_mut(test, mapping)?;
            rename_statement_mut(consequent, mapping)?;
            if let Some(value) = alternate {
                rename_statement_mut(value, mapping)?;
            }
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            rename_expression_mut(test, mapping)?;
            rename_statement_mut(body, mapping)?;
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            if let Some(init) = init {
                match init {
                    ForInit::Expression(value) => rename_expression_mut(value, mapping)?,
                    ForInit::VariableDeclaration { declarations, .. } => {
                        for declaration in declarations {
                            if let Some(name) = mapping.get(&declaration.name) {
                                declaration.name = name.clone();
                            }
                            if let Some(value) = &mut declaration.init {
                                rename_expression_mut(value, mapping)?;
                            }
                        }
                    }
                }
            }
            if let Some(value) = test {
                rename_expression_mut(value, mapping)?;
            }
            if let Some(value) = update {
                rename_expression_mut(value, mapping)?;
            }
            rename_statement_mut(body, mapping)?;
        }
        StatementKind::ForIn {
            name, right, body, ..
        }
        | StatementKind::ForOf {
            name, right, body, ..
        } => {
            if let Some(value) = mapping.get(name) {
                *name = value.clone();
            }
            rename_expression_mut(right, mapping)?;
            rename_statement_mut(body, mapping)?;
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            rename_expression_mut(discriminant, mapping)?;
            for case in cases {
                if let Some(value) = &mut case.test {
                    rename_expression_mut(value, mapping)?;
                }
                for statement in &mut case.consequent {
                    rename_statement_mut(statement, mapping)?;
                }
            }
        }
        StatementKind::Labeled { body, .. } => rename_statement_mut(body, mapping)?,
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            rename_statement_mut(block, mapping)?;
            if let Some(handler) = handler {
                if let Some(name) = &mut handler.parameter {
                    if let Some(value) = mapping.get(name) {
                        *name = value.clone();
                    }
                }
                rename_statement_mut(&mut handler.body, mapping)?;
            }
            if let Some(value) = finalizer {
                rename_statement_mut(value, mapping)?;
            }
        }
        StatementKind::FunctionDeclaration(_) => {}
        StatementKind::Return(value) => {
            if let Some(value) = value {
                rename_expression_mut(value, mapping)?;
            }
        }
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => {}
    }
    Ok(())
}

fn rename_expression_mut(value: &mut Expression, mapping: &HashMap<String, String>) -> Result<()> {
    match &mut value.kind {
        ExpressionKind::Global(name) => {
            if let Some(value) = mapping.get(name) {
                *name = value.clone();
            }
        }
        ExpressionKind::Member { object, property } => {
            rename_expression_mut(object, mapping)?;
            if let MemberProperty::Computed(value) = property {
                rename_expression_mut(value, mapping)?;
            }
        }
        ExpressionKind::Object(entries) => {
            for entry in entries {
                match entry {
                    ObjectEntry::Property(property) => {
                        rename_expression_mut(&mut property.value, mapping)?
                    }
                    ObjectEntry::Spread(value) => rename_expression_mut(value, mapping)?,
                    ObjectEntry::Accessor { get, set, .. } => {
                        if let Some(value) = get {
                            rename_expression_mut(value, mapping)?;
                        }
                        if let Some(value) = set {
                            rename_expression_mut(value, mapping)?;
                        }
                    }
                }
            }
        }
        ExpressionKind::Array(elements) => {
            for element in elements {
                match element {
                    ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                        rename_expression_mut(value, mapping)?
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
            rename_expression_mut(test, mapping)?;
            rename_expression_mut(consequent, mapping)?;
            rename_expression_mut(alternate, mapping)?;
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            rename_expression_mut(argument, mapping)?
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            rename_expression_mut(left, mapping)?;
            rename_expression_mut(right, mapping)?;
        }
        ExpressionKind::Assignment { target, value, .. } => {
            rename_target_mut(target, mapping)?;
            rename_expression_mut(value, mapping)?;
        }
        ExpressionKind::Update { target, .. } => rename_target_mut(target, mapping)?,
        ExpressionKind::Call { callee, arguments } | ExpressionKind::New { callee, arguments } => {
            rename_expression_mut(callee, mapping)?;
            for value in arguments {
                rename_expression_mut(value, mapping)?;
            }
        }
        ExpressionKind::Function(_)
        | ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This => {}
    }
    Ok(())
}

fn rename_target_mut(
    target: &mut AssignmentTarget,
    mapping: &HashMap<String, String>,
) -> Result<()> {
    match target {
        AssignmentTarget::Identifier(name) => {
            if let Some(value) = mapping.get(name) {
                *name = value.clone();
            }
        }
        AssignmentTarget::Member { object, property } => {
            rename_expression_mut(object, mapping)?;
            if let MemberProperty::Computed(value) = property {
                rename_expression_mut(value, mapping)?;
            }
        }
    }
    Ok(())
}

fn validate_erased(statements: &[Statement]) -> Result<()> {
    fn expression(value: &Expression) -> Result<()> {
        if yield_marker(value).is_some() {
            bail!("yield survived generator normalization")
        }
        match &value.kind {
            ExpressionKind::Member { object, property } => {
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
            ExpressionKind::Assignment { value, .. } => expression(value)?,
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                expression(callee)?;
                for value in arguments {
                    expression(value)?;
                }
            }
            ExpressionKind::Function(function) => {
                for statement in &function.body {
                    statement_check(statement)?;
                }
            }
            ExpressionKind::Update { .. }
            | ExpressionKind::String(_)
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
            StatementKind::FunctionDeclaration(function) if function.generator => {
                bail!("generator declaration survived normalization")
            }
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

fn require_runtime(value: StaticValue, context: &str) -> Result<Expression> {
    match value {
        StaticValue::Runtime(value) => Ok(value),
        StaticValue::IterResult(_) => bail!(
            "{context} would materialize IteratorResult identity; access .value/.done or bind it statically"
        ),
    }
}

fn materialize(value: StaticValue) -> Result<Expression> {
    match value {
        StaticValue::Runtime(value) => Ok(value),
        StaticValue::IterResult(result) => Ok(Expression {
            kind: ExpressionKind::Object(vec![
                ObjectEntry::Property(ObjectProperty {
                    key: MemberProperty::Static("value".to_owned()),
                    value: result.value,
                }),
                ObjectEntry::Property(ObjectProperty {
                    key: MemberProperty::Static("done".to_owned()),
                    value: Expression {
                        kind: ExpressionKind::Bool(result.done),
                        span: result.span,
                    },
                }),
            ]),
            span: result.span,
        }),
    }
}

fn runtime(value: Expression) -> Lowered {
    Lowered {
        prefix: Vec::new(),
        value: StaticValue::Runtime(value),
    }
}

fn undefined_expression(span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Global("undefined".to_owned()),
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

fn single(mut body: Vec<Statement>, span: Span) -> Statement {
    if body.len() == 1 {
        body.pop().unwrap()
    } else {
        Statement {
            kind: StatementKind::Block(body),
            span,
        }
    }
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
