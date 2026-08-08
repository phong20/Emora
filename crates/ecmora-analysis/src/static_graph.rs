use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, CatchClause, Expression,
    ExpressionKind, ForInit, Function, MemberProperty, ObjectEntry, Program, Span, Statement,
    StatementKind, SwitchCase, UnaryOperator, UpdateOperator, VariableDeclarator, VariableKind,
};
use std::collections::{HashMap, HashSet};

type ObjectId = u32;
type ClosureId = u32;

#[derive(Debug, Clone)]
enum StaticBinding {
    Object(ObjectId),
    Closure(StaticClosure),
}

#[derive(Debug, Clone, Default)]
struct Scope {
    statics: HashMap<String, StaticBinding>,
    shadows: HashSet<String>,
}

#[derive(Debug, Clone)]
struct StaticClosure {
    id: ClosureId,
    function: Function,
    receiver: Option<ObjectId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Prototype {
    BuiltinObject,
    Null,
    Object(ObjectId),
}

#[derive(Debug, Clone)]
enum StaticProperty {
    Data {
        value_name: String,
        present: bool,
    },
    Object(ObjectId),
    Closure(StaticClosure),
    Accessor {
        getter: Option<StaticClosure>,
        setter: Option<StaticClosure>,
    },
}

#[derive(Debug, Clone)]
struct StaticObject {
    prototype: Prototype,
    properties: HashMap<String, StaticProperty>,
    order: Vec<String>,
}

#[derive(Debug, Clone)]
enum StaticValue {
    Runtime(Expression),
    Object(ObjectId),
    Closure(StaticClosure),
}

#[derive(Debug, Clone)]
struct Lowered {
    prefix: Vec<Statement>,
    value: StaticValue,
}

impl Lowered {
    fn runtime(expression: Expression) -> Self {
        Self {
            prefix: Vec::new(),
            value: StaticValue::Runtime(expression),
        }
    }
}

pub(super) fn lower(program: &Program) -> Result<Program> {
    let exported = program
        .exports
        .iter()
        .map(|binding| binding.local.clone())
        .collect::<HashSet<_>>();
    let graph_object_names = collect_prototype_object_names(&program.statements);
    let forced_functions = collect_exception_inline_functions(&program.statements);
    let mut lowerer = GraphLowerer {
        exported,
        graph_object_names,
        scopes: vec![Scope::default()],
        objects: HashMap::new(),
        next_object: 0,
        next_closure: 0,
        next_synthetic: 0,
        this_stack: Vec::new(),
        active_closures: HashSet::new(),
        forced_functions,
        control_depth: 0,
        function_depth: 0,
    };
    let statements = lowerer.lower_statements(&program.statements)?;
    validate_no_runtime_graph(&statements)?;

    let mut output = program.clone();
    output.statements = statements;
    Ok(output)
}

struct GraphLowerer {
    exported: HashSet<String>,
    graph_object_names: HashSet<String>,
    scopes: Vec<Scope>,
    objects: HashMap<ObjectId, StaticObject>,
    next_object: ObjectId,
    next_closure: ClosureId,
    next_synthetic: u32,
    this_stack: Vec<Option<ObjectId>>,
    active_closures: HashSet<ClosureId>,
    forced_functions: HashSet<String>,
    control_depth: usize,
    function_depth: usize,
}

impl GraphLowerer {
    fn fresh_name(&mut self, hint: &str) -> String {
        let id = self.next_synthetic;
        self.next_synthetic += 1;
        let hint = hint
            .chars()
            .map(|character| {
                if character.is_ascii_alphanumeric() || character == '_' {
                    character
                } else {
                    '_'
                }
            })
            .collect::<String>();
        format!("@sg_{hint}_{id}")
    }

    fn new_closure(&mut self, function: Function, receiver: Option<ObjectId>) -> StaticClosure {
        let id = self.next_closure;
        self.next_closure += 1;
        StaticClosure {
            id,
            function,
            receiver,
        }
    }

    fn new_object(&mut self, prototype: Prototype) -> ObjectId {
        let id = self.next_object;
        self.next_object += 1;
        self.objects.insert(
            id,
            StaticObject {
                prototype,
                properties: HashMap::new(),
                order: Vec::new(),
            },
        );
        id
    }

    fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn lookup_static(&self, name: &str) -> Option<StaticBinding> {
        for scope in self.scopes.iter().rev() {
            if scope.shadows.contains(name) {
                return None;
            }
            if let Some(value) = scope.statics.get(name) {
                return Some(value.clone());
            }
        }
        None
    }

    fn bind_static(&mut self, name: String, value: StaticBinding) -> Result<()> {
        if self.exported.contains(&name) {
            bail!(
                "static object/closure `{name}` is exported; native closed-world graph cannot erase its runtime identity"
            )
        }
        let scope = self.scopes.last_mut().expect("static graph scope");
        scope.shadows.remove(&name);
        scope.statics.insert(name, value);
        Ok(())
    }

    fn shadow_runtime(&mut self, name: String) {
        let scope = self.scopes.last_mut().expect("static graph scope");
        scope.statics.remove(&name);
        scope.shadows.insert(name);
    }

    fn replace_static(&mut self, name: &str, value: StaticBinding) -> Result<()> {
        for scope in self.scopes.iter_mut().rev() {
            if scope.shadows.contains(name) {
                bail!("cannot assign static value to runtime binding `{name}`")
            }
            if scope.statics.contains_key(name) {
                scope.statics.insert(name.to_owned(), value);
                return Ok(());
            }
        }
        bail!("static binding `{name}` does not exist")
    }

    fn function_is_static_only(&self, name: &str, function: &Function) -> bool {
        self.function_depth > 0
            || self.forced_functions.contains(name)
            || name.starts_with("@gen_factory_")
            || name.starts_with("@gen_resume_")
            || function_needs_static_inline(function)
    }

    fn predeclare_static_functions(&mut self, statements: &[Statement]) -> Result<()> {
        for statement in statements {
            let StatementKind::FunctionDeclaration(function) = &statement.kind else {
                continue;
            };
            let Some(name) = &function.name else {
                continue;
            };
            if self.function_is_static_only(name, function) {
                let closure = self.new_closure(function.clone(), None);
                self.bind_static(name.clone(), StaticBinding::Closure(closure))?;
            }
        }
        Ok(())
    }

    fn lower_statements(&mut self, statements: &[Statement]) -> Result<Vec<Statement>> {
        self.predeclare_static_functions(statements)?;
        let mut output = Vec::new();
        for statement in statements {
            output.extend(self.lower_statement(statement)?);
        }
        Ok(output)
    }

    fn lower_statement(&mut self, statement: &Statement) -> Result<Vec<Statement>> {
        let span = statement.span;
        Ok(match &statement.kind {
            StatementKind::Empty | StatementKind::Debugger => vec![statement.clone()],
            StatementKind::Expression(expression) => {
                let lowered = self.lower_expression(expression)?;
                let mut output = lowered.prefix;
                if let StaticValue::Runtime(value) = lowered.value {
                    output.push(Statement {
                        kind: StatementKind::Expression(value),
                        span,
                    });
                }
                output
            }
            StatementKind::VariableDeclaration { kind, declarations } => {
                self.lower_declarations(*kind, declarations, span)?
            }
            StatementKind::Block(body) => {
                self.push_scope();
                let body = self.lower_statements(body)?;
                self.pop_scope();
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
                let mut output = test.prefix;
                let test = require_runtime(test.value, "if condition")?;
                self.control_depth += 1;
                self.push_scope();
                let consequent = self.lower_as_single(consequent)?;
                self.pop_scope();
                let alternate = if let Some(alternate) = alternate {
                    self.push_scope();
                    let alternate = self.lower_as_single(alternate)?;
                    self.pop_scope();
                    Some(Box::new(alternate))
                } else {
                    None
                };
                self.control_depth -= 1;
                output.push(Statement {
                    kind: StatementKind::If {
                        test,
                        consequent: Box::new(consequent),
                        alternate,
                    },
                    span,
                });
                output
            }
            StatementKind::While { test, body } => {
                let test = self.lower_expression(test)?;
                if !test.prefix.is_empty() {
                    bail!(
                        "static graph operations in while conditions need loop-state normalization"
                    )
                }
                let test = require_runtime(test.value, "while condition")?;
                self.control_depth += 1;
                self.push_scope();
                let body = self.lower_as_single(body)?;
                self.pop_scope();
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
                self.control_depth += 1;
                self.push_scope();
                let body = self.lower_as_single(body)?;
                self.pop_scope();
                let test = self.lower_expression(test)?;
                self.control_depth -= 1;
                if !test.prefix.is_empty() {
                    bail!(
                        "static graph operations in do-while conditions need loop-state normalization"
                    )
                }
                vec![Statement {
                    kind: StatementKind::DoWhile {
                        body: Box::new(body),
                        test: require_runtime(test.value, "do-while condition")?,
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
                self.push_scope();
                let init = init
                    .as_ref()
                    .map(|init| self.lower_for_init(init))
                    .transpose()?;
                let test = test
                    .as_ref()
                    .map(|test| self.lower_expression(test))
                    .transpose()?;
                let update = update
                    .as_ref()
                    .map(|update| self.lower_expression(update))
                    .transpose()?;
                if test.as_ref().is_some_and(|value| !value.prefix.is_empty())
                    || update
                        .as_ref()
                        .is_some_and(|value| !value.prefix.is_empty())
                {
                    bail!(
                        "static graph operations in for test/update need loop-state normalization"
                    )
                }
                self.control_depth += 1;
                let body = self.lower_as_single(body)?;
                self.control_depth -= 1;
                self.pop_scope();
                vec![Statement {
                    kind: StatementKind::For {
                        init,
                        test: test
                            .map(|value| require_runtime(value.value, "for condition"))
                            .transpose()?,
                        update: update
                            .map(|value| require_runtime(value.value, "for update"))
                            .transpose()?,
                        body: Box::new(body),
                    },
                    span,
                }]
            }
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => {
                let right = self.lower_expression(right)?;
                if !right.prefix.is_empty() {
                    bail!("static graph operations in for-in source need iterator normalization")
                }
                self.push_scope();
                self.shadow_runtime(name.clone());
                self.control_depth += 1;
                let body = self.lower_as_single(body)?;
                self.control_depth -= 1;
                self.pop_scope();
                vec![Statement {
                    kind: StatementKind::ForIn {
                        name: name.clone(),
                        kind: *kind,
                        right: require_runtime(right.value, "for-in source")?,
                        body: Box::new(body),
                    },
                    span,
                }]
            }
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => {
                let right = self.lower_expression(right)?;
                if !right.prefix.is_empty() {
                    bail!("static graph operations in for-of source need iterator normalization")
                }
                self.push_scope();
                self.shadow_runtime(name.clone());
                self.control_depth += 1;
                let body = self.lower_as_single(body)?;
                self.control_depth -= 1;
                self.pop_scope();
                vec![Statement {
                    kind: StatementKind::ForOf {
                        name: name.clone(),
                        kind: *kind,
                        right: require_runtime(right.value, "for-of source")?,
                        body: Box::new(body),
                    },
                    span,
                }]
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                let discriminant = self.lower_expression(discriminant)?;
                let mut output = discriminant.prefix;
                let discriminant = require_runtime(discriminant.value, "switch discriminant")?;
                self.control_depth += 1;
                self.push_scope();
                let mut lowered_cases = Vec::with_capacity(cases.len());
                for case in cases {
                    let test = case
                        .test
                        .as_ref()
                        .map(|test| self.lower_expression(test))
                        .transpose()?;
                    if test.as_ref().is_some_and(|value| !value.prefix.is_empty()) {
                        bail!("static graph operations in switch case tests are not hoistable")
                    }
                    lowered_cases.push(SwitchCase {
                        test: test
                            .map(|value| require_runtime(value.value, "switch case"))
                            .transpose()?,
                        consequent: self.lower_statements(&case.consequent)?,
                        span: case.span,
                    });
                }
                self.pop_scope();
                self.control_depth -= 1;
                output.push(Statement {
                    kind: StatementKind::Switch {
                        discriminant,
                        cases: lowered_cases,
                    },
                    span,
                });
                output
            }
            StatementKind::Labeled { label, body } => vec![Statement {
                kind: StatementKind::Labeled {
                    label: label.clone(),
                    body: Box::new(self.lower_as_single(body)?),
                },
                span,
            }],
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                self.control_depth += 1;
                self.push_scope();
                let block = self.lower_as_single(block)?;
                self.pop_scope();
                let handler = if let Some(handler) = handler {
                    self.push_scope();
                    if let Some(parameter) = &handler.parameter {
                        self.shadow_runtime(parameter.clone());
                    }
                    let body = self.lower_as_single(&handler.body)?;
                    self.pop_scope();
                    Some(CatchClause {
                        parameter: handler.parameter.clone(),
                        body: Box::new(body),
                        span: handler.span,
                    })
                } else {
                    None
                };
                let finalizer = if let Some(finalizer) = finalizer {
                    self.push_scope();
                    let finalizer = self.lower_as_single(finalizer)?;
                    self.pop_scope();
                    Some(Box::new(finalizer))
                } else {
                    None
                };
                self.control_depth -= 1;
                vec![Statement {
                    kind: StatementKind::Try {
                        block: Box::new(block),
                        handler,
                        finalizer,
                    },
                    span,
                }]
            }
            StatementKind::FunctionDeclaration(function) => {
                if let Some(name) = &function.name {
                    if matches!(self.lookup_static(name), Some(StaticBinding::Closure(_)))
                        && self.function_is_static_only(name, function)
                    {
                        Vec::new()
                    } else {
                        let function = self.lower_runtime_function(function)?;
                        self.shadow_runtime(name.clone());
                        vec![Statement {
                            kind: StatementKind::FunctionDeclaration(function),
                            span,
                        }]
                    }
                } else {
                    vec![Statement {
                        kind: StatementKind::FunctionDeclaration(
                            self.lower_runtime_function(function)?,
                        ),
                        span,
                    }]
                }
            }
            StatementKind::Return(value) => {
                let Some(value) = value else {
                    return Ok(vec![statement.clone()]);
                };
                let value = self.lower_expression(value)?;
                let mut output = value.prefix;
                output.push(Statement {
                    kind: StatementKind::Return(Some(require_runtime(
                        value.value,
                        "runtime function return",
                    )?)),
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
            StatementKind::Break(_) | StatementKind::Continue(_) => vec![statement.clone()],
        })
    }

    fn lower_runtime_function(&mut self, function: &Function) -> Result<Function> {
        let saved_scopes = std::mem::replace(&mut self.scopes, vec![Scope::default()]);
        self.function_depth += 1;
        if let Some(name) = &function.name {
            self.shadow_runtime(name.clone());
        }
        for parameter in &function.parameters {
            self.shadow_runtime(
                parameter
                    .strip_prefix("@rest:")
                    .unwrap_or(parameter)
                    .to_owned(),
            );
        }
        let body = self.lower_statements(&function.body)?;
        self.function_depth -= 1;
        self.scopes = saved_scopes;
        Ok(Function {
            name: function.name.clone(),
            parameters: function.parameters.clone(),
            body,
            r#async: function.r#async,
            generator: function.generator,
            arrow: function.arrow,
            lowering_error: function.lowering_error.clone(),
        })
    }

    fn lower_as_single(&mut self, statement: &Statement) -> Result<Statement> {
        let mut output = self.lower_statement(statement)?;
        if output.len() == 1 {
            return Ok(output.remove(0));
        }
        Ok(Statement {
            kind: StatementKind::Block(output),
            span: statement.span,
        })
    }

    fn lower_for_init(&mut self, init: &ForInit) -> Result<ForInit> {
        match init {
            ForInit::Expression(expression) => {
                let lowered = self.lower_expression(expression)?;
                if !lowered.prefix.is_empty() {
                    bail!("static graph operations in for initializer need statement normalization")
                }
                Ok(ForInit::Expression(require_runtime(
                    lowered.value,
                    "for initializer",
                )?))
            }
            ForInit::VariableDeclaration { kind, declarations } => {
                let mut output = Vec::with_capacity(declarations.len());
                for declaration in declarations {
                    let init = declaration
                        .init
                        .as_ref()
                        .map(|value| self.lower_expression(value))
                        .transpose()?;
                    let init = if let Some(init) = init {
                        if !init.prefix.is_empty() {
                            bail!(
                                "static graph operations in for declaration need statement normalization"
                            )
                        }
                        Some(require_runtime(init.value, "for declaration")?)
                    } else {
                        None
                    };
                    self.shadow_runtime(declaration.name.clone());
                    output.push(VariableDeclarator {
                        name: declaration.name.clone(),
                        init,
                        span: declaration.span,
                    });
                }
                Ok(ForInit::VariableDeclaration {
                    kind: *kind,
                    declarations: output,
                })
            }
        }
    }

    fn lower_declarations(
        &mut self,
        kind: VariableKind,
        declarations: &[VariableDeclarator],
        statement_span: Span,
    ) -> Result<Vec<Statement>> {
        let mut output = Vec::new();
        for declaration in declarations {
            let Some(initializer) = &declaration.init else {
                self.shadow_runtime(declaration.name.clone());
                output.push(variable_statement(
                    kind,
                    declaration.name.clone(),
                    None,
                    declaration.span,
                ));
                continue;
            };
            let lowered = if self.graph_object_names.contains(&declaration.name) {
                match &initializer.kind {
                    ExpressionKind::Object(entries) => {
                        self.materialize_object(entries, initializer.span)?
                    }
                    _ => self.lower_expression(initializer)?,
                }
            } else {
                self.lower_expression(initializer)?
            };
            output.extend(lowered.prefix);
            match lowered.value {
                StaticValue::Object(id) => {
                    self.bind_static(declaration.name.clone(), StaticBinding::Object(id))?;
                }
                StaticValue::Closure(closure) => {
                    self.bind_static(declaration.name.clone(), StaticBinding::Closure(closure))?;
                }
                StaticValue::Runtime(value) => {
                    self.shadow_runtime(declaration.name.clone());
                    output.push(variable_statement(
                        kind,
                        declaration.name.clone(),
                        Some(value),
                        declaration.span,
                    ));
                }
            }
        }
        if output.is_empty() {
            let _ = statement_span;
        }
        Ok(output)
    }

    fn lower_expression(&mut self, expression: &Expression) -> Result<Lowered> {
        let span = expression.span;
        match &expression.kind {
            ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null => Ok(Lowered::runtime(expression.clone())),
            ExpressionKind::This => match self.this_stack.last().copied().flatten() {
                Some(object) => Ok(Lowered {
                    prefix: Vec::new(),
                    value: StaticValue::Object(object),
                }),
                None => Ok(Lowered::runtime(expression.clone())),
            },
            ExpressionKind::Global(name) => match self.lookup_static(name) {
                Some(StaticBinding::Object(id)) => Ok(Lowered {
                    prefix: Vec::new(),
                    value: StaticValue::Object(id),
                }),
                Some(StaticBinding::Closure(closure)) => Ok(Lowered {
                    prefix: Vec::new(),
                    value: StaticValue::Closure(closure),
                }),
                None => Ok(Lowered::runtime(expression.clone())),
            },
            ExpressionKind::Member { object, property } => {
                let object = self.lower_expression(object)?;
                match object.value {
                    StaticValue::Object(id) => {
                        let mut result = self.read_property(id, property, span)?;
                        let mut prefix = object.prefix;
                        prefix.append(&mut result.prefix);
                        result.prefix = prefix;
                        Ok(result)
                    }
                    StaticValue::Runtime(object_value) => {
                        let property = self.lower_member_property(property)?;
                        let mut prefix = object.prefix;

                        // ANF invariant: a non-atomic runtime Member receiver is materialized exactly once.
                        //
                        // Calls, object/array literals, conditionals and other
                        // compound receivers must not stay nested below a
                        // property read. Besides preserving exactly-once
                        // evaluation, this exposes transient object literals as
                        // declarations to aggregate_scalar, so {value, done}
                        // results can become scalar SSA instead of a recursive
                        // aggregate expression.
                        let object_value = if runtime_member_receiver_needs_anf(&object_value) {
                            let temporary = self.fresh_name("member_base");
                            prefix.push(variable_statement(
                                VariableKind::Let,
                                temporary.clone(),
                                Some(object_value),
                                span,
                            ));
                            global_expression(temporary, span)
                        } else {
                            object_value
                        };

                        Ok(Lowered {
                            prefix,
                            value: StaticValue::Runtime(Expression {
                                kind: ExpressionKind::Member {
                                    object: Box::new(object_value),
                                    property,
                                },
                                span,
                            }),
                        })
                    }
                    StaticValue::Closure(_) => {
                        bail!(
                            "property access on erased static closure would require runtime identity"
                        )
                    }
                }
            }
            ExpressionKind::Object(entries) => {
                if object_entries_need_graph(entries) {
                    self.materialize_object(entries, span)
                } else {
                    self.lower_runtime_object(entries, span)
                }
            }
            ExpressionKind::Array(elements) => {
                let mut prefix = Vec::new();
                let mut output = Vec::with_capacity(elements.len());
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) => {
                            let mut lowered = self.lower_expression(value)?;
                            prefix.append(&mut lowered.prefix);
                            output.push(ArrayElement::Expression(require_runtime(
                                lowered.value,
                                "array element",
                            )?));
                        }
                        ArrayElement::Spread(value) => {
                            let mut lowered = self.lower_expression(value)?;
                            prefix.append(&mut lowered.prefix);
                            output.push(ArrayElement::Spread(require_runtime(
                                lowered.value,
                                "array spread",
                            )?));
                        }
                        ArrayElement::Hole => output.push(ArrayElement::Hole),
                    }
                }
                Ok(Lowered {
                    prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Array(output),
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
                    || !matches!(&consequent.value, StaticValue::Runtime(_))
                    || !matches!(&alternate.value, StaticValue::Runtime(_))
                {
                    bail!(
                        "static graph values inside conditional expressions need CFG value normalization"
                    )
                }
                let consequent = require_runtime(consequent.value, "conditional consequent")?;
                let alternate = require_runtime(alternate.value, "conditional alternate")?;
                Ok(Lowered {
                    prefix: test.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Conditional {
                            test: Box::new(require_runtime(test.value, "conditional condition")?),
                            consequent: Box::new(consequent),
                            alternate: Box::new(alternate),
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Unary { operator, argument } => {
                if *operator == UnaryOperator::Delete {
                    if let ExpressionKind::Member { object, property } = &argument.kind {
                        let object = self.lower_expression(object)?;
                        if let StaticValue::Object(id) = object.value {
                            let key = static_property_key(property)?;
                            self.delete_property(id, &key)?;
                            return Ok(Lowered {
                                prefix: object.prefix,
                                value: StaticValue::Runtime(bool_expression(true, span)),
                            });
                        }
                    }
                }
                let argument = self.lower_expression(argument)?;
                match argument.value {
                    StaticValue::Object(_) => match operator {
                        UnaryOperator::Typeof => Ok(Lowered {
                            prefix: argument.prefix,
                            value: StaticValue::Runtime(string_expression("object", span)),
                        }),
                        UnaryOperator::Not => Ok(Lowered {
                            prefix: argument.prefix,
                            value: StaticValue::Runtime(bool_expression(false, span)),
                        }),
                        UnaryOperator::Void => Ok(Lowered {
                            prefix: argument.prefix,
                            value: StaticValue::Runtime(undefined_expression(span)),
                        }),
                        _ => bail!("object coercion escaped static graph analysis"),
                    },
                    StaticValue::Closure(_) => match operator {
                        UnaryOperator::Typeof => Ok(Lowered {
                            prefix: argument.prefix,
                            value: StaticValue::Runtime(string_expression("function", span)),
                        }),
                        UnaryOperator::Not => Ok(Lowered {
                            prefix: argument.prefix,
                            value: StaticValue::Runtime(bool_expression(false, span)),
                        }),
                        UnaryOperator::Void => Ok(Lowered {
                            prefix: argument.prefix,
                            value: StaticValue::Runtime(undefined_expression(span)),
                        }),
                        _ => bail!("closure coercion escaped static graph analysis"),
                    },
                    StaticValue::Runtime(argument_value) => Ok(Lowered {
                        prefix: argument.prefix,
                        value: StaticValue::Runtime(Expression {
                            kind: ExpressionKind::Unary {
                                operator: *operator,
                                argument: Box::new(argument_value),
                            },
                            span,
                        }),
                    }),
                }
            }
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => self.lower_binary(left, *operator, right, span),
            ExpressionKind::Logical {
                left,
                operator,
                right,
            } => {
                let left = self.lower_expression(left)?;
                let right = self.lower_expression(right)?;
                if !right.prefix.is_empty()
                    || !matches!(&left.value, StaticValue::Runtime(_))
                    || !matches!(&right.value, StaticValue::Runtime(_))
                {
                    bail!(
                        "static graph values inside logical expressions need short-circuit CFG normalization"
                    )
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
            } => self.lower_assignment(target, *operator, value, span),
            ExpressionKind::Update {
                target,
                operator,
                prefix,
            } => self.lower_update(target, *operator, *prefix, span),
            ExpressionKind::Call { callee, arguments } => self.lower_call(callee, arguments, span),
            ExpressionKind::New { callee, arguments } => {
                let callee = self.lower_expression(callee)?;
                let mut prefix = callee.prefix;
                let callee = require_runtime(callee.value, "constructor callee")?;
                let mut output = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    let mut lowered = self.lower_expression(argument)?;
                    prefix.append(&mut lowered.prefix);
                    output.push(require_runtime(lowered.value, "constructor argument")?);
                }
                Ok(Lowered {
                    prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::New {
                            callee: Box::new(callee),
                            arguments: output,
                        },
                        span,
                    }),
                })
            }
            ExpressionKind::Function(function) => Ok(Lowered {
                prefix: Vec::new(),
                value: StaticValue::Closure(self.new_closure(function.clone(), None)),
            }),
            ExpressionKind::Await(value) => {
                let value = self.lower_expression(value)?;
                Ok(Lowered {
                    prefix: value.prefix,
                    value: StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Await(Box::new(require_runtime(
                            value.value,
                            "await value",
                        )?)),
                        span,
                    }),
                })
            }
        }
    }

    fn lower_member_property(&mut self, property: &MemberProperty) -> Result<MemberProperty> {
        match property {
            MemberProperty::Static(key) => Ok(MemberProperty::Static(key.clone())),
            MemberProperty::Computed(value) => {
                let value = self.lower_expression(value)?;
                if !value.prefix.is_empty() {
                    bail!("computed property key with static graph side effects is not hoistable")
                }
                Ok(MemberProperty::Computed(Box::new(require_runtime(
                    value.value,
                    "computed property key",
                )?)))
            }
        }
    }

    fn lower_binary(
        &mut self,
        left: &Expression,
        operator: BinaryOperator,
        right: &Expression,
        span: Span,
    ) -> Result<Lowered> {
        let mut left = self.lower_expression(left)?;
        let mut right = self.lower_expression(right)?;
        let mut prefix = Vec::new();
        prefix.append(&mut left.prefix);
        prefix.append(&mut right.prefix);

        if matches!(
            operator,
            BinaryOperator::Equal
                | BinaryOperator::NotEqual
                | BinaryOperator::StrictEqual
                | BinaryOperator::StrictNotEqual
        ) {
            let equal = match (&left.value, &right.value) {
                (StaticValue::Object(left), StaticValue::Object(right)) => Some(left == right),
                (StaticValue::Closure(left), StaticValue::Closure(right)) => {
                    Some(left.id == right.id)
                }
                (StaticValue::Object(_), StaticValue::Runtime(value))
                | (StaticValue::Closure(_), StaticValue::Runtime(value))
                | (StaticValue::Runtime(value), StaticValue::Object(_))
                | (StaticValue::Runtime(value), StaticValue::Closure(_))
                    if is_nullish_runtime(value) =>
                {
                    Some(false)
                }
                _ => None,
            };
            if let Some(equal) = equal {
                let result = if matches!(
                    operator,
                    BinaryOperator::NotEqual | BinaryOperator::StrictNotEqual
                ) {
                    !equal
                } else {
                    equal
                };
                return Ok(Lowered {
                    prefix,
                    value: StaticValue::Runtime(bool_expression(result, span)),
                });
            }
        }

        if operator == BinaryOperator::In {
            if let StaticValue::Object(object) = right.value.clone() {
                let key = runtime_literal_key(&left.value)?;
                let present = self.has_property(object, &key)?;
                return Ok(Lowered {
                    prefix,
                    value: StaticValue::Runtime(bool_expression(present, span)),
                });
            }
        }

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

    fn lower_assignment(
        &mut self,
        target: &AssignmentTarget,
        operator: AssignmentOperator,
        value: &Expression,
        span: Span,
    ) -> Result<Lowered> {
        match target {
            AssignmentTarget::Identifier(name) => {
                if self.lookup_static(name).is_some() {
                    if operator != AssignmentOperator::Assign {
                        bail!("compound assignment to erased static binding `{name}`")
                    }
                    let value = self.lower_expression(value)?;
                    let binding = match value.value.clone() {
                        StaticValue::Object(id) => StaticBinding::Object(id),
                        StaticValue::Closure(closure) => StaticBinding::Closure(closure),
                        StaticValue::Runtime(_) => {
                            bail!("cannot reify erased static binding `{name}` as runtime value")
                        }
                    };
                    self.replace_static(name, binding)?;
                    return Ok(value);
                }
                let mut value = self.lower_expression(value)?;
                let runtime = require_runtime(value.value, "identifier assignment")?;
                value.value = StaticValue::Runtime(Expression {
                    kind: ExpressionKind::Assignment {
                        target: AssignmentTarget::Identifier(name.clone()),
                        operator,
                        value: Box::new(runtime),
                    },
                    span,
                });
                Ok(value)
            }
            AssignmentTarget::Member { object, property } => {
                let mut object = self.lower_expression(object)?;
                if let StaticValue::Object(id) = object.value.clone() {
                    let mut assigned = self.assign_property(id, property, operator, value, span)?;
                    object.prefix.append(&mut assigned.prefix);
                    assigned.prefix = object.prefix;
                    Ok(assigned)
                } else {
                    let object_value = require_runtime(object.value, "member assignment object")?;
                    let property = self.lower_member_property(property)?;
                    let mut value = self.lower_expression(value)?;
                    object.prefix.append(&mut value.prefix);
                    Ok(Lowered {
                        prefix: object.prefix,
                        value: StaticValue::Runtime(Expression {
                            kind: ExpressionKind::Assignment {
                                target: AssignmentTarget::Member {
                                    object: Box::new(object_value),
                                    property,
                                },
                                operator,
                                value: Box::new(require_runtime(
                                    value.value,
                                    "member assignment value",
                                )?),
                            },
                            span,
                        }),
                    })
                }
            }
        }
    }

    fn lower_update(
        &mut self,
        target: &AssignmentTarget,
        operator: UpdateOperator,
        prefix_result: bool,
        span: Span,
    ) -> Result<Lowered> {
        if let AssignmentTarget::Member { object, property } = target {
            let object = self.lower_expression(object)?;
            if let StaticValue::Object(id) = object.value {
                let old = self.read_property(id, property, span)?;
                let old_value = require_runtime(old.value, "static property update")?;
                let temporary = self.fresh_name("update");
                let arithmetic = Expression {
                    kind: ExpressionKind::Binary {
                        left: Box::new(old_value.clone()),
                        operator: if operator == UpdateOperator::Increment {
                            BinaryOperator::Add
                        } else {
                            BinaryOperator::Subtract
                        },
                        right: Box::new(number_expression(1.0, span)),
                    },
                    span,
                };
                let mut write = self.write_property_value(
                    id,
                    &static_property_key(property)?,
                    StaticValue::Runtime(global_expression(temporary.clone(), span)),
                    span,
                )?;
                let mut output = object.prefix;
                output.extend(old.prefix);
                output.push(variable_statement(
                    VariableKind::Let,
                    temporary.clone(),
                    Some(arithmetic),
                    span,
                ));
                output.append(&mut write);
                return Ok(Lowered {
                    prefix: output,
                    value: StaticValue::Runtime(if prefix_result {
                        global_expression(temporary, span)
                    } else {
                        old_value
                    }),
                });
            }
        }

        let target = self.lower_assignment_target_runtime(target)?;
        Ok(Lowered {
            prefix: Vec::new(),
            value: StaticValue::Runtime(Expression {
                kind: ExpressionKind::Update {
                    target,
                    operator,
                    prefix: prefix_result,
                },
                span,
            }),
        })
    }

    fn lower_assignment_target_runtime(
        &mut self,
        target: &AssignmentTarget,
    ) -> Result<AssignmentTarget> {
        match target {
            AssignmentTarget::Identifier(name) => Ok(AssignmentTarget::Identifier(name.clone())),
            AssignmentTarget::Member { object, property } => {
                let object = self.lower_expression(object)?;
                if !object.prefix.is_empty() {
                    bail!("runtime assignment target object has non-hoistable static graph effects")
                }
                Ok(AssignmentTarget::Member {
                    object: Box::new(require_runtime(object.value, "runtime assignment target")?),
                    property: self.lower_member_property(property)?,
                })
            }
        }
    }

    fn lower_call(
        &mut self,
        callee: &Expression,
        arguments: &[Expression],
        span: Span,
    ) -> Result<Lowered> {
        if let Some(result) = self.lower_object_builtin_call(callee, arguments, span)? {
            return Ok(result);
        }

        if let ExpressionKind::Member { object, property } = &callee.kind {
            let mut object = self.lower_expression(object)?;
            if let StaticValue::Object(id) = object.value {
                let mut property_value = self.read_property(id, property, span)?;
                object.prefix.append(&mut property_value.prefix);
                let closure = match property_value.value {
                    StaticValue::Closure(mut closure) => {
                        closure.receiver = Some(id);
                        closure
                    }
                    _ => bail!(
                        "calling static property `{}` requires a statically known method",
                        static_property_key(property)?
                    ),
                };
                let mut call = self.inline_closure(&closure, arguments, Some(id), span)?;
                object.prefix.append(&mut call.prefix);
                call.prefix = object.prefix;
                return Ok(call);
            }
        }

        let mut callee = self.lower_expression(callee)?;
        if let StaticValue::Closure(closure) = callee.value.clone() {
            let mut call = self.inline_closure(&closure, arguments, closure.receiver, span)?;
            callee.prefix.append(&mut call.prefix);
            call.prefix = callee.prefix;
            return Ok(call);
        }

        let callee_value = require_runtime(callee.value, "runtime callee")?;
        let mut output_arguments = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let mut lowered = self.lower_expression(argument)?;
            callee.prefix.append(&mut lowered.prefix);
            output_arguments.push(require_runtime(lowered.value, "runtime call argument")?);
        }
        Ok(Lowered {
            prefix: callee.prefix,
            value: StaticValue::Runtime(Expression {
                kind: ExpressionKind::Call {
                    callee: Box::new(callee_value),
                    arguments: output_arguments,
                },
                span,
            }),
        })
    }

    fn lower_graph_object_expression(&mut self, expression: &Expression) -> Result<Lowered> {
        match &expression.kind {
            ExpressionKind::Object(entries) => self.materialize_object(entries, expression.span),
            _ => self.lower_expression(expression),
        }
    }

    fn lower_object_builtin_call(
        &mut self,
        callee: &Expression,
        arguments: &[Expression],
        span: Span,
    ) -> Result<Option<Lowered>> {
        let ExpressionKind::Member { object, property } = &callee.kind else {
            return Ok(None);
        };
        let ExpressionKind::Global(object_name) = &object.kind else {
            return Ok(None);
        };
        let MemberProperty::Static(method) = property else {
            return Ok(None);
        };
        if object_name != "Object" || self.lookup_static(object_name).is_some() {
            return Ok(None);
        }

        match method.as_str() {
            "create" => {
                if arguments.len() != 1 {
                    bail!("Object.create requires exactly one prototype")
                }
                let prototype = self.lower_graph_object_expression(&arguments[0])?;
                let prototype_kind = match prototype.value {
                    StaticValue::Object(id) => Prototype::Object(id),
                    StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Null,
                        ..
                    }) => Prototype::Null,
                    _ => {
                        bail!("Object.create prototype is not a closed-world static object or null")
                    }
                };
                Ok(Some(Lowered {
                    prefix: prototype.prefix,
                    value: StaticValue::Object(self.new_object(prototype_kind)),
                }))
            }
            "setPrototypeOf" => {
                if arguments.len() != 2 {
                    bail!("Object.setPrototypeOf requires target and prototype")
                }
                if self.control_depth != 0 {
                    bail!(
                        "conditional prototype mutation cannot be represented as one static graph"
                    )
                }
                let mut target = self.lower_expression(&arguments[0])?;
                let mut prototype = self.lower_graph_object_expression(&arguments[1])?;
                target.prefix.append(&mut prototype.prefix);
                let target_id = match target.value {
                    StaticValue::Object(id) => id,
                    _ => bail!("Object.setPrototypeOf target must be a static object"),
                };
                let prototype = match prototype.value {
                    StaticValue::Object(id) => Prototype::Object(id),
                    StaticValue::Runtime(Expression {
                        kind: ExpressionKind::Null,
                        ..
                    }) => Prototype::Null,
                    _ => bail!("Object.setPrototypeOf prototype must be a static object or null"),
                };
                self.ensure_no_prototype_cycle(target_id, prototype)?;
                self.objects
                    .get_mut(&target_id)
                    .expect("static object")
                    .prototype = prototype;
                Ok(Some(Lowered {
                    prefix: target.prefix,
                    value: StaticValue::Object(target_id),
                }))
            }
            "getPrototypeOf" => {
                if arguments.len() != 1 {
                    bail!("Object.getPrototypeOf requires one target")
                }
                let target = self.lower_expression(&arguments[0])?;
                let id = match target.value {
                    StaticValue::Object(id) => id,
                    _ => bail!("Object.getPrototypeOf target must be a static object"),
                };
                let value = match self.objects.get(&id).expect("static object").prototype {
                    Prototype::Object(prototype) => StaticValue::Object(prototype),
                    Prototype::Null => StaticValue::Runtime(null_expression(span)),
                    Prototype::BuiltinObject => {
                        bail!(
                            "Object.getPrototypeOf on an object literal exposes builtin Object.prototype identity"
                        )
                    }
                };
                Ok(Some(Lowered {
                    prefix: target.prefix,
                    value,
                }))
            }
            _ => Ok(None),
        }
    }

    fn lower_runtime_object(&mut self, entries: &[ObjectEntry], span: Span) -> Result<Lowered> {
        let mut prefix = Vec::new();
        let mut output = Vec::with_capacity(entries.len());
        for entry in entries {
            match entry {
                ObjectEntry::Property(property) => {
                    let mut value = self.lower_expression(&property.value)?;
                    prefix.append(&mut value.prefix);
                    output.push(ObjectEntry::Property(ecmora_hir::ObjectProperty {
                        key: self.lower_member_property(&property.key)?,
                        value: require_runtime(value.value, "runtime object property")?,
                    }));
                }
                ObjectEntry::Spread(value) => {
                    let mut value = self.lower_expression(value)?;
                    prefix.append(&mut value.prefix);
                    output.push(ObjectEntry::Spread(require_runtime(
                        value.value,
                        "runtime object spread",
                    )?));
                }
                ObjectEntry::Accessor { .. } => {
                    bail!("accessor object must enter the static graph pass")
                }
            }
        }
        Ok(Lowered {
            prefix,
            value: StaticValue::Runtime(Expression {
                kind: ExpressionKind::Object(output),
                span,
            }),
        })
    }

    fn materialize_object(&mut self, entries: &[ObjectEntry], span: Span) -> Result<Lowered> {
        let id = self.new_object(Prototype::BuiltinObject);
        let mut prefix = Vec::new();
        for entry in entries {
            match entry {
                ObjectEntry::Property(property) => {
                    let key = static_property_key(&property.key)?;
                    let mut value = self.lower_expression(&property.value)?;
                    prefix.append(&mut value.prefix);
                    let mut emitted =
                        self.install_own_property(id, key, value.value, property.value.span)?;
                    prefix.append(&mut emitted);
                }
                ObjectEntry::Accessor { key, get, set } => {
                    let getter = get
                        .as_ref()
                        .map(|value| self.closure_from_accessor(value, Some(id)))
                        .transpose()?;
                    let setter = set
                        .as_ref()
                        .map(|value| self.closure_from_accessor(value, Some(id)))
                        .transpose()?;
                    self.install_accessor_property(id, key.clone(), getter, setter);
                }
                ObjectEntry::Spread(source) => {
                    let mut source = self.lower_expression(source)?;
                    prefix.append(&mut source.prefix);
                    let source_id = match source.value {
                        StaticValue::Object(id) => id,
                        _ => bail!("object spread source is not a static object"),
                    };
                    let keys = self
                        .objects
                        .get(&source_id)
                        .expect("spread source")
                        .order
                        .clone();
                    for key in keys {
                        let property = self
                            .objects
                            .get(&source_id)
                            .and_then(|object| object.properties.get(&key))
                            .cloned()
                            .expect("spread property");
                        match property {
                            StaticProperty::Data {
                                value_name,
                                present: true,
                            } => {
                                let target = self.fresh_name(&format!("spread_{key}"));
                                prefix.push(variable_statement(
                                    VariableKind::Let,
                                    target.clone(),
                                    Some(global_expression(value_name, span)),
                                    span,
                                ));
                                self.install_property(
                                    id,
                                    key,
                                    StaticProperty::Data {
                                        value_name: target,
                                        present: true,
                                    },
                                );
                            }
                            StaticProperty::Object(object) => {
                                self.install_property(id, key, StaticProperty::Object(object));
                            }
                            StaticProperty::Closure(closure) => {
                                self.install_property(id, key, StaticProperty::Closure(closure));
                            }
                            StaticProperty::Accessor { .. } => {
                                bail!(
                                    "object spread over an accessor needs an explicit static Get normalization"
                                )
                            }
                            StaticProperty::Data { present: false, .. } => {}
                        }
                    }
                }
            }
        }
        Ok(Lowered {
            prefix,
            value: StaticValue::Object(id),
        })
    }

    fn closure_from_accessor(
        &mut self,
        expression: &Expression,
        receiver: Option<ObjectId>,
    ) -> Result<StaticClosure> {
        let ExpressionKind::Function(function) = &expression.kind else {
            bail!("accessor entry is not a function")
        };
        Ok(self.new_closure(function.clone(), receiver))
    }

    fn install_own_property(
        &mut self,
        object: ObjectId,
        key: String,
        value: StaticValue,
        span: Span,
    ) -> Result<Vec<Statement>> {
        match value {
            StaticValue::Runtime(value) => {
                let name = self.fresh_name(&format!("field_{key}"));
                self.install_property(
                    object,
                    key,
                    StaticProperty::Data {
                        value_name: name.clone(),
                        present: true,
                    },
                );
                Ok(vec![variable_statement(
                    VariableKind::Let,
                    name,
                    Some(value),
                    span,
                )])
            }
            StaticValue::Object(id) => {
                self.install_property(object, key, StaticProperty::Object(id));
                Ok(Vec::new())
            }
            StaticValue::Closure(closure) => {
                self.install_property(object, key, StaticProperty::Closure(closure));
                Ok(Vec::new())
            }
        }
    }

    /// Install one accessor definition from an object literal.
    ///
    /// OXC lowers `get x(){...}` and `set x(v){...}` as two distinct
    /// ObjectEntry::Accessor values. ECMAScript object-literal evaluation,
    /// however, leaves a single accessor descriptor containing both halves.
    ///
    /// A later getter replaces only [[Get]] and preserves an existing [[Set]];
    /// a later setter replaces only [[Set]] and preserves an existing [[Get]].
    /// A transition between data/method and accessor descriptors still replaces
    /// the whole previous descriptor; `install_property` handles those cases.
    fn install_accessor_property(
        &mut self,
        object: ObjectId,
        key: String,
        getter: Option<StaticClosure>,
        setter: Option<StaticClosure>,
    ) {
        let existing = self
            .objects
            .get(&object)
            .and_then(|state| state.properties.get(&key))
            .cloned();

        let (getter, setter) = match existing {
            Some(StaticProperty::Accessor {
                getter: previous_getter,
                setter: previous_setter,
            }) => (getter.or(previous_getter), setter.or(previous_setter)),
            _ => (getter, setter),
        };

        self.install_property(object, key, StaticProperty::Accessor { getter, setter });
    }

    fn install_property(&mut self, object: ObjectId, key: String, property: StaticProperty) {
        let object = self.objects.get_mut(&object).expect("static object");
        if !object.properties.contains_key(&key) {
            object.order.push(key.clone());
        }
        object.properties.insert(key, property);
    }

    fn read_property(
        &mut self,
        receiver: ObjectId,
        property: &MemberProperty,
        span: Span,
    ) -> Result<Lowered> {
        let key = static_property_key(property)?;
        let Some((_owner, property)) = self.lookup_property(receiver, &key)? else {
            return Ok(Lowered::runtime(undefined_expression(span)));
        };
        match property {
            StaticProperty::Data {
                value_name,
                present: true,
            } => Ok(Lowered::runtime(global_expression(value_name, span))),
            StaticProperty::Data { present: false, .. } => {
                Ok(Lowered::runtime(undefined_expression(span)))
            }
            StaticProperty::Object(id) => Ok(Lowered {
                prefix: Vec::new(),
                value: StaticValue::Object(id),
            }),
            StaticProperty::Closure(mut closure) => {
                closure.receiver = Some(receiver);
                Ok(Lowered {
                    prefix: Vec::new(),
                    value: StaticValue::Closure(closure),
                })
            }
            StaticProperty::Accessor { getter, .. } => match getter {
                Some(mut getter) => {
                    getter.receiver = Some(receiver);
                    self.inline_closure(&getter, &[], Some(receiver), span)
                }
                None => Ok(Lowered::runtime(undefined_expression(span))),
            },
        }
    }

    fn assign_property(
        &mut self,
        receiver: ObjectId,
        property: &MemberProperty,
        operator: AssignmentOperator,
        value: &Expression,
        span: Span,
    ) -> Result<Lowered> {
        let key = static_property_key(property)?;
        if operator == AssignmentOperator::Assign {
            let mut value = self.lower_expression(value)?;
            let temporary = self.fresh_name("assign");
            let runtime_value = match &value.value {
                StaticValue::Runtime(value) => Some(value.clone()),
                _ => None,
            };
            if let Some(runtime_value) = runtime_value {
                value.prefix.push(variable_statement(
                    VariableKind::Let,
                    temporary.clone(),
                    Some(runtime_value),
                    span,
                ));
                let mut write = self.write_property_value(
                    receiver,
                    &key,
                    StaticValue::Runtime(global_expression(temporary.clone(), span)),
                    span,
                )?;
                value.prefix.append(&mut write);
                value.value = StaticValue::Runtime(global_expression(temporary, span));
                return Ok(value);
            }
            let mut write = self.write_property_value(receiver, &key, value.value.clone(), span)?;
            value.prefix.append(&mut write);
            Ok(value)
        } else {
            // Preserve ECMAScript compound-assignment order:
            //
            //   1. resolve/get the current property value exactly once;
            //   2. materialize that value before evaluating the RHS;
            //   3. evaluate the RHS;
            //   4. let the normal typed assignment lowerer perform `op=`;
            //   5. invoke the resolved setter/write path with the new value.
            //
            // Keeping `op=` as an identifier assignment is important: the
            // analysis lattice sees a concrete lvalue type and can emit
            // BinaryNumber/phi directly instead of losing it in an untyped
            // `old <op> rhs` expression.
            let mut old = self.read_property(receiver, property, span)?;
            let old_value = require_runtime(old.value, "compound property left")?;
            let temporary = self.fresh_name("compound");
            let _ = assignment_binary_operator(operator)?;

            let mut prefix = Vec::new();
            prefix.append(&mut old.prefix);
            prefix.push(variable_statement(
                VariableKind::Let,
                temporary.clone(),
                Some(old_value),
                span,
            ));

            let mut right = self.lower_expression(value)?;
            prefix.append(&mut right.prefix);
            let right_value = require_runtime(right.value, "compound property right")?;
            prefix.push(Statement {
                kind: StatementKind::Expression(Expression {
                    kind: ExpressionKind::Assignment {
                        target: AssignmentTarget::Identifier(temporary.clone()),
                        operator,
                        value: Box::new(right_value),
                    },
                    span,
                }),
                span,
            });

            let mut write = self.write_property_value(
                receiver,
                &key,
                StaticValue::Runtime(global_expression(temporary.clone(), span)),
                span,
            )?;
            prefix.append(&mut write);
            Ok(Lowered {
                prefix,
                value: StaticValue::Runtime(global_expression(temporary, span)),
            })
        }
    }

    fn write_property_value(
        &mut self,
        receiver: ObjectId,
        key: &str,
        value: StaticValue,
        span: Span,
    ) -> Result<Vec<Statement>> {
        if let Some((_owner, StaticProperty::Accessor { setter, .. })) =
            self.lookup_property(receiver, key)?
        {
            let Some(mut setter) = setter else {
                bail!("assignment to getter-only static accessor `{key}`")
            };
            setter.receiver = Some(receiver);
            let argument = static_value_expression(&value, span)?;
            return Ok(self
                .inline_closure(&setter, &[argument], Some(receiver), span)?
                .prefix);
        }

        let own = self
            .objects
            .get(&receiver)
            .and_then(|object| object.properties.get(key))
            .cloned();
        match (own, value) {
            (
                Some(StaticProperty::Data {
                    value_name,
                    present: true,
                }),
                StaticValue::Runtime(value),
            ) => Ok(vec![assignment_statement(value_name, value, span)]),
            (Some(_), value) => {
                if self.control_depth != 0 {
                    bail!(
                        "conditional static property representation change for `{key}` is not SSA-normalized"
                    )
                }
                self.install_static_property_value(receiver, key.to_owned(), value, span)
            }
            (None, value) => {
                if self.control_depth != 0 {
                    bail!(
                        "conditional shape growth for static property `{key}` is not SSA-normalized"
                    )
                }
                self.install_static_property_value(receiver, key.to_owned(), value, span)
            }
        }
    }

    fn install_static_property_value(
        &mut self,
        receiver: ObjectId,
        key: String,
        value: StaticValue,
        span: Span,
    ) -> Result<Vec<Statement>> {
        match value {
            StaticValue::Runtime(value) => {
                let name = self.fresh_name(&format!("field_{key}"));
                self.install_property(
                    receiver,
                    key,
                    StaticProperty::Data {
                        value_name: name.clone(),
                        present: true,
                    },
                );
                Ok(vec![variable_statement(
                    VariableKind::Let,
                    name,
                    Some(value),
                    span,
                )])
            }
            StaticValue::Object(object) => {
                self.install_property(receiver, key, StaticProperty::Object(object));
                Ok(Vec::new())
            }
            StaticValue::Closure(closure) => {
                self.install_property(receiver, key, StaticProperty::Closure(closure));
                Ok(Vec::new())
            }
        }
    }

    fn delete_property(&mut self, receiver: ObjectId, key: &str) -> Result<()> {
        if self.control_depth != 0 {
            bail!("conditional delete on static object is not shape-SSA normalized")
        }
        let remove = match self
            .objects
            .get_mut(&receiver)
            .expect("static object")
            .properties
            .get_mut(key)
        {
            Some(StaticProperty::Data { present, .. }) => {
                *present = false;
                false
            }
            Some(_) => true,
            None => false,
        };
        if remove {
            self.objects
                .get_mut(&receiver)
                .expect("static object")
                .properties
                .remove(key);
        }
        Ok(())
    }

    fn lookup_property(
        &self,
        receiver: ObjectId,
        key: &str,
    ) -> Result<Option<(ObjectId, StaticProperty)>> {
        let mut current = Some(receiver);
        let mut seen = HashSet::new();
        while let Some(object_id) = current {
            if !seen.insert(object_id) {
                bail!("prototype cycle while resolving property `{key}`")
            }
            let object = self.objects.get(&object_id).expect("static object");
            if let Some(property) = object.properties.get(key) {
                return Ok(Some((object_id, property.clone())));
            }
            current = match object.prototype {
                Prototype::Object(prototype) => Some(prototype),
                Prototype::BuiltinObject | Prototype::Null => None,
            };
        }
        Ok(None)
    }

    fn has_property(&self, receiver: ObjectId, key: &str) -> Result<bool> {
        Ok(self
            .lookup_property(receiver, key)?
            .is_some_and(|(_, property)| {
                !matches!(property, StaticProperty::Data { present: false, .. })
            }))
    }

    fn ensure_no_prototype_cycle(&self, target: ObjectId, prototype: Prototype) -> Result<()> {
        let mut current = match prototype {
            Prototype::Object(id) => Some(id),
            Prototype::BuiltinObject | Prototype::Null => None,
        };
        let mut seen = HashSet::new();
        while let Some(id) = current {
            if id == target {
                bail!("Object.setPrototypeOf would create a prototype cycle")
            }
            if !seen.insert(id) {
                bail!("existing prototype graph contains a cycle")
            }
            current = match self.objects.get(&id).expect("static prototype").prototype {
                Prototype::Object(next) => Some(next),
                Prototype::BuiltinObject | Prototype::Null => None,
            };
        }
        Ok(())
    }

    fn inline_closure(
        &mut self,
        closure: &StaticClosure,
        arguments: &[Expression],
        receiver: Option<ObjectId>,
        span: Span,
    ) -> Result<Lowered> {
        if closure.function.r#async || closure.function.generator {
            bail!("async/generator static closure requires continuation/state-machine lowering")
        }
        if let Some(error) = &closure.function.lowering_error {
            bail!("static closure frontend lowering failed: {error}")
        }
        if !self.active_closures.insert(closure.id) {
            bail!("recursive static closure requires a convergent recursion specialization")
        }

        let result = (|| {
            let mut evaluated_arguments = Vec::with_capacity(arguments.len());
            let mut prefix = Vec::new();
            for argument in arguments {
                let mut lowered = self.lower_expression(argument)?;
                prefix.append(&mut lowered.prefix);
                evaluated_arguments.push(lowered.value);
            }

            let renamed = self.rename_function_for_inline(&closure.function)?;
            self.push_scope();
            let mut parameter_names = Vec::new();
            for (index, parameter) in renamed.parameters.iter().enumerate() {
                let name = parameter
                    .strip_prefix("@rest:")
                    .unwrap_or(parameter)
                    .to_owned();
                if parameter.starts_with("@rest:") {
                    bail!("rest parameter in static closure needs tuple expansion")
                }
                let value = evaluated_arguments
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| StaticValue::Runtime(undefined_expression(span)));
                match value {
                    StaticValue::Runtime(value) => {
                        prefix.push(variable_statement(
                            VariableKind::Let,
                            name.clone(),
                            Some(value),
                            span,
                        ));
                        self.shadow_runtime(name.clone());
                    }
                    StaticValue::Object(id) => {
                        self.bind_static(name.clone(), StaticBinding::Object(id))?;
                    }
                    StaticValue::Closure(closure) => {
                        self.bind_static(name.clone(), StaticBinding::Closure(closure))?;
                    }
                }
                parameter_names.push(name);
            }
            for extra in evaluated_arguments.iter().skip(parameter_names.len()) {
                if let StaticValue::Runtime(extra) = extra {
                    prefix.push(Statement {
                        kind: StatementKind::Expression(extra.clone()),
                        span: extra.span,
                    });
                }
            }

            self.this_stack.push(receiver.or(closure.receiver));
            let result = if let Some((head, tail)) = split_final_return(&renamed.body) {
                if head.iter().any(statement_contains_return) {
                    self.inline_control_flow_function(&renamed, &mut prefix, span)?
                } else {
                    prefix.extend(self.lower_statements(head)?);
                    match tail {
                        Some(value) => {
                            let mut value = self.lower_expression(value)?;
                            prefix.append(&mut value.prefix);
                            Lowered {
                                prefix,
                                value: value.value,
                            }
                        }
                        None => Lowered {
                            prefix,
                            value: StaticValue::Runtime(undefined_expression(span)),
                        },
                    }
                }
            } else if !renamed.body.iter().any(statement_contains_return) {
                // A returnless closure has only normal fallthrough completion.
                // Do not synthesize an `inline_result = undefined` plus a
                // labeled completion region: that creates a fake SSA state
                // dimension and can overwrite captured-mutation flow at the
                // label merge. Lower the body directly and expose only the
                // language-mandated undefined call result.
                prefix.extend(self.lower_statements(&renamed.body)?);
                Lowered {
                    prefix,
                    value: StaticValue::Runtime(undefined_expression(span)),
                }
            } else {
                self.inline_control_flow_function(&renamed, &mut prefix, span)?
            };
            self.this_stack.pop();
            self.pop_scope();
            Ok(result)
        })();

        self.active_closures.remove(&closure.id);
        result
    }

    fn inline_control_flow_function(
        &mut self,
        function: &Function,
        prefix: &mut Vec<Statement>,
        span: Span,
    ) -> Result<Lowered> {
        let result_name = self.fresh_name("inline_result");
        let label = self.fresh_name("inline_exit");
        prefix.push(variable_statement(
            VariableKind::Let,
            result_name.clone(),
            Some(undefined_expression(span)),
            span,
        ));
        self.shadow_runtime(result_name.clone());
        let body = function
            .body
            .iter()
            .map(|statement| rewrite_returns(statement, &label, &result_name))
            .collect::<Vec<_>>();
        let labeled = Statement {
            kind: StatementKind::Labeled {
                label,
                body: Box::new(Statement {
                    kind: StatementKind::Block(body),
                    span,
                }),
            },
            span,
        };
        prefix.extend(self.lower_statement(&labeled)?);
        Ok(Lowered {
            prefix: std::mem::take(prefix),
            value: StaticValue::Runtime(global_expression(result_name, span)),
        })
    }

    fn rename_function_for_inline(&mut self, function: &Function) -> Result<Function> {
        let mut names = function
            .parameters
            .iter()
            .map(|parameter| {
                parameter
                    .strip_prefix("@rest:")
                    .unwrap_or(parameter)
                    .to_owned()
            })
            .collect::<Vec<_>>();
        collect_function_local_names(&function.body, &mut names);
        let mut seen = HashSet::new();
        for name in &names {
            if !seen.insert(name.clone()) {
                bail!(
                    "shadowed local `{name}` in static closure needs lexical-scope alpha conversion"
                )
            }
        }
        let mut mapping = HashMap::new();
        for name in names {
            mapping.insert(name.clone(), self.fresh_name(&name));
        }
        rename_function(function, &mapping)
    }
}

/// Return true when a runtime receiver should cross an ANF statement boundary
/// before a property access.
///
/// Global/This are already atomic references. Primitive literals are also
/// atomic (their eventual property semantics are validated by later lowering).
/// Everything else may contain evaluation, allocation, or a nested aggregate.
fn runtime_member_receiver_needs_anf(expression: &Expression) -> bool {
    !matches!(
        &expression.kind,
        ExpressionKind::Global(_)
            | ExpressionKind::This
            | ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
    )
}

fn require_runtime(value: StaticValue, context: &str) -> Result<Expression> {
    match value {
        StaticValue::Runtime(value) => Ok(value),
        StaticValue::Object(_) => {
            bail!("{context} would expose an erased static object identity")
        }
        StaticValue::Closure(_) => {
            bail!("{context} would expose an erased static closure identity")
        }
    }
}

fn static_value_expression(value: &StaticValue, _span: Span) -> Result<Expression> {
    match value {
        StaticValue::Runtime(value) => Ok(value.clone()),
        StaticValue::Object(_) => {
            bail!("passing a static object into an accessor requires object-state parameters")
        }
        StaticValue::Closure(_) => {
            bail!("passing a static closure as a runtime argument requires defunctionalization")
        }
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

fn assignment_statement(name: String, value: Expression, span: Span) -> Statement {
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

fn global_expression(name: String, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Global(name),
        span,
    }
}

fn undefined_expression(span: Span) -> Expression {
    global_expression("undefined".to_owned(), span)
}

fn null_expression(span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Null,
        span,
    }
}

fn bool_expression(value: bool, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Bool(value),
        span,
    }
}

fn number_expression(value: f64, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::Number(value),
        span,
    }
}

fn string_expression(value: &str, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::String(value.to_owned()),
        span,
    }
}

fn static_property_key(property: &MemberProperty) -> Result<String> {
    match property {
        MemberProperty::Static(key) => Ok(key.clone()),
        MemberProperty::Computed(value) => match &value.kind {
            ExpressionKind::String(value) => Ok(value.clone()),
            ExpressionKind::Number(value) => Ok(value.to_string()),
            _ => bail!("computed prototype/accessor property key is not statically known"),
        },
    }
}

fn runtime_literal_key(value: &StaticValue) -> Result<String> {
    let StaticValue::Runtime(value) = value else {
        bail!("static object/closure cannot be used as a property key")
    };
    match &value.kind {
        ExpressionKind::String(value) => Ok(value.clone()),
        ExpressionKind::Number(value) => Ok(value.to_string()),
        _ => bail!("`in` key is not a static String/Number"),
    }
}

fn is_nullish_runtime(value: &Expression) -> bool {
    matches!(&value.kind, ExpressionKind::Null)
        || matches!(&value.kind, ExpressionKind::Global(name) if name == "undefined")
}

fn assignment_binary_operator(operator: AssignmentOperator) -> Result<BinaryOperator> {
    Ok(match operator {
        AssignmentOperator::Add => BinaryOperator::Add,
        AssignmentOperator::Subtract => BinaryOperator::Subtract,
        AssignmentOperator::Multiply => BinaryOperator::Multiply,
        AssignmentOperator::Divide => BinaryOperator::Divide,
        AssignmentOperator::Remainder => BinaryOperator::Remainder,
        AssignmentOperator::Exponential => BinaryOperator::Exponential,
        AssignmentOperator::ShiftLeft => BinaryOperator::ShiftLeft,
        AssignmentOperator::ShiftRight => BinaryOperator::ShiftRight,
        AssignmentOperator::ShiftRightZeroFill => BinaryOperator::ShiftRightZeroFill,
        AssignmentOperator::BitwiseOr => BinaryOperator::BitwiseOr,
        AssignmentOperator::BitwiseXor => BinaryOperator::BitwiseXor,
        AssignmentOperator::BitwiseAnd => BinaryOperator::BitwiseAnd,
        AssignmentOperator::Assign
        | AssignmentOperator::LogicalOr
        | AssignmentOperator::LogicalAnd
        | AssignmentOperator::LogicalNullish => {
            bail!("assignment operator is not a compound binary operator")
        }
    })
}

fn split_final_return(body: &[Statement]) -> Option<(&[Statement], Option<&Expression>)> {
    let (last, head) = body.split_last()?;
    let StatementKind::Return(value) = &last.kind else {
        return None;
    };
    Some((head, value.as_ref()))
}

fn statement_contains_return(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Return(_) => true,
        StatementKind::Block(body) => body.iter().any(statement_contains_return),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            statement_contains_return(consequent)
                || alternate.as_deref().is_some_and(statement_contains_return)
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => statement_contains_return(body),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|case| &case.consequent)
            .any(statement_contains_return),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_contains_return(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| statement_contains_return(&handler.body))
                || finalizer.as_deref().is_some_and(statement_contains_return)
        }
        StatementKind::FunctionDeclaration(_)
        | StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Expression(_)
        | StatementKind::VariableDeclaration { .. }
        | StatementKind::Throw(_)
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn collect_exception_inline_functions(statements: &[Statement]) -> HashSet<String> {
    let functions = statements
        .iter()
        .filter_map(|statement| match &statement.kind {
            StatementKind::FunctionDeclaration(function) => function
                .name
                .as_ref()
                .map(|name| (name.clone(), function.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let mut forced = functions
        .iter()
        .filter(|(_, function)| {
            function
                .body
                .iter()
                .any(statement_contains_direct_exception)
        })
        .map(|(name, _)| name.clone())
        .collect::<HashSet<_>>();
    loop {
        let mut changed = false;
        for (name, function) in &functions {
            if forced.contains(name) {
                continue;
            }
            if function
                .body
                .iter()
                .any(|statement| statement_calls_any(statement, &forced))
            {
                forced.insert(name.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    forced
}

fn statement_contains_direct_exception(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Try { .. } | StatementKind::Throw(_) => true,
        StatementKind::Block(body) => body.iter().any(statement_contains_direct_exception),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            statement_contains_direct_exception(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(statement_contains_direct_exception)
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => statement_contains_direct_exception(body),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|case| &case.consequent)
            .any(statement_contains_direct_exception),
        StatementKind::FunctionDeclaration(_)
        | StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Expression(_)
        | StatementKind::VariableDeclaration { .. }
        | StatementKind::Return(_)
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn statement_calls_any(statement: &Statement, names: &HashSet<String>) -> bool {
    fn expression(value: &Expression, names: &HashSet<String>) -> bool {
        match &value.kind {
            ExpressionKind::Call { callee, arguments } => {
                matches!(&callee.kind, ExpressionKind::Global(name) if names.contains(name))
                    || expression(callee, names)
                    || arguments.iter().any(|value| expression(value, names))
            }
            ExpressionKind::Member { object, property } => {
                expression(object, names)
                    || matches!(property, MemberProperty::Computed(value) if expression(value, names))
            }
            ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
                ObjectEntry::Property(property) => expression(&property.value, names),
                ObjectEntry::Spread(value) => expression(value, names),
                ObjectEntry::Accessor { .. } => false,
            }),
            ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
                ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                    expression(value, names)
                }
                ArrayElement::Hole => false,
            }),
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => {
                expression(test, names)
                    || expression(consequent, names)
                    || expression(alternate, names)
            }
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                expression(argument, names)
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                expression(left, names) || expression(right, names)
            }
            ExpressionKind::Assignment { value, .. } => expression(value, names),
            ExpressionKind::New { callee, arguments } => {
                expression(callee, names) || arguments.iter().any(|value| expression(value, names))
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
        StatementKind::Expression(value) | StatementKind::Throw(value) => expression(value, names),
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|value| value.init.as_ref())
            .any(|value| expression(value, names)),
        StatementKind::Block(body) => body.iter().any(|value| statement_calls_any(value, names)),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression(test, names)
                || statement_calls_any(consequent, names)
                || alternate
                    .as_deref()
                    .is_some_and(|value| statement_calls_any(value, names))
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression(test, names) || statement_calls_any(body, names)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => expression(value, names),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|value| value.init.as_ref())
                    .any(|value| expression(value, names)),
            }) || test.as_ref().is_some_and(|value| expression(value, names))
                || update
                    .as_ref()
                    .is_some_and(|value| expression(value, names))
                || statement_calls_any(body, names)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expression(right, names) || statement_calls_any(body, names)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expression(discriminant, names)
                || cases.iter().any(|case| {
                    case.test
                        .as_ref()
                        .is_some_and(|value| expression(value, names))
                        || case
                            .consequent
                            .iter()
                            .any(|value| statement_calls_any(value, names))
                })
        }
        StatementKind::Labeled { body, .. } => statement_calls_any(body, names),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_calls_any(block, names)
                || handler
                    .as_ref()
                    .is_some_and(|handler| statement_calls_any(&handler.body, names))
                || finalizer
                    .as_deref()
                    .is_some_and(|value| statement_calls_any(value, names))
        }
        StatementKind::Return(value) => {
            value.as_ref().is_some_and(|value| expression(value, names))
        }
        StatementKind::FunctionDeclaration(_)
        | StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn function_needs_static_inline(function: &Function) -> bool {
    function.body.iter().any(statement_needs_static_inline)
}

fn statement_needs_static_inline(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            expression_needs_static_inline(value)
        }
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|declaration| declaration.init.as_ref())
            .any(expression_needs_static_inline),
        StatementKind::Block(body) => body.iter().any(statement_needs_static_inline),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression_needs_static_inline(test)
                || statement_needs_static_inline(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(statement_needs_static_inline)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression_needs_static_inline(test) || statement_needs_static_inline(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => expression_needs_static_inline(value),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|declaration| declaration.init.as_ref())
                    .any(expression_needs_static_inline),
            }) || test.as_ref().is_some_and(expression_needs_static_inline)
                || update.as_ref().is_some_and(expression_needs_static_inline)
                || statement_needs_static_inline(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expression_needs_static_inline(right) || statement_needs_static_inline(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expression_needs_static_inline(discriminant)
                || cases.iter().any(|case| {
                    case.test
                        .as_ref()
                        .is_some_and(expression_needs_static_inline)
                        || case.consequent.iter().any(statement_needs_static_inline)
                })
        }
        StatementKind::Labeled { body, .. } => statement_needs_static_inline(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_needs_static_inline(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| statement_needs_static_inline(&handler.body))
                || finalizer
                    .as_deref()
                    .is_some_and(statement_needs_static_inline)
        }
        StatementKind::FunctionDeclaration(_) => true,
        StatementKind::Return(value) => value.as_ref().is_some_and(expression_needs_static_inline),
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn expression_needs_static_inline(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Function(_) | ExpressionKind::This => true,
        ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
            ObjectEntry::Accessor { .. } => true,
            ObjectEntry::Property(property) => expression_needs_static_inline(&property.value),
            ObjectEntry::Spread(value) => expression_needs_static_inline(value),
        }),
        ExpressionKind::Call { callee, arguments } => {
            is_object_graph_builtin(callee)
                || matches!(
                    &callee.kind,
                    ExpressionKind::Member {
                        property: MemberProperty::Static(method),
                        ..
                    } if matches!(method.as_str(), "next" | "return" | "throw")
                )
                || expression_needs_static_inline(callee)
                || arguments.iter().any(expression_needs_static_inline)
        }
        ExpressionKind::Member { object, property } => {
            expression_needs_static_inline(object)
                || matches!(
                    property,
                    MemberProperty::Computed(value)
                        if expression_needs_static_inline(value)
                )
        }
        ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
            ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                expression_needs_static_inline(value)
            }
            ArrayElement::Hole => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            expression_needs_static_inline(test)
                || expression_needs_static_inline(consequent)
                || expression_needs_static_inline(alternate)
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            expression_needs_static_inline(argument)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            expression_needs_static_inline(left) || expression_needs_static_inline(right)
        }
        ExpressionKind::Assignment { target, value, .. } => {
            target_needs_static_inline(target) || expression_needs_static_inline(value)
        }
        ExpressionKind::Update { target, .. } => target_needs_static_inline(target),
        ExpressionKind::New { callee, arguments } => {
            expression_needs_static_inline(callee)
                || arguments.iter().any(expression_needs_static_inline)
        }
        ExpressionKind::Global(name) => {
            name.starts_with("@gen_factory_") || name.starts_with("@gen_resume_")
        }
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null => false,
    }
}

fn target_needs_static_inline(target: &AssignmentTarget) -> bool {
    match target {
        AssignmentTarget::Identifier(_) => false,
        AssignmentTarget::Member { object, property } => {
            expression_needs_static_inline(object)
                || matches!(
                    property,
                    MemberProperty::Computed(value)
                        if expression_needs_static_inline(value)
                )
        }
    }
}

fn is_object_graph_builtin(callee: &Expression) -> bool {
    matches!(
        &callee.kind,
        ExpressionKind::Member {
            object,
            property: MemberProperty::Static(method),
        } if matches!(&object.kind, ExpressionKind::Global(name) if name == "Object")
            && matches!(
                method.as_str(),
                "create" | "setPrototypeOf" | "getPrototypeOf"
            )
    )
}

fn collect_function_local_names(statements: &[Statement], output: &mut Vec<String>) {
    for statement in statements {
        match &statement.kind {
            StatementKind::VariableDeclaration { declarations, .. } => {
                output.extend(
                    declarations
                        .iter()
                        .map(|declaration| declaration.name.clone()),
                );
            }
            StatementKind::Block(body) => collect_function_local_names(body, output),
            StatementKind::If {
                consequent,
                alternate,
                ..
            } => {
                collect_function_local_names(std::slice::from_ref(consequent.as_ref()), output);
                if let Some(alternate) = alternate {
                    collect_function_local_names(std::slice::from_ref(alternate.as_ref()), output);
                }
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Labeled { body, .. } => {
                collect_function_local_names(std::slice::from_ref(body.as_ref()), output)
            }
            StatementKind::For { init, body, .. } => {
                if let Some(ForInit::VariableDeclaration { declarations, .. }) = init {
                    output.extend(
                        declarations
                            .iter()
                            .map(|declaration| declaration.name.clone()),
                    );
                }
                collect_function_local_names(std::slice::from_ref(body.as_ref()), output);
            }
            StatementKind::ForIn { name, body, .. } | StatementKind::ForOf { name, body, .. } => {
                output.push(name.clone());
                collect_function_local_names(std::slice::from_ref(body.as_ref()), output);
            }
            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    collect_function_local_names(&case.consequent, output);
                }
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                collect_function_local_names(std::slice::from_ref(block.as_ref()), output);
                if let Some(handler) = handler {
                    if let Some(parameter) = &handler.parameter {
                        output.push(parameter.clone());
                    }
                    collect_function_local_names(
                        std::slice::from_ref(handler.body.as_ref()),
                        output,
                    );
                }
                if let Some(finalizer) = finalizer {
                    collect_function_local_names(std::slice::from_ref(finalizer.as_ref()), output);
                }
            }
            StatementKind::FunctionDeclaration(function) => {
                if let Some(name) = &function.name {
                    output.push(name.clone());
                }
            }
            StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Expression(_)
            | StatementKind::Return(_)
            | StatementKind::Throw(_)
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
        }
    }
}

fn function_bound_names(function: &Function) -> HashSet<String> {
    let mut names = function
        .parameters
        .iter()
        .map(|parameter| {
            parameter
                .strip_prefix("@rest:")
                .unwrap_or(parameter)
                .to_owned()
        })
        .collect::<Vec<_>>();
    if let Some(name) = &function.name {
        names.push(name.clone());
    }
    collect_function_local_names(&function.body, &mut names);
    names.into_iter().collect()
}

fn rename_function(function: &Function, mapping: &HashMap<String, String>) -> Result<Function> {
    Ok(Function {
        name: function
            .name
            .as_ref()
            .map(|name| mapping.get(name).cloned().unwrap_or_else(|| name.clone())),
        parameters: function
            .parameters
            .iter()
            .map(|parameter| {
                if let Some(rest) = parameter.strip_prefix("@rest:") {
                    format!(
                        "@rest:{}",
                        mapping
                            .get(rest)
                            .cloned()
                            .unwrap_or_else(|| rest.to_owned())
                    )
                } else {
                    mapping
                        .get(parameter)
                        .cloned()
                        .unwrap_or_else(|| parameter.clone())
                }
            })
            .collect(),
        body: function
            .body
            .iter()
            .map(|statement| rename_statement(statement, mapping))
            .collect::<Result<Vec<_>>>()?,
        r#async: function.r#async,
        generator: function.generator,
        arrow: function.arrow,
        lowering_error: function.lowering_error.clone(),
    })
}

fn rename_nested_function(
    function: &Function,
    outer_mapping: &HashMap<String, String>,
) -> Result<Function> {
    let bound = function_bound_names(function);
    let filtered = outer_mapping
        .iter()
        .filter(|(name, _)| !bound.contains(*name))
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect::<HashMap<_, _>>();
    rename_function(function, &filtered)
}

fn rename_statement(statement: &Statement, mapping: &HashMap<String, String>) -> Result<Statement> {
    let span = statement.span;
    Ok(Statement {
        kind: match &statement.kind {
            StatementKind::Empty => StatementKind::Empty,
            StatementKind::Debugger => StatementKind::Debugger,
            StatementKind::Expression(value) => {
                StatementKind::Expression(rename_expression(value, mapping)?)
            }
            StatementKind::VariableDeclaration { kind, declarations } => {
                StatementKind::VariableDeclaration {
                    kind: *kind,
                    declarations: declarations
                        .iter()
                        .map(|declaration| {
                            Ok(VariableDeclarator {
                                name: mapping
                                    .get(&declaration.name)
                                    .cloned()
                                    .unwrap_or_else(|| declaration.name.clone()),
                                init: declaration
                                    .init
                                    .as_ref()
                                    .map(|value| rename_expression(value, mapping))
                                    .transpose()?,
                                span: declaration.span,
                            })
                        })
                        .collect::<Result<Vec<_>>>()?,
                }
            }
            StatementKind::Block(body) => StatementKind::Block(
                body.iter()
                    .map(|statement| rename_statement(statement, mapping))
                    .collect::<Result<Vec<_>>>()?,
            ),
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => StatementKind::If {
                test: rename_expression(test, mapping)?,
                consequent: Box::new(rename_statement(consequent, mapping)?),
                alternate: alternate
                    .as_deref()
                    .map(|alternate| rename_statement(alternate, mapping).map(Box::new))
                    .transpose()?,
            },
            StatementKind::While { test, body } => StatementKind::While {
                test: rename_expression(test, mapping)?,
                body: Box::new(rename_statement(body, mapping)?),
            },
            StatementKind::DoWhile { body, test } => StatementKind::DoWhile {
                body: Box::new(rename_statement(body, mapping)?),
                test: rename_expression(test, mapping)?,
            },
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => StatementKind::For {
                init: init
                    .as_ref()
                    .map(|init| rename_for_init(init, mapping))
                    .transpose()?,
                test: test
                    .as_ref()
                    .map(|test| rename_expression(test, mapping))
                    .transpose()?,
                update: update
                    .as_ref()
                    .map(|update| rename_expression(update, mapping))
                    .transpose()?,
                body: Box::new(rename_statement(body, mapping)?),
            },
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => StatementKind::ForIn {
                name: mapping.get(name).cloned().unwrap_or_else(|| name.clone()),
                kind: *kind,
                right: rename_expression(right, mapping)?,
                body: Box::new(rename_statement(body, mapping)?),
            },
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => StatementKind::ForOf {
                name: mapping.get(name).cloned().unwrap_or_else(|| name.clone()),
                kind: *kind,
                right: rename_expression(right, mapping)?,
                body: Box::new(rename_statement(body, mapping)?),
            },
            StatementKind::Switch {
                discriminant,
                cases,
            } => StatementKind::Switch {
                discriminant: rename_expression(discriminant, mapping)?,
                cases: cases
                    .iter()
                    .map(|case| {
                        Ok(SwitchCase {
                            test: case
                                .test
                                .as_ref()
                                .map(|test| rename_expression(test, mapping))
                                .transpose()?,
                            consequent: case
                                .consequent
                                .iter()
                                .map(|statement| rename_statement(statement, mapping))
                                .collect::<Result<Vec<_>>>()?,
                            span: case.span,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?,
            },
            StatementKind::Labeled { label, body } => StatementKind::Labeled {
                label: label.clone(),
                body: Box::new(rename_statement(body, mapping)?),
            },
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => StatementKind::Try {
                block: Box::new(rename_statement(block, mapping)?),
                handler: handler
                    .as_ref()
                    .map(|handler| -> Result<CatchClause> {
                        Ok(CatchClause {
                            parameter: handler.parameter.as_ref().map(|parameter| {
                                mapping
                                    .get(parameter)
                                    .cloned()
                                    .unwrap_or_else(|| parameter.clone())
                            }),
                            body: Box::new(rename_statement(&handler.body, mapping)?),
                            span: handler.span,
                        })
                    })
                    .transpose()?,
                finalizer: finalizer
                    .as_deref()
                    .map(|finalizer| rename_statement(finalizer, mapping).map(Box::new))
                    .transpose()?,
            },
            StatementKind::FunctionDeclaration(function) => {
                StatementKind::FunctionDeclaration(rename_nested_function(function, mapping)?)
            }
            StatementKind::Return(value) => StatementKind::Return(
                value
                    .as_ref()
                    .map(|value| rename_expression(value, mapping))
                    .transpose()?,
            ),
            StatementKind::Throw(value) => StatementKind::Throw(rename_expression(value, mapping)?),
            StatementKind::Break(label) => StatementKind::Break(label.clone()),
            StatementKind::Continue(label) => StatementKind::Continue(label.clone()),
        },
        span,
    })
}

fn rename_for_init(init: &ForInit, mapping: &HashMap<String, String>) -> Result<ForInit> {
    Ok(match init {
        ForInit::Expression(value) => ForInit::Expression(rename_expression(value, mapping)?),
        ForInit::VariableDeclaration { kind, declarations } => ForInit::VariableDeclaration {
            kind: *kind,
            declarations: declarations
                .iter()
                .map(|declaration| {
                    Ok(VariableDeclarator {
                        name: mapping
                            .get(&declaration.name)
                            .cloned()
                            .unwrap_or_else(|| declaration.name.clone()),
                        init: declaration
                            .init
                            .as_ref()
                            .map(|value| rename_expression(value, mapping))
                            .transpose()?,
                        span: declaration.span,
                    })
                })
                .collect::<Result<Vec<_>>>()?,
        },
    })
}

fn rename_expression(
    expression: &Expression,
    mapping: &HashMap<String, String>,
) -> Result<Expression> {
    let span = expression.span;
    Ok(Expression {
        kind: match &expression.kind {
            ExpressionKind::String(value) => ExpressionKind::String(value.clone()),
            ExpressionKind::Number(value) => ExpressionKind::Number(*value),
            ExpressionKind::BigInt(value) => ExpressionKind::BigInt(value.clone()),
            ExpressionKind::Bool(value) => ExpressionKind::Bool(*value),
            ExpressionKind::Null => ExpressionKind::Null,
            ExpressionKind::This => ExpressionKind::This,
            ExpressionKind::Global(name) => {
                ExpressionKind::Global(mapping.get(name).cloned().unwrap_or_else(|| name.clone()))
            }
            ExpressionKind::Member { object, property } => ExpressionKind::Member {
                object: Box::new(rename_expression(object, mapping)?),
                property: rename_member_property(property, mapping)?,
            },
            ExpressionKind::Object(entries) => ExpressionKind::Object(
                entries
                    .iter()
                    .map(|entry| rename_object_entry(entry, mapping))
                    .collect::<Result<Vec<_>>>()?,
            ),
            ExpressionKind::Array(elements) => ExpressionKind::Array(
                elements
                    .iter()
                    .map(|element| rename_array_element(element, mapping))
                    .collect::<Result<Vec<_>>>()?,
            ),
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => ExpressionKind::Conditional {
                test: Box::new(rename_expression(test, mapping)?),
                consequent: Box::new(rename_expression(consequent, mapping)?),
                alternate: Box::new(rename_expression(alternate, mapping)?),
            },
            ExpressionKind::Unary { operator, argument } => ExpressionKind::Unary {
                operator: *operator,
                argument: Box::new(rename_expression(argument, mapping)?),
            },
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => ExpressionKind::Binary {
                left: Box::new(rename_expression(left, mapping)?),
                operator: *operator,
                right: Box::new(rename_expression(right, mapping)?),
            },
            ExpressionKind::Logical {
                left,
                operator,
                right,
            } => ExpressionKind::Logical {
                left: Box::new(rename_expression(left, mapping)?),
                operator: *operator,
                right: Box::new(rename_expression(right, mapping)?),
            },
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => ExpressionKind::Assignment {
                target: rename_assignment_target(target, mapping)?,
                operator: *operator,
                value: Box::new(rename_expression(value, mapping)?),
            },
            ExpressionKind::Update {
                target,
                operator,
                prefix,
            } => ExpressionKind::Update {
                target: rename_assignment_target(target, mapping)?,
                operator: *operator,
                prefix: *prefix,
            },
            ExpressionKind::Call { callee, arguments } => ExpressionKind::Call {
                callee: Box::new(rename_expression(callee, mapping)?),
                arguments: arguments
                    .iter()
                    .map(|argument| rename_expression(argument, mapping))
                    .collect::<Result<Vec<_>>>()?,
            },
            ExpressionKind::New { callee, arguments } => ExpressionKind::New {
                callee: Box::new(rename_expression(callee, mapping)?),
                arguments: arguments
                    .iter()
                    .map(|argument| rename_expression(argument, mapping))
                    .collect::<Result<Vec<_>>>()?,
            },
            ExpressionKind::Function(function) => {
                ExpressionKind::Function(rename_nested_function(function, mapping)?)
            }
            ExpressionKind::Await(value) => {
                ExpressionKind::Await(Box::new(rename_expression(value, mapping)?))
            }
        },
        span,
    })
}

fn rename_member_property(
    property: &MemberProperty,
    mapping: &HashMap<String, String>,
) -> Result<MemberProperty> {
    Ok(match property {
        MemberProperty::Static(key) => MemberProperty::Static(key.clone()),
        MemberProperty::Computed(value) => {
            MemberProperty::Computed(Box::new(rename_expression(value, mapping)?))
        }
    })
}

fn rename_object_entry(
    entry: &ObjectEntry,
    mapping: &HashMap<String, String>,
) -> Result<ObjectEntry> {
    Ok(match entry {
        ObjectEntry::Property(property) => ObjectEntry::Property(ecmora_hir::ObjectProperty {
            key: rename_member_property(&property.key, mapping)?,
            value: rename_expression(&property.value, mapping)?,
        }),
        ObjectEntry::Spread(value) => ObjectEntry::Spread(rename_expression(value, mapping)?),
        ObjectEntry::Accessor { key, get, set } => ObjectEntry::Accessor {
            key: key.clone(),
            get: get
                .as_ref()
                .map(|value| rename_expression(value, mapping))
                .transpose()?,
            set: set
                .as_ref()
                .map(|value| rename_expression(value, mapping))
                .transpose()?,
        },
    })
}

fn rename_array_element(
    element: &ArrayElement,
    mapping: &HashMap<String, String>,
) -> Result<ArrayElement> {
    Ok(match element {
        ArrayElement::Expression(value) => {
            ArrayElement::Expression(rename_expression(value, mapping)?)
        }
        ArrayElement::Spread(value) => ArrayElement::Spread(rename_expression(value, mapping)?),
        ArrayElement::Hole => ArrayElement::Hole,
    })
}

fn rename_assignment_target(
    target: &AssignmentTarget,
    mapping: &HashMap<String, String>,
) -> Result<AssignmentTarget> {
    Ok(match target {
        AssignmentTarget::Identifier(name) => {
            AssignmentTarget::Identifier(mapping.get(name).cloned().unwrap_or_else(|| name.clone()))
        }
        AssignmentTarget::Member { object, property } => AssignmentTarget::Member {
            object: Box::new(rename_expression(object, mapping)?),
            property: rename_member_property(property, mapping)?,
        },
    })
}

fn rewrite_returns(statement: &Statement, label: &str, result: &str) -> Statement {
    let span = statement.span;
    let kind = match &statement.kind {
        StatementKind::Return(value) => {
            let mut body = Vec::new();
            if let Some(value) = value {
                body.push(assignment_statement(result.to_owned(), value.clone(), span));
            }
            body.push(Statement {
                kind: StatementKind::Break(Some(label.to_owned())),
                span,
            });
            StatementKind::Block(body)
        }
        StatementKind::Block(body) => StatementKind::Block(
            body.iter()
                .map(|statement| rewrite_returns(statement, label, result))
                .collect(),
        ),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => StatementKind::If {
            test: test.clone(),
            consequent: Box::new(rewrite_returns(consequent, label, result)),
            alternate: alternate
                .as_deref()
                .map(|alternate| Box::new(rewrite_returns(alternate, label, result))),
        },
        StatementKind::While { test, body } => StatementKind::While {
            test: test.clone(),
            body: Box::new(rewrite_returns(body, label, result)),
        },
        StatementKind::DoWhile { body, test } => StatementKind::DoWhile {
            body: Box::new(rewrite_returns(body, label, result)),
            test: test.clone(),
        },
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => StatementKind::For {
            init: init.clone(),
            test: test.clone(),
            update: update.clone(),
            body: Box::new(rewrite_returns(body, label, result)),
        },
        StatementKind::ForIn {
            name,
            kind,
            right,
            body,
        } => StatementKind::ForIn {
            name: name.clone(),
            kind: *kind,
            right: right.clone(),
            body: Box::new(rewrite_returns(body, label, result)),
        },
        StatementKind::ForOf {
            name,
            kind,
            right,
            body,
        } => StatementKind::ForOf {
            name: name.clone(),
            kind: *kind,
            right: right.clone(),
            body: Box::new(rewrite_returns(body, label, result)),
        },
        StatementKind::Switch {
            discriminant,
            cases,
        } => StatementKind::Switch {
            discriminant: discriminant.clone(),
            cases: cases
                .iter()
                .map(|case| SwitchCase {
                    test: case.test.clone(),
                    consequent: case
                        .consequent
                        .iter()
                        .map(|statement| rewrite_returns(statement, label, result))
                        .collect(),
                    span: case.span,
                })
                .collect(),
        },
        StatementKind::Labeled {
            label: nested,
            body,
        } => StatementKind::Labeled {
            label: nested.clone(),
            body: Box::new(rewrite_returns(body, label, result)),
        },
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => StatementKind::Try {
            block: Box::new(rewrite_returns(block, label, result)),
            handler: handler.as_ref().map(|handler| CatchClause {
                parameter: handler.parameter.clone(),
                body: Box::new(rewrite_returns(&handler.body, label, result)),
                span: handler.span,
            }),
            finalizer: finalizer
                .as_deref()
                .map(|finalizer| Box::new(rewrite_returns(finalizer, label, result))),
        },
        StatementKind::FunctionDeclaration(_) => statement.kind.clone(),
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Expression(_)
        | StatementKind::VariableDeclaration { .. }
        | StatementKind::Throw(_)
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => statement.kind.clone(),
    };
    Statement { kind, span }
}

fn object_entries_need_graph(entries: &[ObjectEntry]) -> bool {
    entries.iter().any(|entry| match entry {
        ObjectEntry::Accessor { .. } => true,
        ObjectEntry::Property(property) => {
            matches!(&property.value.kind, ExpressionKind::Function(_))
        }
        ObjectEntry::Spread(_) => false,
    })
}

fn collect_prototype_object_names(statements: &[Statement]) -> HashSet<String> {
    let mut output = HashSet::new();
    for statement in statements {
        collect_prototype_names_statement(statement, &mut output);
    }
    output
}

fn collect_prototype_names_statement(statement: &Statement, output: &mut HashSet<String>) {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            collect_prototype_names_expression(value, output);
        }
        StatementKind::VariableDeclaration { declarations, .. } => {
            for declaration in declarations {
                if let Some(value) = &declaration.init {
                    collect_prototype_names_expression(value, output);
                }
            }
        }
        StatementKind::Block(body) => {
            for statement in body {
                collect_prototype_names_statement(statement, output);
            }
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            collect_prototype_names_expression(test, output);
            collect_prototype_names_statement(consequent, output);
            if let Some(alternate) = alternate {
                collect_prototype_names_statement(alternate, output);
            }
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            collect_prototype_names_expression(test, output);
            collect_prototype_names_statement(body, output);
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            if let Some(init) = init {
                match init {
                    ForInit::Expression(value) => collect_prototype_names_expression(value, output),
                    ForInit::VariableDeclaration { declarations, .. } => {
                        for declaration in declarations {
                            if let Some(value) = &declaration.init {
                                collect_prototype_names_expression(value, output);
                            }
                        }
                    }
                }
            }
            if let Some(test) = test {
                collect_prototype_names_expression(test, output);
            }
            if let Some(update) = update {
                collect_prototype_names_expression(update, output);
            }
            collect_prototype_names_statement(body, output);
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            collect_prototype_names_expression(right, output);
            collect_prototype_names_statement(body, output);
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            collect_prototype_names_expression(discriminant, output);
            for case in cases {
                if let Some(test) = &case.test {
                    collect_prototype_names_expression(test, output);
                }
                for statement in &case.consequent {
                    collect_prototype_names_statement(statement, output);
                }
            }
        }
        StatementKind::Labeled { body, .. } => collect_prototype_names_statement(body, output),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            collect_prototype_names_statement(block, output);
            if let Some(handler) = handler {
                collect_prototype_names_statement(&handler.body, output);
            }
            if let Some(finalizer) = finalizer {
                collect_prototype_names_statement(finalizer, output);
            }
        }
        StatementKind::FunctionDeclaration(function) => {
            for statement in &function.body {
                collect_prototype_names_statement(statement, output);
            }
        }
        StatementKind::Return(value) => {
            if let Some(value) = value {
                collect_prototype_names_expression(value, output);
            }
        }
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => {}
    }
}

fn collect_prototype_names_expression(expression: &Expression, output: &mut HashSet<String>) {
    if let ExpressionKind::Call { callee, arguments } = &expression.kind {
        if let ExpressionKind::Member {
            object,
            property: MemberProperty::Static(method),
        } = &callee.kind
        {
            if matches!(&object.kind, ExpressionKind::Global(name) if name == "Object") {
                let candidate = match method.as_str() {
                    "create" => arguments.first(),
                    "setPrototypeOf" => arguments.get(1),
                    _ => None,
                };
                if let Some(Expression {
                    kind: ExpressionKind::Global(name),
                    ..
                }) = candidate
                {
                    output.insert(name.clone());
                }
            }
        }
    }

    match &expression.kind {
        ExpressionKind::Member { object, property } => {
            collect_prototype_names_expression(object, output);
            if let MemberProperty::Computed(value) = property {
                collect_prototype_names_expression(value, output);
            }
        }
        ExpressionKind::Object(entries) => {
            for entry in entries {
                match entry {
                    ObjectEntry::Property(property) => {
                        collect_prototype_names_expression(&property.value, output);
                        if let MemberProperty::Computed(value) = &property.key {
                            collect_prototype_names_expression(value, output);
                        }
                    }
                    ObjectEntry::Spread(value) => collect_prototype_names_expression(value, output),
                    ObjectEntry::Accessor { get, set, .. } => {
                        if let Some(get) = get {
                            collect_prototype_names_expression(get, output);
                        }
                        if let Some(set) = set {
                            collect_prototype_names_expression(set, output);
                        }
                    }
                }
            }
        }
        ExpressionKind::Array(elements) => {
            for element in elements {
                match element {
                    ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                        collect_prototype_names_expression(value, output)
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
            collect_prototype_names_expression(test, output);
            collect_prototype_names_expression(consequent, output);
            collect_prototype_names_expression(alternate, output);
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            collect_prototype_names_expression(argument, output)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            collect_prototype_names_expression(left, output);
            collect_prototype_names_expression(right, output);
        }
        ExpressionKind::Assignment { target, value, .. } => {
            if let AssignmentTarget::Member { object, property } = target {
                collect_prototype_names_expression(object, output);
                if let MemberProperty::Computed(value) = property {
                    collect_prototype_names_expression(value, output);
                }
            }
            collect_prototype_names_expression(value, output);
        }
        ExpressionKind::Update { target, .. } => {
            if let AssignmentTarget::Member { object, property } = target {
                collect_prototype_names_expression(object, output);
                if let MemberProperty::Computed(value) = property {
                    collect_prototype_names_expression(value, output);
                }
            }
        }
        ExpressionKind::Call { callee, arguments } | ExpressionKind::New { callee, arguments } => {
            collect_prototype_names_expression(callee, output);
            for argument in arguments {
                collect_prototype_names_expression(argument, output);
            }
        }
        ExpressionKind::Function(function) => {
            for statement in &function.body {
                collect_prototype_names_statement(statement, output);
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
}

fn validate_no_runtime_graph(statements: &[Statement]) -> Result<()> {
    for statement in statements {
        validate_statement(statement)?;
    }
    Ok(())
}

fn validate_statement(statement: &Statement) -> Result<()> {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            validate_expression(value)
        }
        StatementKind::VariableDeclaration { declarations, .. } => {
            for declaration in declarations {
                if let Some(value) = &declaration.init {
                    validate_expression(value)?;
                }
            }
            Ok(())
        }
        StatementKind::Block(body) => validate_no_runtime_graph(body),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            validate_expression(test)?;
            validate_statement(consequent)?;
            if let Some(alternate) = alternate {
                validate_statement(alternate)?;
            }
            Ok(())
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            validate_expression(test)?;
            validate_statement(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            if let Some(init) = init {
                match init {
                    ForInit::Expression(value) => validate_expression(value)?,
                    ForInit::VariableDeclaration { declarations, .. } => {
                        for declaration in declarations {
                            if let Some(value) = &declaration.init {
                                validate_expression(value)?;
                            }
                        }
                    }
                }
            }
            if let Some(test) = test {
                validate_expression(test)?;
            }
            if let Some(update) = update {
                validate_expression(update)?;
            }
            validate_statement(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            validate_expression(right)?;
            validate_statement(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            validate_expression(discriminant)?;
            for case in cases {
                if let Some(test) = &case.test {
                    validate_expression(test)?;
                }
                validate_no_runtime_graph(&case.consequent)?;
            }
            Ok(())
        }
        StatementKind::Labeled { body, .. } => validate_statement(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            validate_statement(block)?;
            if let Some(handler) = handler {
                validate_statement(&handler.body)?;
            }
            if let Some(finalizer) = finalizer {
                validate_statement(finalizer)?;
            }
            Ok(())
        }
        StatementKind::FunctionDeclaration(function) => validate_no_runtime_graph(&function.body),
        StatementKind::Return(value) => {
            if let Some(value) = value {
                validate_expression(value)?;
            }
            Ok(())
        }
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => Ok(()),
    }
}

fn validate_expression(expression: &Expression) -> Result<()> {
    match &expression.kind {
        ExpressionKind::Function(_) => {
            bail!("residual function value would require closure runtime")
        }
        ExpressionKind::This => {
            bail!("residual `this` would require receiver runtime")
        }
        ExpressionKind::Object(entries) => {
            for entry in entries {
                match entry {
                    ObjectEntry::Accessor { .. } => {
                        bail!("residual accessor would require object runtime")
                    }
                    ObjectEntry::Property(property) => {
                        validate_expression(&property.value)?;
                        if let MemberProperty::Computed(value) = &property.key {
                            validate_expression(value)?;
                        }
                    }
                    ObjectEntry::Spread(value) => validate_expression(value)?,
                }
            }
            Ok(())
        }
        ExpressionKind::Call { callee, arguments } => {
            if is_object_graph_builtin(callee) {
                bail!("residual Object prototype API would require object runtime")
            }
            validate_expression(callee)?;
            for argument in arguments {
                validate_expression(argument)?;
            }
            Ok(())
        }
        ExpressionKind::Member { object, property } => {
            validate_expression(object)?;
            if let MemberProperty::Computed(value) = property {
                validate_expression(value)?;
            }
            Ok(())
        }
        ExpressionKind::Array(elements) => {
            for element in elements {
                match element {
                    ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                        validate_expression(value)?
                    }
                    ArrayElement::Hole => {}
                }
            }
            Ok(())
        }
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            validate_expression(test)?;
            validate_expression(consequent)?;
            validate_expression(alternate)
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            validate_expression(argument)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            validate_expression(left)?;
            validate_expression(right)
        }
        ExpressionKind::Assignment { target, value, .. } => {
            validate_target(target)?;
            validate_expression(value)
        }
        ExpressionKind::Update { target, .. } => validate_target(target),
        ExpressionKind::New { callee, arguments } => {
            validate_expression(callee)?;
            for argument in arguments {
                validate_expression(argument)?;
            }
            Ok(())
        }
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::Global(_) => Ok(()),
    }
}

fn validate_target(target: &AssignmentTarget) -> Result<()> {
    match target {
        AssignmentTarget::Identifier(_) => Ok(()),
        AssignmentTarget::Member { object, property } => {
            validate_expression(object)?;
            if let MemberProperty::Computed(value) = property {
                validate_expression(value)?;
            }
            Ok(())
        }
    }
}
