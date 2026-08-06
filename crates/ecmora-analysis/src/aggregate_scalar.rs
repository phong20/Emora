use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, CatchClause, Expression,
    ExpressionKind, ForInit, Function, ImportSpecifier, MemberProperty, ObjectEntry, Program, Span,
    Statement, StatementKind, SwitchCase, UnaryOperator, VariableDeclarator, VariableKind,
};
use std::collections::{HashMap, HashSet};

type CandidateId = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AggregateKind {
    Object,
    Array,
}

#[derive(Debug, Clone)]
struct Candidate {
    id: CandidateId,
    kind: AggregateKind,
    base_eligible: bool,
    direct_keys: HashSet<String>,
    static_array_len: usize,
    array_present: Vec<bool>,
    array_has_spread: bool,
}

#[derive(Debug, Default)]
struct Registry {
    candidates: Vec<Candidate>,
    by_declaration: HashMap<(u32, String), CandidateId>,
    by_name: HashMap<String, Vec<CandidateId>>,
}

impl Registry {
    fn candidate(&self, id: CandidateId) -> &Candidate {
        &self.candidates[id as usize]
    }

    fn declaration(&self, span: Span, name: &str) -> Option<CandidateId> {
        self.by_declaration
            .get(&(span.start, name.to_owned()))
            .copied()
    }
}

#[derive(Debug, Clone, Default)]
struct AliasFrame {
    aggregates: HashMap<String, CandidateId>,
    shadows: HashSet<String>,
}

#[derive(Debug, Clone)]
struct AliasEnvironment {
    frames: Vec<AliasFrame>,
}

impl Default for AliasEnvironment {
    fn default() -> Self {
        Self {
            frames: vec![AliasFrame::default()],
        }
    }
}

impl AliasEnvironment {
    fn push(&mut self) {
        self.frames.push(AliasFrame::default());
    }

    fn pop(&mut self) {
        self.frames.pop();
    }

    fn lookup(&self, name: &str) -> Option<CandidateId> {
        for frame in self.frames.iter().rev() {
            if frame.shadows.contains(name) {
                return None;
            }
            if let Some(id) = frame.aggregates.get(name) {
                return Some(*id);
            }
        }
        None
    }

    fn declare_alias(&mut self, name: impl Into<String>, id: CandidateId) {
        let name = name.into();
        let frame = self.frames.last_mut().expect("alias frame");
        frame.shadows.remove(&name);
        frame.aggregates.insert(name, id);
    }

    fn declare_nonaggregate(&mut self, name: impl Into<String>) {
        let name = name.into();
        let frame = self.frames.last_mut().expect("alias frame");
        frame.aggregates.remove(&name);
        frame.shadows.insert(name);
    }
}

#[derive(Debug, Clone)]
struct FieldLayout {
    key: String,
    value_name: String,
    present: bool,
}

#[derive(Debug, Clone)]
struct AggregateLayout {
    kind: AggregateKind,
    fields: Vec<FieldLayout>,
    by_key: HashMap<String, usize>,
    length: Option<usize>,
}

impl AggregateLayout {
    fn field(&self, key: &str) -> Option<&FieldLayout> {
        self.by_key.get(key).map(|index| &self.fields[*index])
    }
}

pub(super) fn scalarize(program: &Program) -> Result<Program> {
    let mut registry = Registry::default();
    discover_statements(&program.statements, &mut registry);
    if registry.candidates.is_empty() {
        return Ok(program.clone());
    }

    let mut safety = Safety::new(&registry);
    safety.declare_imports(program);
    safety.scan_statements(&program.statements);
    safety.mark_exports(program);
    let safe = safety.finish();

    if safe.is_empty() {
        return Ok(program.clone());
    }

    let mut transformer = Transformer::new(&registry, safe);
    let mut output = program.clone();
    output.statements = transformer.transform_statements(&program.statements)?;
    Ok(output)
}

fn discover_statements(statements: &[Statement], registry: &mut Registry) {
    for statement in statements {
        discover_statement(statement, registry);
    }
}

fn discover_statement(statement: &Statement, registry: &mut Registry) {
    match &statement.kind {
        StatementKind::VariableDeclaration { declarations, .. } => {
            for declaration in declarations {
                let Some(initializer) = &declaration.init else {
                    continue;
                };
                let Some(kind) = literal_kind(initializer) else {
                    continue;
                };
                let id = registry.candidates.len() as CandidateId;
                let (base_eligible, direct_keys, static_array_len, array_present, array_has_spread) =
                    inspect_literal(initializer);
                registry
                    .by_declaration
                    .insert((declaration.span.start, declaration.name.clone()), id);
                registry
                    .by_name
                    .entry(declaration.name.clone())
                    .or_default()
                    .push(id);
                registry.candidates.push(Candidate {
                    id,
                    kind,
                    base_eligible,
                    direct_keys,
                    static_array_len,
                    array_present,
                    array_has_spread,
                });
            }
        }
        StatementKind::Block(body) => discover_statements(body, registry),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            discover_statement(consequent, registry);
            if let Some(alternate) = alternate {
                discover_statement(alternate, registry);
            }
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Labeled { body, .. } => discover_statement(body, registry),
        StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. } => discover_statement(body, registry),
        StatementKind::Switch { cases, .. } => {
            for case in cases {
                discover_statements(&case.consequent, registry);
            }
        }
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            discover_statement(block, registry);
            if let Some(handler) = handler {
                discover_statement(&handler.body, registry);
            }
            if let Some(finalizer) = finalizer {
                discover_statement(finalizer, registry);
            }
        }
        StatementKind::FunctionDeclaration(function) => {
            discover_statements(&function.body, registry);
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

fn literal_kind(expression: &Expression) -> Option<AggregateKind> {
    match &expression.kind {
        ExpressionKind::Object(_) => Some(AggregateKind::Object),
        ExpressionKind::Array(_) => Some(AggregateKind::Array),
        _ => None,
    }
}

fn inspect_literal(expression: &Expression) -> (bool, HashSet<String>, usize, Vec<bool>, bool) {
    match &expression.kind {
        ExpressionKind::Object(entries) => {
            let mut eligible = true;
            let mut keys = HashSet::new();
            for entry in entries {
                match entry {
                    ObjectEntry::Property(property) => {
                        let Some(key) = static_property_key(&property.key) else {
                            eligible = false;
                            continue;
                        };
                        keys.insert(key);
                        if contains_aggregate_literal(&property.value) {
                            eligible = false;
                        }
                    }
                    ObjectEntry::Spread(value) => {
                        if !matches!(&value.kind, ExpressionKind::Global(_)) {
                            eligible = false;
                        }
                    }
                    ObjectEntry::Accessor { .. } => eligible = false,
                }
            }
            (eligible, keys, 0, Vec::new(), false)
        }
        ExpressionKind::Array(elements) => {
            let mut eligible = true;
            let mut length = 0usize;
            let mut present = Vec::new();
            let mut has_spread = false;
            for element in elements {
                match element {
                    ArrayElement::Expression(value) => {
                        if contains_aggregate_literal(value) {
                            eligible = false;
                        }
                        length += 1;
                        present.push(true);
                    }
                    ArrayElement::Hole => {
                        length += 1;
                        present.push(false);
                    }
                    ArrayElement::Spread(value) => {
                        has_spread = true;
                        if !matches!(&value.kind, ExpressionKind::Global(_)) {
                            eligible = false;
                        }
                    }
                }
            }
            (eligible, HashSet::new(), length, present, has_spread)
        }
        _ => (false, HashSet::new(), 0, Vec::new(), false),
    }
}

fn contains_aggregate_literal(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Object(_) | ExpressionKind::Array(_) => true,
        ExpressionKind::Member { object, property } => {
            contains_aggregate_literal(object)
                || matches!(
                    property,
                    MemberProperty::Computed(value) if contains_aggregate_literal(value)
                )
        }
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            contains_aggregate_literal(test)
                || contains_aggregate_literal(consequent)
                || contains_aggregate_literal(alternate)
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            contains_aggregate_literal(argument)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            contains_aggregate_literal(left) || contains_aggregate_literal(right)
        }
        ExpressionKind::Assignment { target, value, .. } => {
            target_contains_aggregate_literal(target) || contains_aggregate_literal(value)
        }
        ExpressionKind::Update { target, .. } => target_contains_aggregate_literal(target),
        ExpressionKind::Call { callee, arguments } | ExpressionKind::New { callee, arguments } => {
            contains_aggregate_literal(callee) || arguments.iter().any(contains_aggregate_literal)
        }
        ExpressionKind::Function(function) => function
            .body
            .iter()
            .any(statement_contains_aggregate_literal),
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This
        | ExpressionKind::Global(_) => false,
    }
}

fn target_contains_aggregate_literal(target: &AssignmentTarget) -> bool {
    match target {
        AssignmentTarget::Identifier(_) => false,
        AssignmentTarget::Member { object, property } => {
            contains_aggregate_literal(object)
                || matches!(
                    property,
                    MemberProperty::Computed(value) if contains_aggregate_literal(value)
                )
        }
    }
}

fn statement_contains_aggregate_literal(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            contains_aggregate_literal(value)
        }
        StatementKind::VariableDeclaration { declarations, .. } => declarations
            .iter()
            .filter_map(|declaration| declaration.init.as_ref())
            .any(contains_aggregate_literal),
        StatementKind::Block(body) => body.iter().any(statement_contains_aggregate_literal),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            contains_aggregate_literal(test)
                || statement_contains_aggregate_literal(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(statement_contains_aggregate_literal)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            contains_aggregate_literal(test) || statement_contains_aggregate_literal(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => contains_aggregate_literal(value),
                ForInit::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .filter_map(|declaration| declaration.init.as_ref())
                    .any(contains_aggregate_literal),
            }) || test.as_ref().is_some_and(contains_aggregate_literal)
                || update.as_ref().is_some_and(contains_aggregate_literal)
                || statement_contains_aggregate_literal(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            contains_aggregate_literal(right) || statement_contains_aggregate_literal(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            contains_aggregate_literal(discriminant)
                || cases.iter().any(|case| {
                    case.test.as_ref().is_some_and(contains_aggregate_literal)
                        || case
                            .consequent
                            .iter()
                            .any(statement_contains_aggregate_literal)
                })
        }
        StatementKind::Labeled { body, .. } => statement_contains_aggregate_literal(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_contains_aggregate_literal(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| statement_contains_aggregate_literal(&handler.body))
                || finalizer
                    .as_deref()
                    .is_some_and(statement_contains_aggregate_literal)
        }
        StatementKind::FunctionDeclaration(function) => function
            .body
            .iter()
            .any(statement_contains_aggregate_literal),
        StatementKind::Return(value) => value.as_ref().is_some_and(contains_aggregate_literal),
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

struct Safety<'a> {
    registry: &'a Registry,
    environment: AliasEnvironment,
    unsafe_ids: HashSet<CandidateId>,
    dependencies: HashMap<CandidateId, HashSet<CandidateId>>,
}

impl<'a> Safety<'a> {
    fn new(registry: &'a Registry) -> Self {
        let unsafe_ids = registry
            .candidates
            .iter()
            .filter(|candidate| !candidate.base_eligible)
            .map(|candidate| candidate.id)
            .collect();
        Self {
            registry,
            environment: AliasEnvironment::default(),
            unsafe_ids,
            dependencies: HashMap::new(),
        }
    }

    fn declare_imports(&mut self, program: &Program) {
        for declaration in &program.imports {
            for specifier in &declaration.specifiers {
                let local = match specifier {
                    ImportSpecifier::Named { local, .. }
                    | ImportSpecifier::Default { local }
                    | ImportSpecifier::Namespace { local } => local,
                };
                self.environment.declare_nonaggregate(local.clone());
            }
        }
    }

    fn mark_exports(&mut self, program: &Program) {
        for export in &program.exports {
            if let Some(id) = self.environment.lookup(&export.local) {
                self.mark_unsafe(id);
            }
        }
    }

    fn finish(mut self) -> HashSet<CandidateId> {
        loop {
            let mut changed = false;
            for candidate in &self.registry.candidates {
                if self.unsafe_ids.contains(&candidate.id) {
                    continue;
                }
                if self
                    .dependencies
                    .get(&candidate.id)
                    .is_some_and(|dependencies| {
                        dependencies
                            .iter()
                            .any(|dependency| self.unsafe_ids.contains(dependency))
                    })
                {
                    self.unsafe_ids.insert(candidate.id);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        self.registry
            .candidates
            .iter()
            .map(|candidate| candidate.id)
            .filter(|id| !self.unsafe_ids.contains(id))
            .collect()
    }

    fn mark_unsafe(&mut self, id: CandidateId) {
        self.unsafe_ids.insert(id);
    }

    fn root(&self, expression: &Expression) -> Option<CandidateId> {
        let ExpressionKind::Global(name) = &expression.kind else {
            return None;
        };
        self.environment.lookup(name)
    }

    fn mark_unbound_candidate_name(&mut self, name: &str) {
        if let Some(ids) = self.registry.by_name.get(name) {
            for id in ids {
                self.unsafe_ids.insert(*id);
            }
        }
    }

    fn add_dependency(&mut self, owner: CandidateId, dependency: CandidateId) {
        self.dependencies
            .entry(owner)
            .or_default()
            .insert(dependency);
    }

    fn scan_statements(&mut self, statements: &[Statement]) {
        for statement in statements {
            self.scan_statement(statement);
        }
    }

    fn scan_statement(&mut self, statement: &Statement) {
        match &statement.kind {
            StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::Break(_)
            | StatementKind::Continue(_) => {}
            StatementKind::Expression(value) | StatementKind::Throw(value) => {
                self.scan_expression(value);
            }
            StatementKind::VariableDeclaration { declarations, .. } => {
                self.scan_declarations(declarations);
            }
            StatementKind::Block(body) => {
                self.environment.push();
                self.scan_statements(body);
                self.environment.pop();
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                self.scan_condition(test);
                self.environment.push();
                self.scan_statement(consequent);
                self.environment.pop();
                if let Some(alternate) = alternate {
                    self.environment.push();
                    self.scan_statement(alternate);
                    self.environment.pop();
                }
            }
            StatementKind::While { test, body } => {
                self.scan_condition(test);
                self.environment.push();
                self.scan_statement(body);
                self.environment.pop();
            }
            StatementKind::DoWhile { body, test } => {
                self.environment.push();
                self.scan_statement(body);
                self.environment.pop();
                self.scan_condition(test);
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                self.environment.push();
                if let Some(init) = init {
                    self.scan_for_init(init);
                }
                if let Some(test) = test {
                    self.scan_condition(test);
                }
                if let Some(update) = update {
                    self.scan_expression(update);
                }
                self.scan_statement(body);
                self.environment.pop();
            }
            StatementKind::ForIn {
                name, right, body, ..
            }
            | StatementKind::ForOf {
                name, right, body, ..
            } => {
                self.scan_expression(right);
                self.environment.push();
                self.environment.declare_nonaggregate(name.clone());
                self.scan_statement(body);
                self.environment.pop();
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                self.scan_expression(discriminant);
                self.environment.push();
                for case in cases {
                    if let Some(test) = &case.test {
                        self.scan_expression(test);
                    }
                    self.scan_statements(&case.consequent);
                }
                self.environment.pop();
            }
            StatementKind::Labeled { body, .. } => self.scan_statement(body),
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                self.environment.push();
                self.scan_statement(block);
                self.environment.pop();
                if let Some(handler) = handler {
                    self.environment.push();
                    if let Some(parameter) = &handler.parameter {
                        self.environment.declare_nonaggregate(parameter.clone());
                    }
                    self.scan_statement(&handler.body);
                    self.environment.pop();
                }
                if let Some(finalizer) = finalizer {
                    self.environment.push();
                    self.scan_statement(finalizer);
                    self.environment.pop();
                }
            }
            StatementKind::FunctionDeclaration(function) => {
                if let Some(name) = &function.name {
                    self.environment.declare_nonaggregate(name.clone());
                }
                self.scan_function(function);
            }
            StatementKind::Return(value) => {
                if let Some(value) = value {
                    self.scan_expression(value);
                }
            }
        }
    }

    fn scan_function(&mut self, function: &Function) {
        self.environment.push();
        if let Some(name) = &function.name {
            self.environment.declare_nonaggregate(name.clone());
        }
        for parameter in &function.parameters {
            let parameter = parameter.strip_prefix("@rest:").unwrap_or(parameter);
            self.environment.declare_nonaggregate(parameter.to_owned());
        }
        self.scan_statements(&function.body);
        self.environment.pop();
    }

    fn scan_for_init(&mut self, init: &ForInit) {
        match init {
            ForInit::Expression(value) => self.scan_expression(value),
            ForInit::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    if let Some(value) = &declaration.init {
                        self.scan_expression(value);
                    }
                    self.environment
                        .declare_nonaggregate(declaration.name.clone());
                }
            }
        }
    }

    fn scan_declarations(&mut self, declarations: &[VariableDeclarator]) {
        for declaration in declarations {
            if let Some(id) = self
                .registry
                .declaration(declaration.span, &declaration.name)
            {
                if let Some(initializer) = &declaration.init {
                    self.scan_candidate_initializer(id, initializer);
                }
                self.environment.declare_alias(declaration.name.clone(), id);
                continue;
            }

            if let Some(initializer) = &declaration.init {
                if let Some(id) = self.root(initializer) {
                    self.environment.declare_alias(declaration.name.clone(), id);
                    continue;
                }
                self.scan_expression(initializer);
            }
            self.environment
                .declare_nonaggregate(declaration.name.clone());
        }
    }

    fn scan_candidate_initializer(&mut self, owner: CandidateId, expression: &Expression) {
        match &expression.kind {
            ExpressionKind::Object(entries) => {
                for entry in entries {
                    match entry {
                        ObjectEntry::Property(property) => {
                            if let MemberProperty::Computed(value) = &property.key {
                                if static_property_key(&property.key).is_none() {
                                    self.mark_unsafe(owner);
                                    self.scan_expression(value);
                                }
                            }
                            self.scan_expression(&property.value);
                        }
                        ObjectEntry::Spread(value) => {
                            if let Some(dependency) = self.root(value) {
                                self.add_dependency(owner, dependency);
                            } else {
                                self.mark_unsafe(owner);
                                self.scan_expression(value);
                            }
                        }
                        ObjectEntry::Accessor { .. } => self.mark_unsafe(owner),
                    }
                }
            }
            ExpressionKind::Array(elements) => {
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) => self.scan_expression(value),
                        ArrayElement::Spread(value) => {
                            if let Some(dependency) = self.root(value) {
                                if self.registry.candidate(dependency).kind != AggregateKind::Array
                                {
                                    self.mark_unsafe(owner);
                                } else {
                                    self.add_dependency(owner, dependency);
                                }
                            } else {
                                self.mark_unsafe(owner);
                                self.scan_expression(value);
                            }
                        }
                        ArrayElement::Hole => {}
                    }
                }
            }
            _ => self.mark_unsafe(owner),
        }
    }

    fn scan_condition(&mut self, expression: &Expression) {
        if self.root(expression).is_none() {
            self.scan_expression(expression);
        }
    }

    fn scan_expression(&mut self, expression: &Expression) {
        match &expression.kind {
            ExpressionKind::Global(name) => {
                if let Some(id) = self.root(expression) {
                    self.mark_unsafe(id);
                } else {
                    self.mark_unbound_candidate_name(name);
                }
            }
            ExpressionKind::Member { object, property } => {
                if let Some(id) = self.root(object) {
                    let Some(key) = static_property_key(property) else {
                        self.mark_unsafe(id);
                        if let MemberProperty::Computed(value) = property {
                            self.scan_expression(value);
                        }
                        return;
                    };
                    if !self.read_is_static(id, &key) {
                        self.mark_unsafe(id);
                    }
                } else {
                    self.scan_expression(object);
                    if let MemberProperty::Computed(value) = property {
                        self.scan_expression(value);
                    }
                }
            }
            ExpressionKind::Object(entries) => {
                for entry in entries {
                    match entry {
                        ObjectEntry::Property(property) => {
                            if let MemberProperty::Computed(value) = &property.key {
                                self.scan_expression(value);
                            }
                            self.scan_expression(&property.value);
                        }
                        ObjectEntry::Spread(value) => {
                            if let Some(id) = self.root(value) {
                                self.mark_unsafe(id);
                            } else {
                                self.scan_expression(value);
                            }
                        }
                        ObjectEntry::Accessor { get, set, .. } => {
                            if let Some(getter) = get {
                                self.scan_expression(getter);
                            }
                            if let Some(setter) = set {
                                self.scan_expression(setter);
                            }
                        }
                    }
                }
            }
            ExpressionKind::Array(elements) => {
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) => self.scan_expression(value),
                        ArrayElement::Spread(value) => {
                            if let Some(id) = self.root(value) {
                                self.mark_unsafe(id);
                            } else {
                                self.scan_expression(value);
                            }
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
                self.scan_condition(test);
                self.scan_expression(consequent);
                self.scan_expression(alternate);
            }
            ExpressionKind::Unary { operator, argument } => match operator {
                UnaryOperator::Typeof | UnaryOperator::Not | UnaryOperator::Void
                    if self.root(argument).is_some() => {}
                UnaryOperator::Delete => {
                    if let ExpressionKind::Member { object, property } = &argument.kind {
                        if let Some(id) = self.root(object) {
                            self.mark_unsafe(id);
                            if let MemberProperty::Computed(value) = property {
                                self.scan_expression(value);
                            }
                            return;
                        }
                    }
                    self.scan_expression(argument);
                }
                _ => self.scan_expression(argument),
            },
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => {
                if matches!(
                    operator,
                    BinaryOperator::Equal
                        | BinaryOperator::NotEqual
                        | BinaryOperator::StrictEqual
                        | BinaryOperator::StrictNotEqual
                ) {
                    self.scan_equality(left, right);
                } else if *operator == BinaryOperator::In {
                    if let Some(id) = self.root(right) {
                        if let Some(key) = static_expression_key(left) {
                            if !self.read_is_static(id, &key) {
                                self.mark_unsafe(id);
                            }
                        } else {
                            self.mark_unsafe(id);
                            self.scan_expression(left);
                        }
                    } else {
                        self.scan_expression(left);
                        self.scan_expression(right);
                    }
                } else {
                    self.scan_expression(left);
                    self.scan_expression(right);
                }
            }
            ExpressionKind::Logical { left, right, .. } => {
                self.scan_expression(left);
                self.scan_expression(right);
            }
            ExpressionKind::Assignment { target, value, .. } => {
                self.scan_assignment_target(target, true);
                self.scan_expression(value);
            }
            ExpressionKind::Update { target, .. } => {
                self.scan_assignment_target(target, true);
            }
            ExpressionKind::Call { callee, arguments } => {
                if let ExpressionKind::Member { object, property } = &callee.kind {
                    if let Some(id) = self.root(object) {
                        self.mark_unsafe(id);
                        if let MemberProperty::Computed(value) = property {
                            self.scan_expression(value);
                        }
                    } else {
                        self.scan_expression(callee);
                    }
                } else {
                    self.scan_expression(callee);
                }
                for argument in arguments {
                    if let Some(source) = spread_source(argument) {
                        if let Some(id) = self.root(source) {
                            if self.registry.candidate(id).kind != AggregateKind::Array {
                                self.mark_unsafe(id);
                            }
                            continue;
                        }
                    }
                    self.scan_expression(argument);
                }
            }
            ExpressionKind::New { callee, arguments } => {
                self.scan_expression(callee);
                for argument in arguments {
                    if let Some(source) = spread_source(argument) {
                        if let Some(id) = self.root(source) {
                            if self.registry.candidate(id).kind != AggregateKind::Array {
                                self.mark_unsafe(id);
                            }
                            continue;
                        }
                    }
                    self.scan_expression(argument);
                }
            }
            ExpressionKind::Function(function) => self.scan_function(function),
            ExpressionKind::Await(value) => self.scan_expression(value),
            ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This => {}
        }
    }

    fn scan_equality(&mut self, left: &Expression, right: &Expression) {
        let left_root = self.root(left);
        let right_root = self.root(right);
        match (left_root, right_root) {
            (Some(_), Some(_)) => {}
            (Some(id), None) => {
                if !is_nullish_literal(right) {
                    self.mark_unsafe(id);
                    self.scan_expression(right);
                }
            }
            (None, Some(id)) => {
                if !is_nullish_literal(left) {
                    self.mark_unsafe(id);
                    self.scan_expression(left);
                }
            }
            (None, None) => {
                self.scan_expression(left);
                self.scan_expression(right);
            }
        }
    }

    fn scan_assignment_target(&mut self, target: &AssignmentTarget, write: bool) {
        match target {
            AssignmentTarget::Identifier(name) => {
                if let Some(id) = self.environment.lookup(name) {
                    self.mark_unsafe(id);
                } else {
                    self.mark_unbound_candidate_name(name);
                }
            }
            AssignmentTarget::Member { object, property } => {
                if let Some(id) = self.root(object) {
                    let Some(key) = static_property_key(property) else {
                        self.mark_unsafe(id);
                        if let MemberProperty::Computed(value) = property {
                            self.scan_expression(value);
                        }
                        return;
                    };
                    if write && !self.write_is_static(id, &key) {
                        self.mark_unsafe(id);
                    }
                } else {
                    self.scan_expression(object);
                    if let MemberProperty::Computed(value) = property {
                        self.scan_expression(value);
                    }
                }
            }
        }
    }

    fn read_is_static(&self, id: CandidateId, key: &str) -> bool {
        let candidate = self.registry.candidate(id);
        match candidate.kind {
            AggregateKind::Object => candidate.direct_keys.contains(key),
            AggregateKind::Array => {
                if key == "length" {
                    return true;
                }
                if candidate.array_has_spread {
                    return false;
                }
                key.parse::<usize>()
                    .is_ok_and(|index| index < candidate.static_array_len)
            }
        }
    }

    fn write_is_static(&self, id: CandidateId, key: &str) -> bool {
        let candidate = self.registry.candidate(id);
        match candidate.kind {
            AggregateKind::Object => candidate.direct_keys.contains(key),
            AggregateKind::Array => {
                if key == "length" || candidate.array_has_spread {
                    return false;
                }
                key.parse::<usize>().is_ok_and(|index| {
                    index < candidate.static_array_len
                        && candidate.array_present.get(index).copied().unwrap_or(false)
                })
            }
        }
    }
}

struct Transformer<'a> {
    registry: &'a Registry,
    safe: HashSet<CandidateId>,
    environment: AliasEnvironment,
    layouts: HashMap<CandidateId, AggregateLayout>,
}

impl<'a> Transformer<'a> {
    fn new(registry: &'a Registry, safe: HashSet<CandidateId>) -> Self {
        Self {
            registry,
            safe,
            environment: AliasEnvironment::default(),
            layouts: HashMap::new(),
        }
    }

    fn root(&self, expression: &Expression) -> Option<CandidateId> {
        let ExpressionKind::Global(name) = &expression.kind else {
            return None;
        };
        self.environment.lookup(name)
    }

    fn transform_statements(&mut self, statements: &[Statement]) -> Result<Vec<Statement>> {
        let mut output = Vec::new();
        for statement in statements {
            output.extend(self.transform_statement(statement)?);
        }
        Ok(output)
    }

    fn transform_statement(&mut self, statement: &Statement) -> Result<Vec<Statement>> {
        let one = |kind| {
            vec![Statement {
                kind,
                span: statement.span,
            }]
        };
        Ok(match &statement.kind {
            StatementKind::Empty => one(StatementKind::Empty),
            StatementKind::Debugger => one(StatementKind::Debugger),
            StatementKind::Expression(value) => {
                one(StatementKind::Expression(self.transform_expression(value)?))
            }
            StatementKind::VariableDeclaration { kind, declarations } => {
                self.transform_declarations(*kind, declarations, statement.span)?
            }
            StatementKind::Block(body) => {
                self.environment.push();
                let body = self.transform_statements(body)?;
                self.environment.pop();
                one(StatementKind::Block(body))
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                let test = self.transform_condition(test)?;
                self.environment.push();
                let consequent = self.transform_as_single(consequent)?;
                self.environment.pop();
                let alternate = if let Some(alternate) = alternate {
                    self.environment.push();
                    let alternate = self.transform_as_single(alternate)?;
                    self.environment.pop();
                    Some(Box::new(alternate))
                } else {
                    None
                };
                one(StatementKind::If {
                    test,
                    consequent: Box::new(consequent),
                    alternate,
                })
            }
            StatementKind::While { test, body } => {
                let test = self.transform_condition(test)?;
                self.environment.push();
                let body = self.transform_as_single(body)?;
                self.environment.pop();
                one(StatementKind::While {
                    test,
                    body: Box::new(body),
                })
            }
            StatementKind::DoWhile { body, test } => {
                self.environment.push();
                let body = self.transform_as_single(body)?;
                self.environment.pop();
                let test = self.transform_condition(test)?;
                one(StatementKind::DoWhile {
                    body: Box::new(body),
                    test,
                })
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                self.environment.push();
                let init = init
                    .as_ref()
                    .map(|init| self.transform_for_init(init))
                    .transpose()?;
                let test = test
                    .as_ref()
                    .map(|test| self.transform_condition(test))
                    .transpose()?;
                let update = update
                    .as_ref()
                    .map(|update| self.transform_expression(update))
                    .transpose()?;
                let body = self.transform_as_single(body)?;
                self.environment.pop();
                one(StatementKind::For {
                    init,
                    test,
                    update,
                    body: Box::new(body),
                })
            }
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => {
                let right = self.transform_expression(right)?;
                self.environment.push();
                self.environment.declare_nonaggregate(name.clone());
                let body = self.transform_as_single(body)?;
                self.environment.pop();
                one(StatementKind::ForIn {
                    name: name.clone(),
                    kind: *kind,
                    right,
                    body: Box::new(body),
                })
            }
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => {
                let right = self.transform_expression(right)?;
                self.environment.push();
                self.environment.declare_nonaggregate(name.clone());
                let body = self.transform_as_single(body)?;
                self.environment.pop();
                one(StatementKind::ForOf {
                    name: name.clone(),
                    kind: *kind,
                    right,
                    body: Box::new(body),
                })
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                let discriminant = self.transform_expression(discriminant)?;
                self.environment.push();
                let mut transformed_cases = Vec::with_capacity(cases.len());
                for case in cases {
                    transformed_cases.push(SwitchCase {
                        test: case
                            .test
                            .as_ref()
                            .map(|test| self.transform_expression(test))
                            .transpose()?,
                        consequent: self.transform_statements(&case.consequent)?,
                        span: case.span,
                    });
                }
                self.environment.pop();
                one(StatementKind::Switch {
                    discriminant,
                    cases: transformed_cases,
                })
            }
            StatementKind::Labeled { label, body } => {
                let body = self.transform_as_single(body)?;
                one(StatementKind::Labeled {
                    label: label.clone(),
                    body: Box::new(body),
                })
            }
            StatementKind::Try {
                block,
                handler,
                finalizer,
            } => {
                self.environment.push();
                let block = self.transform_as_single(block)?;
                self.environment.pop();
                let handler = if let Some(handler) = handler {
                    self.environment.push();
                    if let Some(parameter) = &handler.parameter {
                        self.environment.declare_nonaggregate(parameter.clone());
                    }
                    let body = self.transform_as_single(&handler.body)?;
                    self.environment.pop();
                    Some(CatchClause {
                        parameter: handler.parameter.clone(),
                        body: Box::new(body),
                        span: handler.span,
                    })
                } else {
                    None
                };
                let finalizer = if let Some(finalizer) = finalizer {
                    self.environment.push();
                    let finalizer = self.transform_as_single(finalizer)?;
                    self.environment.pop();
                    Some(Box::new(finalizer))
                } else {
                    None
                };
                one(StatementKind::Try {
                    block: Box::new(block),
                    handler,
                    finalizer,
                })
            }
            StatementKind::FunctionDeclaration(function) => {
                if let Some(name) = &function.name {
                    self.environment.declare_nonaggregate(name.clone());
                }
                one(StatementKind::FunctionDeclaration(
                    self.transform_function(function)?,
                ))
            }
            StatementKind::Return(value) => one(StatementKind::Return(
                value
                    .as_ref()
                    .map(|value| self.transform_expression(value))
                    .transpose()?,
            )),
            StatementKind::Throw(value) => {
                one(StatementKind::Throw(self.transform_expression(value)?))
            }
            StatementKind::Break(label) => one(StatementKind::Break(label.clone())),
            StatementKind::Continue(label) => one(StatementKind::Continue(label.clone())),
        })
    }

    fn transform_as_single(&mut self, statement: &Statement) -> Result<Statement> {
        let mut transformed = self.transform_statement(statement)?;
        if transformed.len() == 1 {
            return Ok(transformed.remove(0));
        }
        Ok(Statement {
            kind: StatementKind::Block(transformed),
            span: statement.span,
        })
    }

    fn transform_for_init(&mut self, init: &ForInit) -> Result<ForInit> {
        Ok(match init {
            ForInit::Expression(value) => ForInit::Expression(self.transform_expression(value)?),
            ForInit::VariableDeclaration { kind, declarations } => {
                let mut transformed = Vec::with_capacity(declarations.len());
                for declaration in declarations {
                    let init = declaration
                        .init
                        .as_ref()
                        .map(|value| self.transform_expression(value))
                        .transpose()?;
                    self.environment
                        .declare_nonaggregate(declaration.name.clone());
                    transformed.push(VariableDeclarator {
                        name: declaration.name.clone(),
                        init,
                        span: declaration.span,
                    });
                }
                ForInit::VariableDeclaration {
                    kind: *kind,
                    declarations: transformed,
                }
            }
        })
    }

    fn transform_declarations(
        &mut self,
        kind: VariableKind,
        declarations: &[VariableDeclarator],
        statement_span: Span,
    ) -> Result<Vec<Statement>> {
        let mut output = Vec::new();
        let mut ordinary = Vec::new();

        let flush_ordinary = |output: &mut Vec<Statement>,
                              ordinary: &mut Vec<VariableDeclarator>| {
            if ordinary.is_empty() {
                return;
            }
            output.push(Statement {
                kind: StatementKind::VariableDeclaration {
                    kind,
                    declarations: std::mem::take(ordinary),
                },
                span: statement_span,
            });
        };

        for declaration in declarations {
            if let Some(id) = self
                .registry
                .declaration(declaration.span, &declaration.name)
                .filter(|id| self.safe.contains(id))
            {
                flush_ordinary(&mut output, &mut ordinary);
                let initializer = declaration
                    .init
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("aggregate candidate thiếu initializer"))?;
                let (statements, layout) =
                    self.materialize_candidate(id, initializer, declaration.span)?;
                output.extend(statements);
                self.layouts.insert(id, layout);
                self.environment.declare_alias(declaration.name.clone(), id);
                continue;
            }

            if let Some(initializer) = &declaration.init {
                if let Some(id) = self.root(initializer).filter(|id| self.safe.contains(id)) {
                    flush_ordinary(&mut output, &mut ordinary);
                    self.environment.declare_alias(declaration.name.clone(), id);
                    continue;
                }
            }

            let init = declaration
                .init
                .as_ref()
                .map(|value| self.transform_expression(value))
                .transpose()?;
            self.environment
                .declare_nonaggregate(declaration.name.clone());
            ordinary.push(VariableDeclarator {
                name: declaration.name.clone(),
                init,
                span: declaration.span,
            });
        }

        flush_ordinary(&mut output, &mut ordinary);
        Ok(output)
    }

    fn materialize_candidate(
        &mut self,
        id: CandidateId,
        initializer: &Expression,
        span: Span,
    ) -> Result<(Vec<Statement>, AggregateLayout)> {
        match &initializer.kind {
            ExpressionKind::Object(entries) => self.materialize_object(id, entries, span),
            ExpressionKind::Array(elements) => self.materialize_array(id, elements, span),
            _ => bail!("aggregate candidate không còn là object/array literal"),
        }
    }

    fn materialize_object(
        &mut self,
        id: CandidateId,
        entries: &[ObjectEntry],
        _span: Span,
    ) -> Result<(Vec<Statement>, AggregateLayout)> {
        let mut output = Vec::new();
        let mut fields = Vec::<FieldLayout>::new();
        let mut by_key = HashMap::<String, usize>::new();

        for entry in entries {
            match entry {
                ObjectEntry::Property(property) => {
                    let key = static_property_key(&property.key)
                        .ok_or_else(|| anyhow::anyhow!("static aggregate key became dynamic"))?;
                    let value = self.transform_expression(&property.value)?;
                    self.emit_object_field(
                        id,
                        key,
                        value,
                        property.value.span,
                        &mut output,
                        &mut fields,
                        &mut by_key,
                    );
                }
                ObjectEntry::Spread(source) => {
                    let source_id = self
                        .root(source)
                        .filter(|source_id| self.safe.contains(source_id))
                        .ok_or_else(|| anyhow::anyhow!("object spread source không scalarized"))?;
                    let source_layout =
                        self.layouts.get(&source_id).cloned().ok_or_else(|| {
                            anyhow::anyhow!("object spread source chưa materialize")
                        })?;
                    for field in source_layout.fields {
                        if !field.present {
                            continue;
                        }
                        self.emit_object_field(
                            id,
                            field.key.clone(),
                            global_expression(field.value_name, source.span),
                            source.span,
                            &mut output,
                            &mut fields,
                            &mut by_key,
                        );
                    }
                }
                ObjectEntry::Accessor { .. } => {
                    bail!("accessor không được đưa vào scalar aggregate")
                }
            }
        }

        Ok((
            output,
            AggregateLayout {
                kind: AggregateKind::Object,
                fields,
                by_key,
                length: None,
            },
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_object_field(
        &mut self,
        id: CandidateId,
        key: String,
        value: Expression,
        span: Span,
        output: &mut Vec<Statement>,
        fields: &mut Vec<FieldLayout>,
        by_key: &mut HashMap<String, usize>,
    ) {
        if let Some(index) = by_key.get(&key).copied() {
            let target = fields[index].value_name.clone();
            output.push(assignment_statement(target, value, span));
            fields[index].present = true;
            return;
        }

        let index = fields.len();
        let value_name = synthetic_field_name(id, index, &key);
        by_key.insert(key.clone(), index);
        fields.push(FieldLayout {
            key,
            value_name: value_name.clone(),
            present: true,
        });
        output.push(variable_statement(value_name, value, span));
    }

    fn materialize_array(
        &mut self,
        id: CandidateId,
        elements: &[ArrayElement],
        span: Span,
    ) -> Result<(Vec<Statement>, AggregateLayout)> {
        let mut output = Vec::new();
        let mut fields = Vec::<FieldLayout>::new();
        let mut by_key = HashMap::<String, usize>::new();

        for element in elements {
            match element {
                ArrayElement::Expression(value) => {
                    let transformed = self.transform_expression(value)?;
                    let value_span = transformed.span;
                    self.push_array_field(
                        id,
                        transformed,
                        true,
                        value_span,
                        &mut output,
                        &mut fields,
                        &mut by_key,
                    );
                }
                ArrayElement::Hole => {
                    self.push_array_field(
                        id,
                        undefined_expression(span),
                        false,
                        span,
                        &mut output,
                        &mut fields,
                        &mut by_key,
                    );
                }
                ArrayElement::Spread(source) => {
                    let source_id = self
                        .root(source)
                        .filter(|source_id| self.safe.contains(source_id))
                        .ok_or_else(|| anyhow::anyhow!("array spread source không scalarized"))?;
                    let source_layout =
                        self.layouts.get(&source_id).cloned().ok_or_else(|| {
                            anyhow::anyhow!("array spread source chưa materialize")
                        })?;
                    if source_layout.kind != AggregateKind::Array {
                        bail!("array spread source không phải scalar array")
                    }
                    for field in source_layout.fields {
                        self.push_array_field(
                            id,
                            global_expression(field.value_name, source.span),
                            true,
                            source.span,
                            &mut output,
                            &mut fields,
                            &mut by_key,
                        );
                    }
                }
            }
        }

        Ok((
            output,
            AggregateLayout {
                kind: AggregateKind::Array,
                length: Some(fields.len()),
                fields,
                by_key,
            },
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn push_array_field(
        &mut self,
        id: CandidateId,
        value: Expression,
        present: bool,
        span: Span,
        output: &mut Vec<Statement>,
        fields: &mut Vec<FieldLayout>,
        by_key: &mut HashMap<String, usize>,
    ) {
        let index = fields.len();
        let key = index.to_string();
        let value_name = synthetic_field_name(id, index, &key);
        by_key.insert(key.clone(), index);
        fields.push(FieldLayout {
            key,
            value_name: value_name.clone(),
            present,
        });
        output.push(variable_statement(value_name, value, span));
    }

    fn transform_function(&mut self, function: &Function) -> Result<Function> {
        self.environment.push();
        if let Some(name) = &function.name {
            self.environment.declare_nonaggregate(name.clone());
        }
        for parameter in &function.parameters {
            let name = parameter.strip_prefix("@rest:").unwrap_or(parameter);
            self.environment.declare_nonaggregate(name.to_owned());
        }
        let body = self.transform_statements(&function.body)?;
        self.environment.pop();

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

    fn transform_condition(&mut self, expression: &Expression) -> Result<Expression> {
        if self.root(expression).is_some() {
            return Ok(bool_expression(true, expression.span));
        }
        self.transform_expression(expression)
    }

    fn transform_expression(&mut self, expression: &Expression) -> Result<Expression> {
        let span = expression.span;
        Ok(match &expression.kind {
            ExpressionKind::Global(name) => {
                if let Some(id) = self.environment.lookup(name) {
                    bail!(
                        "aggregate `{}` (candidate #{}) escaped scalar SSA path",
                        name,
                        id
                    )
                }
                expression.clone()
            }
            ExpressionKind::Member { object, property } => {
                if let Some(id) = self.root(object) {
                    self.transform_member_read(id, property, span)?
                } else {
                    Expression {
                        kind: ExpressionKind::Member {
                            object: Box::new(self.transform_expression(object)?),
                            property: self.transform_property(property)?,
                        },
                        span,
                    }
                }
            }
            ExpressionKind::Object(entries) => Expression {
                kind: ExpressionKind::Object(
                    entries
                        .iter()
                        .map(|entry| self.transform_object_entry(entry))
                        .collect::<Result<Vec<_>>>()?,
                ),
                span,
            },
            ExpressionKind::Array(elements) => Expression {
                kind: ExpressionKind::Array(
                    elements
                        .iter()
                        .map(|element| self.transform_array_element(element))
                        .collect::<Result<Vec<_>>>()?,
                ),
                span,
            },
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => Expression {
                kind: ExpressionKind::Conditional {
                    test: Box::new(self.transform_condition(test)?),
                    consequent: Box::new(self.transform_expression(consequent)?),
                    alternate: Box::new(self.transform_expression(alternate)?),
                },
                span,
            },
            ExpressionKind::Unary { operator, argument } => {
                if let Some(_) = self.root(argument) {
                    match operator {
                        UnaryOperator::Typeof => string_expression("object", span),
                        UnaryOperator::Not => bool_expression(false, span),
                        UnaryOperator::Void => undefined_expression(span),
                        _ => bail!("aggregate unary coercion escaped scalar SSA path"),
                    }
                } else {
                    Expression {
                        kind: ExpressionKind::Unary {
                            operator: *operator,
                            argument: Box::new(self.transform_expression(argument)?),
                        },
                        span,
                    }
                }
            }
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => {
                if matches!(
                    operator,
                    BinaryOperator::Equal
                        | BinaryOperator::NotEqual
                        | BinaryOperator::StrictEqual
                        | BinaryOperator::StrictNotEqual
                ) && (self.root(left).is_some() || self.root(right).is_some())
                {
                    self.transform_equality(left, *operator, right, span)?
                } else if *operator == BinaryOperator::In {
                    if let Some(id) = self.root(right) {
                        let key = static_expression_key(left).ok_or_else(|| {
                            anyhow::anyhow!("dynamic `in` key escaped aggregate SSA")
                        })?;
                        let present = self.layouts.get(&id).is_some_and(|layout| {
                            (layout.kind == AggregateKind::Array && key == "length")
                                || layout.field(&key).is_some_and(|field| field.present)
                        });
                        bool_expression(present, span)
                    } else {
                        Expression {
                            kind: ExpressionKind::Binary {
                                left: Box::new(self.transform_expression(left)?),
                                operator: *operator,
                                right: Box::new(self.transform_expression(right)?),
                            },
                            span,
                        }
                    }
                } else {
                    Expression {
                        kind: ExpressionKind::Binary {
                            left: Box::new(self.transform_expression(left)?),
                            operator: *operator,
                            right: Box::new(self.transform_expression(right)?),
                        },
                        span,
                    }
                }
            }
            ExpressionKind::Logical {
                left,
                operator,
                right,
            } => Expression {
                kind: ExpressionKind::Logical {
                    left: Box::new(self.transform_expression(left)?),
                    operator: *operator,
                    right: Box::new(self.transform_expression(right)?),
                },
                span,
            },
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => Expression {
                kind: ExpressionKind::Assignment {
                    target: self.transform_assignment_target(target)?,
                    operator: *operator,
                    value: Box::new(self.transform_expression(value)?),
                },
                span,
            },
            ExpressionKind::Update {
                target,
                operator,
                prefix,
            } => Expression {
                kind: ExpressionKind::Update {
                    target: self.transform_assignment_target(target)?,
                    operator: *operator,
                    prefix: *prefix,
                },
                span,
            },
            ExpressionKind::Call { callee, arguments } => Expression {
                kind: ExpressionKind::Call {
                    callee: Box::new(self.transform_expression(callee)?),
                    arguments: self.transform_call_arguments(arguments)?,
                },
                span,
            },
            ExpressionKind::New { callee, arguments } => Expression {
                kind: ExpressionKind::New {
                    callee: Box::new(self.transform_expression(callee)?),
                    arguments: self.transform_call_arguments(arguments)?,
                },
                span,
            },
            ExpressionKind::Function(function) => Expression {
                kind: ExpressionKind::Function(self.transform_function(function)?),
                span,
            },
            ExpressionKind::Await(value) => Expression {
                kind: ExpressionKind::Await(Box::new(self.transform_expression(value)?)),
                span,
            },
            ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This => expression.clone(),
        })
    }

    fn transform_member_read(
        &self,
        id: CandidateId,
        property: &MemberProperty,
        span: Span,
    ) -> Result<Expression> {
        let key = static_property_key(property)
            .ok_or_else(|| anyhow::anyhow!("dynamic aggregate key escaped scalar SSA"))?;
        let layout = self
            .layouts
            .get(&id)
            .ok_or_else(|| anyhow::anyhow!("aggregate layout #{id} chưa materialize"))?;
        if layout.kind == AggregateKind::Array && key == "length" {
            return Ok(number_expression(layout.length.unwrap_or(0) as f64, span));
        }
        Ok(layout
            .field(&key)
            .map(|field| global_expression(field.value_name.clone(), span))
            .unwrap_or_else(|| undefined_expression(span)))
    }

    fn transform_equality(
        &self,
        left: &Expression,
        operator: BinaryOperator,
        right: &Expression,
        span: Span,
    ) -> Result<Expression> {
        let left_root = self.root(left);
        let right_root = self.root(right);
        let equal = match (left_root, right_root) {
            (Some(left), Some(right)) => left == right,
            (Some(_), None) if is_nullish_literal(right) => false,
            (None, Some(_)) if is_nullish_literal(left) => false,
            _ => bail!("aggregate equality escaped scalar SSA"),
        };
        let value = match operator {
            BinaryOperator::Equal | BinaryOperator::StrictEqual => equal,
            BinaryOperator::NotEqual | BinaryOperator::StrictNotEqual => !equal,
            _ => unreachable!(),
        };
        Ok(bool_expression(value, span))
    }

    fn transform_assignment_target(
        &mut self,
        target: &AssignmentTarget,
    ) -> Result<AssignmentTarget> {
        Ok(match target {
            AssignmentTarget::Identifier(name) => {
                if self.environment.lookup(name).is_some() {
                    bail!("aggregate binding reassignment escaped scalar SSA")
                }
                AssignmentTarget::Identifier(name.clone())
            }
            AssignmentTarget::Member { object, property } => {
                if let Some(id) = self.root(object) {
                    let key = static_property_key(property)
                        .ok_or_else(|| anyhow::anyhow!("dynamic aggregate write key"))?;
                    let layout = self.layouts.get(&id).ok_or_else(|| {
                        anyhow::anyhow!("aggregate layout #{id} chưa materialize")
                    })?;
                    if layout.kind == AggregateKind::Array && key == "length" {
                        bail!("array length mutation chưa thuộc fixed aggregate SSA")
                    }
                    let field = layout.field(&key).ok_or_else(|| {
                        anyhow::anyhow!("shape-changing write `{key}` escaped SSA")
                    })?;
                    AssignmentTarget::Identifier(field.value_name.clone())
                } else {
                    AssignmentTarget::Member {
                        object: Box::new(self.transform_expression(object)?),
                        property: self.transform_property(property)?,
                    }
                }
            }
        })
    }

    fn transform_property(&mut self, property: &MemberProperty) -> Result<MemberProperty> {
        Ok(match property {
            MemberProperty::Static(key) => MemberProperty::Static(key.clone()),
            MemberProperty::Computed(value) => {
                MemberProperty::Computed(Box::new(self.transform_expression(value)?))
            }
        })
    }

    fn transform_object_entry(&mut self, entry: &ObjectEntry) -> Result<ObjectEntry> {
        Ok(match entry {
            ObjectEntry::Property(property) => ObjectEntry::Property(ecmora_hir::ObjectProperty {
                key: self.transform_property(&property.key)?,
                value: self.transform_expression(&property.value)?,
            }),
            ObjectEntry::Spread(value) => ObjectEntry::Spread(self.transform_expression(value)?),
            ObjectEntry::Accessor { key, get, set } => ObjectEntry::Accessor {
                key: key.clone(),
                get: get
                    .as_ref()
                    .map(|value| self.transform_expression(value))
                    .transpose()?,
                set: set
                    .as_ref()
                    .map(|value| self.transform_expression(value))
                    .transpose()?,
            },
        })
    }

    fn transform_array_element(&mut self, element: &ArrayElement) -> Result<ArrayElement> {
        Ok(match element {
            ArrayElement::Expression(value) => {
                ArrayElement::Expression(self.transform_expression(value)?)
            }
            ArrayElement::Spread(value) => ArrayElement::Spread(self.transform_expression(value)?),
            ArrayElement::Hole => ArrayElement::Hole,
        })
    }

    fn transform_call_arguments(&mut self, arguments: &[Expression]) -> Result<Vec<Expression>> {
        let mut output = Vec::new();
        for argument in arguments {
            if let Some(source) = spread_source(argument) {
                if let Some(id) = self.root(source).filter(|id| self.safe.contains(id)) {
                    let layout =
                        self.layouts.get(&id).cloned().ok_or_else(|| {
                            anyhow::anyhow!("spread layout #{id} chưa materialize")
                        })?;
                    if layout.kind != AggregateKind::Array {
                        bail!("call spread source không phải scalar array")
                    }
                    output.extend(
                        layout
                            .fields
                            .into_iter()
                            .map(|field| global_expression(field.value_name, argument.span)),
                    );
                    continue;
                }
            }
            output.push(self.transform_expression(argument)?);
        }
        Ok(output)
    }
}

fn static_property_key(property: &MemberProperty) -> Option<String> {
    match property {
        MemberProperty::Static(key) => Some(key.clone()),
        MemberProperty::Computed(value) => static_expression_key(value),
    }
}

fn static_expression_key(expression: &Expression) -> Option<String> {
    match &expression.kind {
        ExpressionKind::String(value) => Some(value.clone()),
        ExpressionKind::Number(value) => Some(canonical_number_key(*value)),
        _ => None,
    }
}

fn canonical_number_key(value: f64) -> String {
    if value == 0.0 {
        return "0".to_owned();
    }
    if value.is_finite() && value.fract() == 0.0 {
        return format!("{value:.0}");
    }
    value.to_string()
}

fn spread_source(expression: &Expression) -> Option<&Expression> {
    let ExpressionKind::Call { callee, arguments } = &expression.kind else {
        return None;
    };
    if !matches!(&callee.kind, ExpressionKind::Global(name) if name == "@spread") {
        return None;
    }
    match arguments.as_slice() {
        [value] => Some(value),
        _ => None,
    }
}

fn is_nullish_literal(expression: &Expression) -> bool {
    matches!(&expression.kind, ExpressionKind::Null)
        || matches!(&expression.kind, ExpressionKind::Global(name) if name == "undefined")
}

fn synthetic_field_name(id: CandidateId, index: usize, key: &str) -> String {
    let suffix = key
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    format!("@aggregate:{id}:{index}:{suffix}")
}

fn variable_statement(name: String, value: Expression, span: Span) -> Statement {
    Statement {
        kind: StatementKind::VariableDeclaration {
            kind: VariableKind::Let,
            declarations: vec![VariableDeclarator {
                name,
                init: Some(value),
                span,
            }],
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

fn string_expression(value: impl Into<String>, span: Span) -> Expression {
    Expression {
        kind: ExpressionKind::String(value.into()),
        span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_numeric_keys_match_array_indices() {
        assert_eq!(canonical_number_key(0.0), "0");
        assert_eq!(canonical_number_key(-0.0), "0");
        assert_eq!(canonical_number_key(12.0), "12");
        assert_eq!(canonical_number_key(1.5), "1.5");
    }
}
