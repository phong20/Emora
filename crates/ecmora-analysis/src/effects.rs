use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentTarget, BinaryOperator, Expression, ExpressionKind, ForInit,
    MemberProperty, ObjectEntry, Program, Statement, StatementKind,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct EffectSet(u32);

impl EffectSet {
    pub const READ_PROPERTY: Self = Self(1 << 0);
    pub const WRITE_PROPERTY: Self = Self(1 << 1);
    pub const DELETE_PROPERTY: Self = Self(1 << 2);
    pub const ENUMERATE: Self = Self(1 << 3);
    pub const CALL_USER_CODE: Self = Self(1 << 4);
    pub const MAY_THROW: Self = Self(1 << 5);
    pub const ENQUEUE_JOB: Self = Self(1 << 6);
    pub const SUSPEND: Self = Self(1 << 7);
    pub const REALM_SENSITIVE: Self = Self(1 << 8);
    pub const PROXY_OBSERVABLE: Self = Self(1 << 9);
    pub const CLASS_CONSTRUCT: Self = Self(1 << 10);
    pub const GENERATOR_STATE: Self = Self(1 << 11);

    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    fn insert(&mut self, other: Self) {
        self.0 |= other.0;
    }
}

#[derive(Debug, Clone, Default)]
pub struct SemanticSummary {
    pub effects: EffectSet,
    pub intrinsic_proxy: bool,
    pub dynamic_property_reads: usize,
    pub dynamic_property_writes: usize,
    pub suspension_points: usize,
    pub generator_functions: usize,
    pub var_declarations: usize,
}

pub fn summarize(program: &Program) -> SemanticSummary {
    let mut summary = SemanticSummary::default();
    for statement in &program.statements {
        visit_statement(statement, &mut summary);
    }
    for class in &program.promise_subclasses {
        if let Some(constructor) = &class.constructor {
            visit_function(constructor, &mut summary);
        }
        for method in &class.methods {
            visit_function(&method.function, &mut summary);
        }
    }
    summary
}

pub(crate) fn expression_effects(expression: &Expression) -> EffectSet {
    let mut summary = SemanticSummary::default();
    visit_expression(expression, &mut summary);
    summary.effects
}

fn visit_function(function: &ecmora_hir::Function, summary: &mut SemanticSummary) {
    if function.generator {
        summary.generator_functions += 1;
        summary.effects.insert(
            EffectSet::GENERATOR_STATE
                .union(EffectSet::ENQUEUE_JOB)
                .union(EffectSet::SUSPEND)
                .union(EffectSet::MAY_THROW),
        );
    }
    for statement in &function.body {
        visit_statement(statement, summary);
    }
}

pub(super) fn validate_native_semantics(program: &Program) -> Result<()> {
    let summary = summarize(program);
    if summary.intrinsic_proxy {
        bail!(
            "Proxy observable internal methods require compatibility object operations; \
             native SSA must not fold or bypass Proxy traps"
        )
    }
    Ok(())
}

fn visit_statement(statement: &Statement, summary: &mut SemanticSummary) {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            visit_expression(value, summary)
        }
        StatementKind::VariableDeclaration { kind, declarations } => {
            if *kind == ecmora_hir::VariableKind::Var {
                summary.var_declarations += declarations.len();
            }
            for declaration in declarations {
                if let Some(value) = &declaration.init {
                    visit_expression(value, summary);
                }
            }
        }
        StatementKind::Block(body) => {
            for statement in body {
                visit_statement(statement, summary);
            }
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            visit_expression(test, summary);
            visit_statement(consequent, summary);
            if let Some(alternate) = alternate {
                visit_statement(alternate, summary);
            }
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            visit_expression(test, summary);
            visit_statement(body, summary);
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            if let Some(init) = init {
                match init {
                    ForInit::Expression(value) => visit_expression(value, summary),
                    ForInit::VariableDeclaration { declarations, .. } => {
                        for declaration in declarations {
                            if let Some(value) = &declaration.init {
                                visit_expression(value, summary);
                            }
                        }
                    }
                }
            }
            if let Some(test) = test {
                visit_expression(test, summary);
            }
            if let Some(update) = update {
                visit_expression(update, summary);
            }
            visit_statement(body, summary);
        }
        StatementKind::ForIn { right, body, .. } => {
            summary.effects.insert(
                EffectSet::ENUMERATE
                    .union(EffectSet::CALL_USER_CODE)
                    .union(EffectSet::MAY_THROW)
                    .union(EffectSet::PROXY_OBSERVABLE),
            );
            visit_expression(right, summary);
            visit_statement(body, summary);
        }
        StatementKind::ForOf { right, body, .. } => {
            summary.effects.insert(
                EffectSet::CALL_USER_CODE
                    .union(EffectSet::MAY_THROW)
                    .union(EffectSet::REALM_SENSITIVE),
            );
            visit_expression(right, summary);
            visit_statement(body, summary);
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            visit_expression(discriminant, summary);
            for case in cases {
                if let Some(test) = &case.test {
                    visit_expression(test, summary);
                }
                for statement in &case.consequent {
                    visit_statement(statement, summary);
                }
            }
        }
        StatementKind::FunctionDeclaration(function) => {
            visit_function(function, summary);
        }
        StatementKind::Return(value) => {
            if let Some(value) = value {
                visit_expression(value, summary);
            }
        }
        StatementKind::Break | StatementKind::Continue => {}
    }
}

fn visit_expression(expression: &Expression, summary: &mut SemanticSummary) {
    match &expression.kind {
        ExpressionKind::Global(name) => {
            if name == "Proxy" {
                summary.intrinsic_proxy = true;
                summary.effects.insert(
                    EffectSet::PROXY_OBSERVABLE
                        .union(EffectSet::CALL_USER_CODE)
                        .union(EffectSet::MAY_THROW)
                        .union(EffectSet::REALM_SENSITIVE),
                );
            }
        }
        ExpressionKind::Member { object, property } => {
            summary.dynamic_property_reads += 1;
            summary.effects.insert(
                EffectSet::READ_PROPERTY
                    .union(EffectSet::CALL_USER_CODE)
                    .union(EffectSet::MAY_THROW)
                    .union(EffectSet::PROXY_OBSERVABLE),
            );
            visit_expression(object, summary);
            if let MemberProperty::Computed(value) = property {
                visit_expression(value, summary);
            }
        }
        ExpressionKind::Object(entries) => {
            for entry in entries {
                match entry {
                    ObjectEntry::Property(property) => {
                        if let MemberProperty::Computed(value) = &property.key {
                            visit_expression(value, summary);
                        }
                        visit_expression(&property.value, summary);
                    }
                    ObjectEntry::Spread(value) => {
                        summary.effects.insert(
                            EffectSet::ENUMERATE
                                .union(EffectSet::READ_PROPERTY)
                                .union(EffectSet::CALL_USER_CODE)
                                .union(EffectSet::MAY_THROW)
                                .union(EffectSet::PROXY_OBSERVABLE),
                        );
                        visit_expression(value, summary);
                    }
                    ObjectEntry::Accessor { get, set, .. } => {
                        if let Some(get) = get {
                            visit_expression(get, summary);
                        }
                        if let Some(set) = set {
                            visit_expression(set, summary);
                        }
                    }
                }
            }
        }
        ExpressionKind::Array(elements) => {
            for element in elements {
                match element {
                    ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                        visit_expression(value, summary)
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
            visit_expression(test, summary);
            visit_expression(consequent, summary);
            visit_expression(alternate, summary);
        }
        ExpressionKind::Unary { operator, argument } => {
            if matches!(operator, ecmora_hir::UnaryOperator::Delete) {
                summary.effects.insert(
                    EffectSet::DELETE_PROPERTY
                        .union(EffectSet::CALL_USER_CODE)
                        .union(EffectSet::MAY_THROW)
                        .union(EffectSet::PROXY_OBSERVABLE),
                );
            }
            visit_expression(argument, summary);
        }
        ExpressionKind::Binary {
            left,
            operator,
            right,
        } => {
            if matches!(operator, BinaryOperator::In | BinaryOperator::InstanceOf) {
                summary.effects.insert(
                    EffectSet::CALL_USER_CODE
                        .union(EffectSet::MAY_THROW)
                        .union(EffectSet::PROXY_OBSERVABLE)
                        .union(EffectSet::REALM_SENSITIVE),
                );
            }
            visit_expression(left, summary);
            visit_expression(right, summary);
        }
        ExpressionKind::Logical { left, right, .. } => {
            visit_expression(left, summary);
            visit_expression(right, summary);
        }
        ExpressionKind::Assignment { target, value, .. } => {
            visit_target(target, summary, true);
            visit_expression(value, summary);
        }
        ExpressionKind::Update { target, .. } => visit_target(target, summary, true),
        ExpressionKind::Call { callee, arguments } => {
            if matches!(&callee.kind, ExpressionKind::Global(name) if name == "@yield") {
                summary.suspension_points += 1;
                summary.effects.insert(
                    EffectSet::GENERATOR_STATE
                        .union(EffectSet::ENQUEUE_JOB)
                        .union(EffectSet::SUSPEND)
                        .union(EffectSet::MAY_THROW),
                );
            }
            summary.effects.insert(
                EffectSet::CALL_USER_CODE
                    .union(EffectSet::MAY_THROW)
                    .union(EffectSet::REALM_SENSITIVE),
            );
            visit_expression(callee, summary);
            for argument in arguments {
                visit_expression(argument, summary);
            }
        }
        ExpressionKind::New { callee, arguments } => {
            summary.effects.insert(
                EffectSet::CLASS_CONSTRUCT
                    .union(EffectSet::CALL_USER_CODE)
                    .union(EffectSet::MAY_THROW)
                    .union(EffectSet::REALM_SENSITIVE),
            );
            visit_expression(callee, summary);
            for argument in arguments {
                visit_expression(argument, summary);
            }
        }
        ExpressionKind::Function(function) => {
            visit_function(function, summary);
        }
        ExpressionKind::Await(value) => {
            summary.suspension_points += 1;
            summary.effects.insert(
                EffectSet::SUSPEND
                    .union(EffectSet::ENQUEUE_JOB)
                    .union(EffectSet::CALL_USER_CODE)
                    .union(EffectSet::MAY_THROW)
                    .union(EffectSet::REALM_SENSITIVE),
            );
            visit_expression(value, summary);
        }
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This => {}
    }
}

fn visit_target(target: &AssignmentTarget, summary: &mut SemanticSummary, write: bool) {
    match target {
        AssignmentTarget::Identifier(_) => {}
        AssignmentTarget::Member { object, property } => {
            if write {
                summary.dynamic_property_writes += 1;
                summary.effects.insert(
                    EffectSet::WRITE_PROPERTY
                        .union(EffectSet::CALL_USER_CODE)
                        .union(EffectSet::MAY_THROW)
                        .union(EffectSet::PROXY_OBSERVABLE),
                );
            }
            visit_expression(object, summary);
            if let MemberProperty::Computed(value) = property {
                visit_expression(value, summary);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ecmora_hir::{Span, VariableDeclarator, VariableKind};

    fn span() -> Span {
        Span::new(0, 0)
    }

    #[test]
    fn detects_proxy_intrinsic_and_observable_get() {
        let proxy = Expression {
            kind: ExpressionKind::New {
                callee: Box::new(Expression {
                    kind: ExpressionKind::Global("Proxy".to_owned()),
                    span: span(),
                }),
                arguments: vec![
                    Expression {
                        kind: ExpressionKind::Object(Vec::new()),
                        span: span(),
                    },
                    Expression {
                        kind: ExpressionKind::Object(Vec::new()),
                        span: span(),
                    },
                ],
            },
            span: span(),
        };
        let program = Program {
            statements: vec![Statement {
                kind: StatementKind::VariableDeclaration {
                    kind: VariableKind::Const,
                    declarations: vec![VariableDeclarator {
                        name: "proxy".to_owned(),
                        init: Some(proxy),
                        span: span(),
                    }],
                },
                span: span(),
            }],
            strict: false,
            imports: Vec::new(),
            exports: Vec::new(),
            export_all: Vec::new(),
            promise_subclasses: Vec::new(),
        };
        let summary = summarize(&program);
        assert!(summary.intrinsic_proxy);
        assert!(summary.effects.contains(EffectSet::PROXY_OBSERVABLE));
        assert!(validate_native_semantics(&program).is_err());
    }
}
