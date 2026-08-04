use super::*;

pub(super) fn collect_free_variables(function: &HirFunction) -> HashSet<String> {
    FreeVariableCollector::collect(function)
}

#[derive(Debug, Default)]
struct FreeVariableCollector {
    /// Các lexical scope nằm bên trong function đang được phân tích.
    scopes: Vec<HashSet<String>>,

    /// Identifier được dùng nhưng không được khai báo trong function.
    free: HashSet<String>,
}

impl FreeVariableCollector {
    fn collect(function: &HirFunction) -> HashSet<String> {
        let mut collector = Self::default();

        // Function scope chứa tên function và parameters.
        let mut function_scope = HashSet::new();

        // Tên function phải được coi là local để recursion không trở thành
        // một captured variable.
        if let Some(name) = &function.name {
            function_scope.insert(name.clone());
        }

        function_scope.extend(function.parameters.iter().cloned());

        collector.scopes.push(function_scope);
        collector.predeclare_current_scope(&function.body);
        collector.walk_statements(&function.body);
        collector.scopes.pop();

        collector.free
    }

    fn current_scope_mut(&mut self) -> &mut HashSet<String> {
        self.scopes
            .last_mut()
            .expect("free-variable collector phải có scope")
    }

    /// Khai báo trước các binding trực tiếp thuộc lexical scope hiện tại.
    ///
    /// Không đi vào block con vì block con có scope riêng.
    fn predeclare_current_scope(&mut self, statements: &[Statement]) {
        for statement in statements {
            match &statement.kind {
                StatementKind::VariableDeclaration { declarations, .. } => {
                    for declaration in declarations {
                        self.current_scope_mut().insert(declaration.name.clone());
                    }
                }

                StatementKind::FunctionDeclaration(function) => {
                    if let Some(name) = &function.name {
                        self.current_scope_mut().insert(name.clone());
                    }
                }

                _ => {}
            }
        }
    }

    fn use_name(&mut self, name: &str) {
        let is_local = self.scopes.iter().rev().any(|scope| scope.contains(name));

        if !is_local {
            self.free.insert(name.to_owned());
        }
    }

    fn walk_statements(&mut self, statements: &[Statement]) {
        for statement in statements {
            self.walk_statement(statement);
        }
    }

    fn walk_statement(&mut self, statement: &Statement) {
        match &statement.kind {
            StatementKind::Expression(expression) | StatementKind::Throw(expression) => {
                self.walk_expression(expression);
            }

            StatementKind::VariableDeclaration { declarations, .. } => {
                // Tên đã được predeclare. Ở đây chỉ phân tích initializer.
                for declaration in declarations {
                    if let Some(initializer) = &declaration.init {
                        self.walk_expression(initializer);
                    }
                }
            }

            StatementKind::Block(statements) => {
                self.scopes.push(HashSet::new());
                self.predeclare_current_scope(statements);
                self.walk_statements(statements);
                self.scopes.pop();
            }

            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                self.walk_expression(test);
                self.walk_statement(consequent);

                if let Some(alternate) = alternate {
                    self.walk_statement(alternate);
                }
            }

            StatementKind::While { test, body } => {
                self.walk_expression(test);
                self.walk_statement(body);
            }

            StatementKind::DoWhile { body, test } => {
                self.walk_statement(body);
                self.walk_expression(test);
            }

            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                // Lowerer hiện tạo scope riêng khi for có initializer.
                let has_for_scope = init.is_some();

                if has_for_scope {
                    self.scopes.push(HashSet::new());
                }

                if let Some(init) = init {
                    match init {
                        ForInit::VariableDeclaration { declarations, .. } => {
                            // Binding trong for phải tồn tại trước initializer
                            // để xử lý shadowing/TDZ chính xác hơn.
                            for declaration in declarations {
                                self.current_scope_mut().insert(declaration.name.clone());
                            }

                            for declaration in declarations {
                                if let Some(initializer) = &declaration.init {
                                    self.walk_expression(initializer);
                                }
                            }
                        }

                        ForInit::Expression(expression) => {
                            self.walk_expression(expression);
                        }
                    }
                }

                if let Some(test) = test {
                    self.walk_expression(test);
                }

                if let Some(update) = update {
                    self.walk_expression(update);
                }

                self.walk_statement(body);

                if has_for_scope {
                    self.scopes.pop();
                }
            }

            StatementKind::ForIn {
                name, right, body, ..
            }
            | StatementKind::ForOf {
                name, right, body, ..
            } => {
                // RHS được đánh giá ngoài binding của vòng lặp.
                self.walk_expression(right);

                self.scopes.push(HashSet::new());
                self.current_scope_mut().insert(name.clone());
                self.walk_statement(body);
                self.scopes.pop();
            }

            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                self.walk_expression(discriminant);

                // Các case dùng chung lexical scope của switch.
                self.scopes.push(HashSet::new());

                for case in cases {
                    self.predeclare_current_scope(&case.consequent);
                }

                for case in cases {
                    if let Some(test) = &case.test {
                        self.walk_expression(test);
                    }

                    self.walk_statements(&case.consequent);
                }

                self.scopes.pop();
            }

            StatementKind::FunctionDeclaration(function) => {
                // Function declaration là closure được tạo trong scope hiện tại.
                // Ta phải đi vào function con để propagate captures xuyên cấp.
                self.walk_nested_function(function);
            }

            StatementKind::Return(expression) => {
                if let Some(expression) = expression {
                    self.walk_expression(expression);
                }
            }

            StatementKind::Break | StatementKind::Continue => {}
        }
    }

    fn walk_expression(&mut self, expression: &Expression) {
        match &expression.kind {
            ExpressionKind::Global(name) => {
                self.use_name(name);
            }

            ExpressionKind::Member { object, property } => {
                self.walk_expression(object);

                if let MemberProperty::Computed(property) = property {
                    self.walk_expression(property);
                }
            }

            ExpressionKind::Object(entries) => {
                for entry in entries {
                    match entry {
                        ObjectEntry::Property(property) => {
                            if let MemberProperty::Computed(key) = &property.key {
                                self.walk_expression(key);
                            }

                            self.walk_expression(&property.value);
                        }

                        ObjectEntry::Spread(expression) => {
                            self.walk_expression(expression);
                        }

                        ObjectEntry::Accessor { get, set, .. } => {
                            if let Some(getter) = get {
                                self.walk_expression(getter);
                            }

                            if let Some(setter) = set {
                                self.walk_expression(setter);
                            }
                        }
                    }
                }
            }

            ExpressionKind::Array(elements) => {
                for element in elements {
                    match element {
                        ArrayElement::Expression(expression) | ArrayElement::Spread(expression) => {
                            self.walk_expression(expression);
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
                self.walk_expression(test);
                self.walk_expression(consequent);
                self.walk_expression(alternate);
            }

            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                self.walk_expression(argument);
            }

            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                self.walk_expression(left);
                self.walk_expression(right);
            }

            ExpressionKind::Assignment { target, value, .. } => {
                self.walk_assignment_target(target);
                self.walk_expression(value);
            }

            ExpressionKind::Update { target, .. } => {
                self.walk_assignment_target(target);
            }

            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                self.walk_expression(callee);

                for argument in arguments {
                    self.walk_expression(argument);
                }
            }

            ExpressionKind::Function(function) => {
                self.walk_nested_function(function);
            }

            ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This => {}
        }
    }

    fn walk_assignment_target(&mut self, target: &AssignmentTarget) {
        match target {
            AssignmentTarget::Identifier(name) => {
                // Gán vào identifier vẫn là một binding reference.
                self.use_name(name);
            }

            AssignmentTarget::Member { object, property } => {
                self.walk_expression(object);

                if let MemberProperty::Computed(property) = property {
                    self.walk_expression(property);
                }
            }
        }
    }

    fn walk_nested_function(&mut self, function: &HirFunction) {
        let mut function_scope = HashSet::new();

        if let Some(name) = &function.name {
            function_scope.insert(name.clone());
        }

        function_scope.extend(function.parameters.iter().cloned());

        self.scopes.push(function_scope);
        self.predeclare_current_scope(&function.body);
        self.walk_statements(&function.body);
        self.scopes.pop();
    }
}

#[derive(Debug, Default)]
struct ReturnTypeHints {
    known: Vec<ValueType>,
    has_unknown: bool,
}

pub(super) fn infer_function_return_type(
    function: &HirFunction,
    parameter_types: &HashMap<String, ValueType>,
    captures: &[CapturedBinding],
) -> ValueType {
    let mut bindings = parameter_types.clone();

    for capture in captures {
        bindings.insert(capture.name.clone(), capture.value_type);
    }

    let mut hints = ReturnTypeHints::default();

    collect_return_type_hints(
        &function.body,
        &mut bindings,
        function.name.as_deref(),
        &mut hints,
    );

    // Function có đường chạy tới cuối body sẽ return undefined.
    if !statements_always_terminate(&function.body) {
        hints.known.push(ValueType::Undefined);
    }

    let Some(first) = hints.known.first().copied() else {
        return if hints.has_unknown {
            ValueType::Dynamic
        } else {
            ValueType::Undefined
        };
    };

    if hints.known.iter().all(|value_type| *value_type == first) {
        // Unknown return thường chính là recursive call. Base case đã cung cấp
        // type seed cho nó.
        first
    } else {
        ValueType::Dynamic
    }
}

fn collect_return_type_hints(
    statements: &[Statement],
    bindings: &mut HashMap<String, ValueType>,
    recursive_name: Option<&str>,
    hints: &mut ReturnTypeHints,
) {
    for statement in statements {
        match &statement.kind {
            StatementKind::Expression(_) => {}

            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    let value_type = declaration
                        .init
                        .as_ref()
                        .and_then(|expression| {
                            infer_expression_type_hint(expression, bindings, recursive_name)
                        })
                        .unwrap_or(ValueType::Undefined);

                    bindings.insert(declaration.name.clone(), value_type);
                }
            }

            StatementKind::Block(body) => {
                let mut block_bindings = bindings.clone();

                collect_return_type_hints(body, &mut block_bindings, recursive_name, hints);
            }

            StatementKind::If {
                test: _,
                consequent,
                alternate,
            } => {
                let mut then_bindings = bindings.clone();

                collect_return_type_hint_from_statement(
                    consequent,
                    &mut then_bindings,
                    recursive_name,
                    hints,
                );

                if let Some(alternate) = alternate {
                    let mut else_bindings = bindings.clone();

                    collect_return_type_hint_from_statement(
                        alternate,
                        &mut else_bindings,
                        recursive_name,
                        hints,
                    );
                }
            }

            StatementKind::While { body, .. } | StatementKind::DoWhile { body, .. } => {
                let mut loop_bindings = bindings.clone();

                collect_return_type_hint_from_statement(
                    body,
                    &mut loop_bindings,
                    recursive_name,
                    hints,
                );
            }

            StatementKind::For { init, body, .. } => {
                let mut loop_bindings = bindings.clone();

                if let Some(init) = init {
                    match init {
                        ForInit::VariableDeclaration { declarations, .. } => {
                            for declaration in declarations {
                                let value_type = declaration
                                    .init
                                    .as_ref()
                                    .and_then(|expression| {
                                        infer_expression_type_hint(
                                            expression,
                                            &loop_bindings,
                                            recursive_name,
                                        )
                                    })
                                    .unwrap_or(ValueType::Undefined);

                                loop_bindings.insert(declaration.name.clone(), value_type);
                            }
                        }

                        ForInit::Expression(_) => {}
                    }
                }

                collect_return_type_hint_from_statement(
                    body,
                    &mut loop_bindings,
                    recursive_name,
                    hints,
                );
            }

            StatementKind::ForIn { name, body, .. } | StatementKind::ForOf { name, body, .. } => {
                let mut loop_bindings = bindings.clone();
                loop_bindings.insert(name.clone(), ValueType::Dynamic);

                collect_return_type_hint_from_statement(
                    body,
                    &mut loop_bindings,
                    recursive_name,
                    hints,
                );
            }

            StatementKind::Switch { cases, .. } => {
                for case in cases {
                    let mut case_bindings = bindings.clone();

                    collect_return_type_hints(
                        &case.consequent,
                        &mut case_bindings,
                        recursive_name,
                        hints,
                    );
                }
            }

            StatementKind::FunctionDeclaration(function) => {
                if let Some(name) = &function.name {
                    bindings.insert(name.clone(), ValueType::Callable);
                }

                // Không gom return của nested function vào outer function.
            }

            StatementKind::Return(expression) => match expression {
                Some(expression) => {
                    if let Some(value_type) =
                        infer_expression_type_hint(expression, bindings, recursive_name)
                    {
                        hints.known.push(value_type);
                    } else {
                        hints.has_unknown = true;
                    }
                }

                None => {
                    hints.known.push(ValueType::Undefined);
                }
            },

            StatementKind::Throw(_) => {
                // Throw is an abrupt completion, not a normal return. Its type
                // must not widen or seed the function's return specialization.
            }

            StatementKind::Break | StatementKind::Continue => {}
        }

        // Return/throw make later statements in this lexical sequence
        // unreachable. Ignoring them avoids false return-type pollution.
        if statement_always_terminates(statement) {
            break;
        }
    }
}

fn collect_return_type_hint_from_statement(
    statement: &Statement,
    bindings: &mut HashMap<String, ValueType>,
    recursive_name: Option<&str>,
    hints: &mut ReturnTypeHints,
) {
    collect_return_type_hints(
        std::slice::from_ref(statement),
        bindings,
        recursive_name,
        hints,
    );
}

fn statements_always_terminate(statements: &[Statement]) -> bool {
    for statement in statements {
        if statement_always_terminates(statement) {
            return true;
        }
    }

    false
}

fn statement_always_terminates(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Return(_) | StatementKind::Throw(_) => true,

        StatementKind::Block(body) => statements_always_terminate(body),

        StatementKind::If {
            consequent,
            alternate: Some(alternate),
            ..
        } => statement_always_terminates(consequent) && statement_always_terminates(alternate),

        // A do/while executes its body at least once. A literal-true while or
        // for(;;) cannot fall through when its body itself completes abruptly.
        StatementKind::DoWhile { body, .. } => statement_always_terminates(body),
        StatementKind::While { test, body } => {
            expression_is_literal_true(test) && statement_always_terminates(body)
        }
        StatementKind::For {
            test: None, body, ..
        } => statement_always_terminates(body),

        // Each switch clause may be entered directly; require a default and
        // every clause to terminate on its own. This is conservative around
        // case fallthrough but never marks a fallthrough switch as terminal.
        StatementKind::Switch { cases, .. } => {
            cases.iter().any(|case| case.test.is_none())
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|case| statements_always_terminate(&case.consequent))
        }

        StatementKind::Expression(_)
        | StatementKind::VariableDeclaration { .. }
        | StatementKind::If {
            alternate: None, ..
        }
        | StatementKind::For { .. }
        | StatementKind::ForIn { .. }
        | StatementKind::ForOf { .. }
        | StatementKind::FunctionDeclaration(_)
        | StatementKind::Break
        | StatementKind::Continue => false,
    }
}

fn expression_is_literal_true(expression: &Expression) -> bool {
    matches!(&expression.kind, ExpressionKind::Bool(true))
}

/// Detect a throw owned by this function body. Nested functions are skipped:
/// they have an independent completion boundary and are analyzed separately.
pub(super) fn unconditional_function_throw(function: &HirFunction) -> Option<&Expression> {
    for statement in &function.body {
        match &statement.kind {
            StatementKind::Throw(reason) => return Some(reason),
            StatementKind::FunctionDeclaration(_)
            | StatementKind::VariableDeclaration { .. }
            | StatementKind::Expression(_) => {}
            // A branch/loop/switch means the throw is not statically
            // unconditional at this abstraction level.
            _ => return None,
        }
    }
    None
}

pub(super) fn function_contains_direct_throw(function: &HirFunction) -> bool {
    function.body.iter().any(statement_contains_direct_throw)
}

fn statement_contains_direct_throw(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Throw(_) => true,
        StatementKind::Block(body) => body.iter().any(statement_contains_direct_throw),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            statement_contains_direct_throw(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(statement_contains_direct_throw)
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. } => statement_contains_direct_throw(body),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|case| &case.consequent)
            .any(statement_contains_direct_throw),
        // Nested function throws belong to the nested function.
        StatementKind::FunctionDeclaration(_)
        | StatementKind::Expression(_)
        | StatementKind::VariableDeclaration { .. }
        | StatementKind::Return(_)
        | StatementKind::Break
        | StatementKind::Continue => false,
    }
}

pub(super) fn infer_expression_type_hint(
    expression: &Expression,
    bindings: &HashMap<String, ValueType>,
    recursive_name: Option<&str>,
) -> Option<ValueType> {
    match &expression.kind {
        ExpressionKind::String(_) => Some(ValueType::String),
        ExpressionKind::Number(_) => Some(ValueType::Number),
        ExpressionKind::Bool(_) => Some(ValueType::Bool),
        ExpressionKind::Null => Some(ValueType::Null),
        // `this` depends on the call receiver and therefore has no stable
        // call-site type until receiver specialization is available.
        ExpressionKind::This => None,

        ExpressionKind::Global(name) => {
            if recursive_name == Some(name.as_str()) {
                // Self-recursive call/name được xử lý bằng provisional type.
                return None;
            }

            bindings.get(name).copied().or_else(|| match name.as_str() {
                "undefined" => Some(ValueType::Undefined),
                "NaN" | "Infinity" => Some(ValueType::Number),
                _ => None,
            })
        }

        ExpressionKind::Object(_) | ExpressionKind::Array(_) => Some(ValueType::Object),

        ExpressionKind::Function(_) => Some(ValueType::Callable),

        ExpressionKind::Conditional {
            consequent,
            alternate,
            ..
        } => {
            let left = infer_expression_type_hint(consequent, bindings, recursive_name);

            let right = infer_expression_type_hint(alternate, bindings, recursive_name);

            match (left, right) {
                (Some(left), Some(right)) if left == right => Some(left),
                _ => None,
            }
        }

        ExpressionKind::Unary {
            operator,
            argument: _,
        } => Some(match operator {
            UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitwiseNot => {
                ValueType::Number
            }

            UnaryOperator::Not | UnaryOperator::Delete => ValueType::Bool,

            UnaryOperator::Typeof => ValueType::String,
            UnaryOperator::Void => ValueType::Undefined,
        }),

        ExpressionKind::Binary {
            operator,
            left,
            right,
        } => match operator {
            BinaryOperator::Equal
            | BinaryOperator::NotEqual
            | BinaryOperator::StrictEqual
            | BinaryOperator::StrictNotEqual
            | BinaryOperator::LessThan
            | BinaryOperator::LessEqual
            | BinaryOperator::GreaterThan
            | BinaryOperator::GreaterEqual
            | BinaryOperator::In
            | BinaryOperator::InstanceOf => Some(ValueType::Bool),

            BinaryOperator::Add => {
                let left = infer_expression_type_hint(left, bindings, recursive_name);

                let right = infer_expression_type_hint(right, bindings, recursive_name);

                match (left, right) {
                    (Some(ValueType::Number), Some(ValueType::Number)) => Some(ValueType::Number),

                    (Some(ValueType::String), _) | (_, Some(ValueType::String)) => {
                        Some(ValueType::String)
                    }

                    _ => None,
                }
            }

            BinaryOperator::Subtract
            | BinaryOperator::Multiply
            | BinaryOperator::Divide
            | BinaryOperator::Remainder
            | BinaryOperator::Exponential
            | BinaryOperator::ShiftLeft
            | BinaryOperator::ShiftRight
            | BinaryOperator::ShiftRightZeroFill
            | BinaryOperator::BitwiseOr
            | BinaryOperator::BitwiseXor
            | BinaryOperator::BitwiseAnd => Some(ValueType::Number),
        },

        ExpressionKind::Logical { left, right, .. } => {
            let left = infer_expression_type_hint(left, bindings, recursive_name);

            let right = infer_expression_type_hint(right, bindings, recursive_name);

            match (left, right) {
                (Some(left), Some(right)) if left == right => Some(left),
                _ => None,
            }
        }

        ExpressionKind::Assignment {
            operator, value, ..
        } => match operator {
            AssignmentOperator::Assign
            | AssignmentOperator::LogicalOr
            | AssignmentOperator::LogicalAnd
            | AssignmentOperator::LogicalNullish => {
                infer_expression_type_hint(value, bindings, recursive_name)
            }

            AssignmentOperator::Add => infer_expression_type_hint(value, bindings, recursive_name),

            AssignmentOperator::Subtract
            | AssignmentOperator::Multiply
            | AssignmentOperator::Divide
            | AssignmentOperator::Remainder
            | AssignmentOperator::Exponential
            | AssignmentOperator::ShiftLeft
            | AssignmentOperator::ShiftRight
            | AssignmentOperator::ShiftRightZeroFill
            | AssignmentOperator::BitwiseOr
            | AssignmentOperator::BitwiseXor
            | AssignmentOperator::BitwiseAnd => Some(ValueType::Number),
        },

        ExpressionKind::Update { .. } => Some(ValueType::Number),

        ExpressionKind::Call {
            callee,
            arguments: _,
        } => match &callee.kind {
            ExpressionKind::Global(name) => {
                if recursive_name == Some(name.as_str()) {
                    None
                } else {
                    match name.as_str() {
                        "Number" => Some(ValueType::Number),
                        "String" => Some(ValueType::String),
                        "Boolean" => Some(ValueType::Bool),
                        _ => None,
                    }
                }
            }

            ExpressionKind::Member {
                object,
                property: MemberProperty::Static(method),
            } => match &object.kind {
                ExpressionKind::Global(name)
                    if name == "Promise" && matches!(method.as_str(), "resolve" | "reject") =>
                {
                    Some(ValueType::Promise)
                }

                _ => None,
            },

            _ => None,
        },

        ExpressionKind::New { callee, .. } => match &callee.kind {
            ExpressionKind::Global(name) if name == "Promise" => Some(ValueType::Promise),

            _ => Some(ValueType::Object),
        },

        ExpressionKind::Member { .. } | ExpressionKind::Await(_) => None,
    }
}

pub(super) fn type_of(value: &Value) -> ValueType {
    match value {
        Value::Undefined => ValueType::Undefined,
        Value::Null => ValueType::Null,
        Value::Number(_) => ValueType::Number,
        Value::Bool(_) => ValueType::Bool,
        Value::String(_) => ValueType::String,
        Value::Object(_) => ValueType::Object,
        Value::Array(_) => ValueType::Object,
        Value::Function(_) | Value::Promise(_) => ValueType::Dynamic,
    }
}
pub(super) fn to_sem_unary(operator: UnaryOperator) -> SemUnary {
    match operator {
        UnaryOperator::Plus => SemUnary::Plus,
        UnaryOperator::Minus => SemUnary::Minus,
        UnaryOperator::Not => SemUnary::Not,
        UnaryOperator::BitwiseNot => SemUnary::BitwiseNot,
        UnaryOperator::Typeof | UnaryOperator::Void | UnaryOperator::Delete => unreachable!(),
    }
}
pub(super) fn to_sem_binary(operator: BinaryOperator) -> SemBinary {
    match operator {
        BinaryOperator::Add => SemBinary::Add,
        BinaryOperator::Subtract => SemBinary::Subtract,
        BinaryOperator::Multiply => SemBinary::Multiply,
        BinaryOperator::Divide => SemBinary::Divide,
        BinaryOperator::Remainder => SemBinary::Remainder,
        BinaryOperator::Exponential => SemBinary::Exponential,
        BinaryOperator::Equal => SemBinary::Equal,
        BinaryOperator::NotEqual => SemBinary::NotEqual,
        BinaryOperator::StrictEqual => SemBinary::StrictEqual,
        BinaryOperator::StrictNotEqual => SemBinary::StrictNotEqual,
        BinaryOperator::LessThan => SemBinary::LessThan,
        BinaryOperator::LessEqual => SemBinary::LessEqual,
        BinaryOperator::GreaterThan => SemBinary::GreaterThan,
        BinaryOperator::GreaterEqual => SemBinary::GreaterEqual,
        BinaryOperator::ShiftLeft => SemBinary::ShiftLeft,
        BinaryOperator::ShiftRight => SemBinary::ShiftRight,
        BinaryOperator::ShiftRightZeroFill => SemBinary::ShiftRightZeroFill,
        BinaryOperator::BitwiseOr => SemBinary::BitwiseOr,
        BinaryOperator::BitwiseXor => SemBinary::BitwiseXor,
        BinaryOperator::BitwiseAnd => SemBinary::BitwiseAnd,
        BinaryOperator::In => SemBinary::In,
        BinaryOperator::InstanceOf => SemBinary::InstanceOf,
    }
}
pub(super) fn number_operator(operator: BinaryOperator) -> Option<BinaryNumberOperator> {
    Some(match operator {
        BinaryOperator::Add => BinaryNumberOperator::Add,
        BinaryOperator::Subtract => BinaryNumberOperator::Subtract,
        BinaryOperator::Multiply => BinaryNumberOperator::Multiply,
        BinaryOperator::Divide => BinaryNumberOperator::Divide,
        BinaryOperator::Remainder => BinaryNumberOperator::Remainder,
        BinaryOperator::Exponential => BinaryNumberOperator::Exponential,
        BinaryOperator::ShiftLeft => BinaryNumberOperator::ShiftLeft,
        BinaryOperator::ShiftRight => BinaryNumberOperator::ShiftRight,
        BinaryOperator::ShiftRightZeroFill => BinaryNumberOperator::ShiftRightZeroFill,
        BinaryOperator::BitwiseOr => BinaryNumberOperator::BitwiseOr,
        BinaryOperator::BitwiseXor => BinaryNumberOperator::BitwiseXor,
        BinaryOperator::BitwiseAnd => BinaryNumberOperator::BitwiseAnd,
        _ => return None,
    })
}
pub(super) fn number_operator_for_sem(operator: SemBinary) -> Option<BinaryNumberOperator> {
    Some(match operator {
        SemBinary::Add => BinaryNumberOperator::Add,
        SemBinary::Subtract => BinaryNumberOperator::Subtract,
        SemBinary::Multiply => BinaryNumberOperator::Multiply,
        SemBinary::Divide => BinaryNumberOperator::Divide,
        SemBinary::Remainder => BinaryNumberOperator::Remainder,
        SemBinary::Exponential => BinaryNumberOperator::Exponential,
        SemBinary::ShiftLeft => BinaryNumberOperator::ShiftLeft,
        SemBinary::ShiftRight => BinaryNumberOperator::ShiftRight,
        SemBinary::ShiftRightZeroFill => BinaryNumberOperator::ShiftRightZeroFill,
        SemBinary::BitwiseOr => BinaryNumberOperator::BitwiseOr,
        SemBinary::BitwiseXor => BinaryNumberOperator::BitwiseXor,
        SemBinary::BitwiseAnd => BinaryNumberOperator::BitwiseAnd,
        _ => return None,
    })
}
pub(super) fn compare_operator(operator: BinaryOperator) -> Option<CompareNumberOperator> {
    Some(match operator {
        BinaryOperator::Equal => CompareNumberOperator::Equal,
        BinaryOperator::NotEqual => CompareNumberOperator::NotEqual,
        BinaryOperator::StrictEqual => CompareNumberOperator::StrictEqual,
        BinaryOperator::StrictNotEqual => CompareNumberOperator::StrictNotEqual,
        BinaryOperator::LessThan => CompareNumberOperator::LessThan,
        BinaryOperator::LessEqual => CompareNumberOperator::LessEqual,
        BinaryOperator::GreaterThan => CompareNumberOperator::GreaterThan,
        BinaryOperator::GreaterEqual => CompareNumberOperator::GreaterEqual,
        _ => return None,
    })
}
pub(super) fn assignment_binary(operator: AssignmentOperator) -> Option<SemBinary> {
    Some(match operator {
        AssignmentOperator::Add => SemBinary::Add,
        AssignmentOperator::Subtract => SemBinary::Subtract,
        AssignmentOperator::Multiply => SemBinary::Multiply,
        AssignmentOperator::Divide => SemBinary::Divide,
        AssignmentOperator::Remainder => SemBinary::Remainder,
        AssignmentOperator::Exponential => SemBinary::Exponential,
        AssignmentOperator::ShiftLeft => SemBinary::ShiftLeft,
        AssignmentOperator::ShiftRight => SemBinary::ShiftRight,
        AssignmentOperator::ShiftRightZeroFill => SemBinary::ShiftRightZeroFill,
        AssignmentOperator::BitwiseOr => SemBinary::BitwiseOr,
        AssignmentOperator::BitwiseXor => SemBinary::BitwiseXor,
        AssignmentOperator::BitwiseAnd => SemBinary::BitwiseAnd,
        _ => return None,
    })
}

pub(super) fn sanitize_function_name(name: &str) -> String {
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

pub(super) fn collect_used_names(statements: &[Statement]) -> HashSet<String> {
    fn walk_expression(expression: &Expression, names: &mut HashSet<String>) {
        match &expression.kind {
            ExpressionKind::Global(name) => {
                names.insert(name.clone());
            }
            ExpressionKind::Member { object, property } => {
                walk_expression(object, names);
                if let MemberProperty::Computed(property) = property {
                    walk_expression(property, names);
                }
            }
            ExpressionKind::Object(entries) => {
                for entry in entries {
                    match entry {
                        ObjectEntry::Property(property) => {
                            if let MemberProperty::Computed(key) = &property.key {
                                walk_expression(key, names);
                            }
                            walk_expression(&property.value, names);
                        }
                        ObjectEntry::Spread(value) => walk_expression(value, names),
                        ObjectEntry::Accessor { get, set, .. } => {
                            if let Some(get) = get {
                                walk_expression(get, names);
                            }
                            if let Some(set) = set {
                                walk_expression(set, names);
                            }
                        }
                    }
                }
            }
            ExpressionKind::Array(elements) => {
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                            walk_expression(value, names);
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
                walk_expression(test, names);
                walk_expression(consequent, names);
                walk_expression(alternate, names);
            }
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                walk_expression(argument, names);
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                walk_expression(left, names);
                walk_expression(right, names);
            }
            ExpressionKind::Assignment { target, value, .. } => {
                target_names(target, names);
                walk_expression(value, names);
            }
            ExpressionKind::Update { target, .. } => target_names(target, names),
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                walk_expression(callee, names);
                for argument in arguments {
                    walk_expression(argument, names);
                }
            }
            // Function bodies are expanded by the reachability work-list
            // below, only after their declaration binding becomes live.
            ExpressionKind::Function(_) => {}
            ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This => {}
        }
    }

    fn target_names(target: &AssignmentTarget, names: &mut HashSet<String>) {
        match target {
            AssignmentTarget::Identifier(name) => {
                names.insert(name.clone());
            }
            AssignmentTarget::Member { object, property } => {
                walk_expression(object, names);
                if let MemberProperty::Computed(property) = property {
                    walk_expression(property, names);
                }
            }
        }
    }

    fn walk_statement(statement: &Statement, names: &mut HashSet<String>) {
        match &statement.kind {
            StatementKind::Expression(value) | StatementKind::Throw(value) => {
                walk_expression(value, names);
            }
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    if let Some(init) = &declaration.init {
                        walk_expression(init, names);
                    }
                }
            }
            StatementKind::Block(body) => walk_statements(body, names),
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                walk_expression(test, names);
                walk_statement(consequent, names);
                if let Some(alternate) = alternate {
                    walk_statement(alternate, names);
                }
            }
            StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
                walk_expression(test, names);
                walk_statement(body, names);
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
                                if let Some(init) = &declaration.init {
                                    walk_expression(init, names);
                                }
                            }
                        }
                        ForInit::Expression(value) => walk_expression(value, names),
                    }
                }
                if let Some(test) = test {
                    walk_expression(test, names);
                }
                if let Some(update) = update {
                    walk_expression(update, names);
                }
                walk_statement(body, names);
            }
            StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
                walk_expression(right, names);
                walk_statement(body, names);
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                walk_expression(discriminant, names);
                for case in cases {
                    if let Some(test) = &case.test {
                        walk_expression(test, names);
                    }
                    walk_statements(&case.consequent, names);
                }
            }
            StatementKind::FunctionDeclaration(_) => {}
            StatementKind::Return(value) => {
                if let Some(value) = value {
                    walk_expression(value, names);
                }
            }
            StatementKind::Break | StatementKind::Continue => {}
        }
    }

    fn walk_statements(body: &[Statement], names: &mut HashSet<String>) {
        for statement_value in body {
            walk_statement(statement_value, names);
        }
    }

    let mut callables = HashMap::<String, &[Statement]>::new();
    for statement in statements {
        match &statement.kind {
            StatementKind::FunctionDeclaration(function) => {
                if let Some(name) = &function.name {
                    callables.insert(name.clone(), &function.body);
                }
            }
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    if let Some(Expression {
                        kind: ExpressionKind::Function(function),
                        ..
                    }) = &declaration.init
                    {
                        callables.insert(declaration.name.clone(), &function.body);
                    }
                }
            }
            _ => {}
        }
    }

    let mut names = HashSet::new();
    walk_statements(statements, &mut names);
    let mut expanded = HashSet::new();
    loop {
        let pending = names
            .iter()
            .filter(|name| callables.contains_key(*name) && !expanded.contains(*name))
            .cloned()
            .collect::<Vec<_>>();
        if pending.is_empty() {
            break;
        }
        for name in pending {
            expanded.insert(name.clone());
            walk_statements(callables[&name], &mut names);
        }
    }
    names
}

pub(super) fn is_pure_expression_known(
    expression: &Expression,
    known_functions: &HashSet<String>,
) -> bool {
    match &expression.kind {
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This
        | ExpressionKind::Function(_) => true,
        ExpressionKind::Array(elements) => elements.iter().all(|element| match element {
            ArrayElement::Expression(value) => is_pure_expression_known(value, known_functions),
            ArrayElement::Hole => true,
            ArrayElement::Spread(_) => false,
        }),
        ExpressionKind::Object(entries) => entries.iter().all(|entry| match entry {
            ObjectEntry::Property(property) => {
                matches!(property.key, MemberProperty::Static(_))
                    && is_pure_expression_known(&property.value, known_functions)
            }
            ObjectEntry::Accessor { get, set, .. } => get
                .iter()
                .chain(set.iter())
                .all(|value| is_pure_expression_known(value, known_functions)),
            ObjectEntry::Spread(_) => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            is_pure_expression_known(test, known_functions)
                && is_pure_expression_known(consequent, known_functions)
                && is_pure_expression_known(alternate, known_functions)
        }
        ExpressionKind::Unary { argument, .. } => {
            is_pure_expression_known(argument, known_functions)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            is_pure_expression_known(left, known_functions)
                && is_pure_expression_known(right, known_functions)
        }
        ExpressionKind::Global(name) => known_functions.contains(name),
        ExpressionKind::Member { .. }
        | ExpressionKind::Assignment { .. }
        | ExpressionKind::Update { .. }
        | ExpressionKind::Call { .. }
        | ExpressionKind::New { .. }
        | ExpressionKind::Await(_) => false,
    }
}

#[cfg(test)]
mod throw_inference_tests {
    use super::*;

    fn span() -> Span {
        Span::new(0, 0)
    }

    fn number(value: f64) -> Expression {
        Expression {
            kind: ExpressionKind::Number(value),
            span: span(),
        }
    }

    fn string(value: &str) -> Expression {
        Expression {
            kind: ExpressionKind::String(value.to_owned()),
            span: span(),
        }
    }

    fn function(body: Vec<Statement>) -> HirFunction {
        HirFunction {
            name: Some("f".to_owned()),
            parameters: Vec::new(),
            body,
            r#async: false,
            generator: false,
            arrow: false,
            lowering_error: None,
        }
    }

    #[test]
    fn throw_does_not_poison_normal_return_type() {
        let body = vec![Statement {
            kind: StatementKind::If {
                test: Expression {
                    kind: ExpressionKind::Bool(true),
                    span: span(),
                },
                consequent: Box::new(Statement {
                    kind: StatementKind::Throw(string("boom")),
                    span: span(),
                }),
                alternate: Some(Box::new(Statement {
                    kind: StatementKind::Return(Some(number(42.0))),
                    span: span(),
                })),
            },
            span: span(),
        }];
        let captures = Vec::<CapturedBinding>::new();
        assert_eq!(
            infer_function_return_type(&function(body), &HashMap::new(), &captures),
            ValueType::Number
        );
    }

    #[test]
    fn unreachable_return_after_throw_is_ignored() {
        let body = vec![
            Statement {
                kind: StatementKind::Throw(string("boom")),
                span: span(),
            },
            Statement {
                kind: StatementKind::Return(Some(number(1.0))),
                span: span(),
            },
        ];
        let captures = Vec::<CapturedBinding>::new();
        assert_eq!(
            infer_function_return_type(&function(body), &HashMap::new(), &captures),
            ValueType::Undefined
        );
    }

    #[test]
    fn exhaustive_switch_can_seed_normal_return_type() {
        let body = vec![Statement {
            kind: StatementKind::Switch {
                discriminant: number(0.0),
                cases: vec![
                    ecmora_hir::SwitchCase {
                        test: Some(number(0.0)),
                        consequent: vec![Statement {
                            kind: StatementKind::Throw(string("zero")),
                            span: span(),
                        }],
                        span: span(),
                    },
                    ecmora_hir::SwitchCase {
                        test: None,
                        consequent: vec![Statement {
                            kind: StatementKind::Return(Some(number(7.0))),
                            span: span(),
                        }],
                        span: span(),
                    },
                ],
            },
            span: span(),
        }];
        let captures = Vec::<CapturedBinding>::new();
        assert_eq!(
            infer_function_return_type(&function(body), &HashMap::new(), &captures),
            ValueType::Number
        );
    }

    #[test]
    fn direct_throw_scan_skips_nested_functions() {
        let nested = function(vec![Statement {
            kind: StatementKind::Throw(string("nested")),
            span: span(),
        }]);
        let outer = function(vec![Statement {
            kind: StatementKind::FunctionDeclaration(nested),
            span: span(),
        }]);
        assert!(!function_contains_direct_throw(&outer));
    }
}
