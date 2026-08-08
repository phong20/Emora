use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, Expression, ExpressionKind,
    ForInit, Function as HirFunction, LogicalOperator, MemberProperty, ObjectEntry,
    Program as HirProgram, Statement, StatementKind, UnaryOperator, UpdateOperator, VariableKind,
};
use ecmora_ir::{
    BasicBlock, BinaryNumberOperator, BlockId, Builtin, CallArgument, CompareNumberOperator,
    DynamicBinaryOperator, DynamicUnaryOperator, Function, Instruction, Parameter, Program,
    Terminator, UnaryBoolOperator, UnaryNumberOperator, ValueId, ValueType,
};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
struct Binding {
    kind: VariableKind,
    initialized: bool,
    cell: ValueId,
    /// Flow-refined concrete value type stored in the cell. `Dynamic` means
    /// multiple tags can reach the current program point.
    value_type: ValueType,
}

#[derive(Debug)]
struct PendingBlock {
    name: String,
    instructions: Vec<Instruction>,
    terminator: Option<Terminator>,
}

#[derive(Debug, Clone)]
struct ControlTarget {
    label: Option<String>,
    break_target: BlockId,
    continue_target: Option<BlockId>,
}

#[derive(Debug)]
struct GenericLowerer {
    next_value: u32,
    blocks: Vec<PendingBlock>,
    current: usize,
    scopes: Vec<HashMap<String, Binding>>,
    strict: bool,
    function_mode: bool,
    generated_functions: Vec<Function>,
    next_function: u32,
    controls: Vec<ControlTarget>,
}

type Lowered = (ValueId, ValueType);

pub(super) fn requires_generic_callable_lowering(program: &HirProgram) -> bool {
    let top_level_functions = direct_function_names(&program.statements);
    program
        .statements
        .iter()
        .any(|statement| statement_requires_generic_with_functions(statement, &top_level_functions))
        || scope_uses_runtime_callable_values(&program.statements)
}

pub(super) fn analyze(program: &HirProgram) -> Result<Program> {
    if program
        .statements
        .iter()
        .any(statement_contains_async_or_generator)
    {
        bail!("generic callable ABI hiện chỉ nhận synchronous functions")
    }

    let mut lowerer = GenericLowerer::new(program.strict, false);
    lowerer.lower_scope(&program.statements)?;
    if lowerer.blocks[lowerer.current].terminator.is_none() {
        lowerer.set_terminator(Terminator::ReturnI32(0));
    }

    let blocks = lowerer.finish_blocks(Terminator::ReturnI32(0));
    let mut functions = vec![Function {
        name: "main".to_owned(),
        parameters: Vec::new(),
        captures: Vec::new(),
        return_type: None,
        blocks,
    }];
    functions.append(&mut lowerer.generated_functions);
    crate::finalize_native_program(Program { functions })
}

impl GenericLowerer {
    fn new(strict: bool, function_mode: bool) -> Self {
        Self {
            next_value: 0,
            blocks: vec![PendingBlock {
                name: "entry".to_owned(),
                instructions: Vec::new(),
                terminator: None,
            }],
            current: 0,
            scopes: vec![HashMap::new()],
            strict,
            function_mode,
            generated_functions: Vec::new(),
            next_function: 0,
            controls: Vec::new(),
        }
    }

    fn new_value(&mut self) -> ValueId {
        let value = ValueId(self.next_value);
        self.next_value += 1;
        value
    }

    fn emit(&mut self, instruction: Instruction) {
        self.blocks[self.current].instructions.push(instruction);
    }

    fn set_terminator(&mut self, terminator: Terminator) {
        self.blocks[self.current].terminator = Some(terminator);
    }

    fn new_block(&mut self, name: impl Into<String>) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(PendingBlock {
            name: name.into(),
            instructions: Vec::new(),
            terminator: None,
        });
        id
    }

    fn finish_blocks(&mut self, fallback: Terminator) -> Vec<BasicBlock> {
        std::mem::take(&mut self.blocks)
            .into_iter()
            .map(|block| BasicBlock {
                name: block.name,
                instructions: block.instructions,
                terminator: block.terminator.unwrap_or_else(|| match &fallback {
                    Terminator::ReturnI32(value) => Terminator::ReturnI32(*value),
                    Terminator::Unreachable => Terminator::Unreachable,
                    _ => Terminator::Unreachable,
                }),
            })
            .collect()
    }

    fn join_type(left: ValueType, right: ValueType) -> ValueType {
        if left == right {
            left
        } else {
            ValueType::Dynamic
        }
    }

    fn snapshot_scopes(&self) -> Vec<HashMap<String, Binding>> {
        self.scopes.clone()
    }

    fn merge_scope_states(
        base: &[HashMap<String, Binding>],
        left: &[HashMap<String, Binding>],
        right: &[HashMap<String, Binding>],
        left_reaches: bool,
        right_reaches: bool,
    ) -> Vec<HashMap<String, Binding>> {
        if left_reaches && !right_reaches {
            return left.to_vec();
        }
        if right_reaches && !left_reaches {
            return right.to_vec();
        }
        if !left_reaches && !right_reaches {
            return base.to_vec();
        }

        let mut merged = base.to_vec();
        for (scope_index, scope) in merged.iter_mut().enumerate() {
            for (name, binding) in scope.iter_mut() {
                let fallback = (binding.initialized, binding.value_type);
                let left_state = left
                    .get(scope_index)
                    .and_then(|scope| scope.get(name))
                    .map(|binding| (binding.initialized, binding.value_type))
                    .unwrap_or(fallback);
                let right_state = right
                    .get(scope_index)
                    .and_then(|scope| scope.get(name))
                    .map(|binding| (binding.initialized, binding.value_type))
                    .unwrap_or(fallback);
                binding.initialized = left_state.0 && right_state.0;
                binding.value_type = Self::join_type(left_state.1, right_state.1);
            }
        }
        merged
    }

    fn is_number_coercible(value_type: ValueType) -> bool {
        matches!(
            value_type,
            ValueType::Undefined
                | ValueType::Null
                | ValueType::Number
                | ValueType::Bool
                | ValueType::String
        )
    }

    fn infer_expression_type(&self, expression: &Expression) -> ValueType {
        match &expression.kind {
            ExpressionKind::String(_) => ValueType::String,
            ExpressionKind::Number(_) => ValueType::Number,
            ExpressionKind::BigInt(_) => ValueType::Dynamic,
            ExpressionKind::Bool(_) => ValueType::Bool,
            ExpressionKind::Null => ValueType::Null,
            ExpressionKind::This => ValueType::Dynamic,
            ExpressionKind::Global(name) => self
                .find_binding(name)
                .filter(|binding| binding.initialized)
                .map(|binding| binding.value_type)
                .unwrap_or_else(|| match name.as_str() {
                    "undefined" => ValueType::Undefined,
                    "NaN" | "Infinity" => ValueType::Number,
                    _ => ValueType::Dynamic,
                }),
            ExpressionKind::Member { .. }
            | ExpressionKind::Call { .. }
            | ExpressionKind::New { .. }
            | ExpressionKind::Await(_) => ValueType::Dynamic,
            ExpressionKind::Object(_) | ExpressionKind::Array(_) => ValueType::Object,
            ExpressionKind::Function(_) => ValueType::Callable,
            ExpressionKind::Conditional {
                consequent,
                alternate,
                ..
            } => Self::join_type(
                self.infer_expression_type(consequent),
                self.infer_expression_type(alternate),
            ),
            ExpressionKind::Logical { left, right, .. } => Self::join_type(
                self.infer_expression_type(left),
                self.infer_expression_type(right),
            ),
            ExpressionKind::Unary { operator, .. } => match operator {
                UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitwiseNot => {
                    ValueType::Number
                }
                UnaryOperator::Not | UnaryOperator::Delete => ValueType::Bool,
                UnaryOperator::Typeof => ValueType::String,
                UnaryOperator::Void => ValueType::Undefined,
            },
            ExpressionKind::Binary {
                left,
                operator,
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
                | BinaryOperator::InstanceOf => ValueType::Bool,
                BinaryOperator::Add => {
                    let left = self.infer_expression_type(left);
                    let right = self.infer_expression_type(right);
                    if left == ValueType::String || right == ValueType::String {
                        if left != ValueType::Dynamic && right != ValueType::Dynamic {
                            ValueType::String
                        } else {
                            ValueType::Dynamic
                        }
                    } else if Self::is_number_coercible(left) && Self::is_number_coercible(right) {
                        ValueType::Number
                    } else {
                        ValueType::Dynamic
                    }
                }
                _ => ValueType::Number,
            },
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => {
                let right = self.infer_expression_type(value);
                if *operator == AssignmentOperator::Assign {
                    right
                } else if *operator == AssignmentOperator::Add {
                    let left = match target {
                        AssignmentTarget::Identifier(name) => self
                            .find_binding(name)
                            .map(|binding| binding.value_type)
                            .unwrap_or(ValueType::Dynamic),
                        AssignmentTarget::Member { .. } => ValueType::Dynamic,
                    };
                    if left == ValueType::String || right == ValueType::String {
                        if left != ValueType::Dynamic && right != ValueType::Dynamic {
                            ValueType::String
                        } else {
                            ValueType::Dynamic
                        }
                    } else if Self::is_number_coercible(left) && Self::is_number_coercible(right) {
                        ValueType::Number
                    } else {
                        ValueType::Dynamic
                    }
                } else {
                    ValueType::Number
                }
            }
            ExpressionKind::Update { .. } => ValueType::Number,
        }
    }

    fn record_loop_write(
        writes: &mut HashMap<String, ValueType>,
        name: &str,
        value_type: ValueType,
    ) {
        writes
            .entry(name.to_owned())
            .and_modify(|existing| *existing = Self::join_type(*existing, value_type))
            .or_insert(value_type);
    }

    fn collect_expression_writes(
        &self,
        expression: &Expression,
        writes: &mut HashMap<String, ValueType>,
    ) {
        match &expression.kind {
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => {
                self.collect_expression_writes(value, writes);
                match target {
                    AssignmentTarget::Identifier(name) => {
                        let value_type = if *operator == AssignmentOperator::Assign {
                            self.infer_expression_type(value)
                        } else {
                            self.infer_expression_type(expression)
                        };
                        Self::record_loop_write(writes, name, value_type);
                    }
                    AssignmentTarget::Member { object, property } => {
                        self.collect_expression_writes(object, writes);
                        if let MemberProperty::Computed(key) = property {
                            self.collect_expression_writes(key, writes);
                        }
                    }
                }
            }
            ExpressionKind::Update { target, .. } => match target {
                AssignmentTarget::Identifier(name) => {
                    Self::record_loop_write(writes, name, ValueType::Number);
                }
                AssignmentTarget::Member { object, property } => {
                    self.collect_expression_writes(object, writes);
                    if let MemberProperty::Computed(key) = property {
                        self.collect_expression_writes(key, writes);
                    }
                }
            },
            ExpressionKind::Member { object, property } => {
                self.collect_expression_writes(object, writes);
                if let MemberProperty::Computed(key) = property {
                    self.collect_expression_writes(key, writes);
                }
            }
            ExpressionKind::Object(entries) => {
                for entry in entries {
                    match entry {
                        ObjectEntry::Property(property) => {
                            self.collect_expression_writes(&property.value, writes);
                            if let MemberProperty::Computed(key) = &property.key {
                                self.collect_expression_writes(key, writes);
                            }
                        }
                        ObjectEntry::Spread(value) => {
                            self.collect_expression_writes(value, writes);
                        }
                        ObjectEntry::Accessor { .. } => {}
                    }
                }
            }
            ExpressionKind::Array(elements) => {
                for element in elements {
                    match element {
                        ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                            self.collect_expression_writes(value, writes);
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
                self.collect_expression_writes(test, writes);
                self.collect_expression_writes(consequent, writes);
                self.collect_expression_writes(alternate, writes);
            }
            ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
                self.collect_expression_writes(argument, writes);
            }
            ExpressionKind::Binary { left, right, .. }
            | ExpressionKind::Logical { left, right, .. } => {
                self.collect_expression_writes(left, writes);
                self.collect_expression_writes(right, writes);
            }
            ExpressionKind::Call { callee, arguments }
            | ExpressionKind::New { callee, arguments } => {
                self.collect_expression_writes(callee, writes);
                for argument in arguments {
                    self.collect_expression_writes(argument, writes);
                }
            }
            ExpressionKind::Function(_)
            | ExpressionKind::String(_)
            | ExpressionKind::Number(_)
            | ExpressionKind::BigInt(_)
            | ExpressionKind::Bool(_)
            | ExpressionKind::Null
            | ExpressionKind::This
            | ExpressionKind::Global(_) => {}
        }
    }

    fn collect_statement_writes(
        &self,
        statement: &Statement,
        writes: &mut HashMap<String, ValueType>,
    ) {
        match &statement.kind {
            StatementKind::Expression(value) | StatementKind::Throw(value) => {
                self.collect_expression_writes(value, writes);
            }
            StatementKind::VariableDeclaration { declarations, .. } => {
                for declaration in declarations {
                    if let Some(value) = &declaration.init {
                        self.collect_expression_writes(value, writes);
                    }
                }
            }
            StatementKind::Block(statements) => {
                for statement in statements {
                    self.collect_statement_writes(statement, writes);
                }
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => {
                self.collect_expression_writes(test, writes);
                self.collect_statement_writes(consequent, writes);
                if let Some(alternate) = alternate {
                    self.collect_statement_writes(alternate, writes);
                }
            }
            StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
                self.collect_expression_writes(test, writes);
                self.collect_statement_writes(body, writes);
            }
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => {
                if let Some(init) = init {
                    match init {
                        ForInit::Expression(value) => {
                            self.collect_expression_writes(value, writes);
                        }
                        ForInit::VariableDeclaration { declarations, .. } => {
                            for declaration in declarations {
                                if let Some(value) = &declaration.init {
                                    self.collect_expression_writes(value, writes);
                                }
                            }
                        }
                    }
                }
                if let Some(test) = test {
                    self.collect_expression_writes(test, writes);
                }
                if let Some(update) = update {
                    self.collect_expression_writes(update, writes);
                }
                self.collect_statement_writes(body, writes);
            }
            StatementKind::Return(value) => {
                if let Some(value) = value {
                    self.collect_expression_writes(value, writes);
                }
            }
            StatementKind::Labeled { body, .. } => {
                self.collect_statement_writes(body, writes);
            }
            StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
                self.collect_expression_writes(right, writes);
                self.collect_statement_writes(body, writes);
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => {
                self.collect_expression_writes(discriminant, writes);
                for case in cases {
                    if let Some(test) = &case.test {
                        self.collect_expression_writes(test, writes);
                    }
                    for statement in &case.consequent {
                        self.collect_statement_writes(statement, writes);
                    }
                }
            }
            StatementKind::Empty
            | StatementKind::Debugger
            | StatementKind::FunctionDeclaration(_)
            | StatementKind::Break(_)
            | StatementKind::Continue(_)
            | StatementKind::Try { .. } => {}
        }
    }

    fn widen_loop_types(
        &mut self,
        body: &Statement,
        test: Option<&Expression>,
        update: Option<&Expression>,
    ) {
        let mut writes = HashMap::new();
        self.collect_statement_writes(body, &mut writes);
        if let Some(test) = test {
            self.collect_expression_writes(test, &mut writes);
        }
        if let Some(update) = update {
            self.collect_expression_writes(update, &mut writes);
        }
        for (name, written_type) in writes {
            if let Some(binding) = self.find_binding_mut(&name) {
                binding.value_type = Self::join_type(binding.value_type, written_type);
            }
        }
    }

    fn coerce_to_number(&mut self, value: Lowered) -> Option<Lowered> {
        if value.1 == ValueType::Number {
            return Some(value);
        }
        if !Self::is_number_coercible(value.1) {
            return None;
        }
        let result = self.new_value();
        self.emit(Instruction::ToNumber {
            result,
            operand: value.0,
            operand_type: value.1,
        });
        Some((result, ValueType::Number))
    }

    fn invert_bool(&mut self, value: ValueId) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::UnaryBool {
            result,
            operator: UnaryBoolOperator::Not,
            operand: value,
        });
        (result, ValueType::Bool)
    }

    fn const_undefined(&mut self) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::ConstUndefined { result });
        (result, ValueType::Undefined)
    }

    fn const_null(&mut self) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::ConstNull { result });
        (result, ValueType::Null)
    }

    fn const_bool(&mut self, value: bool) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::ConstBool { result, value });
        (result, ValueType::Bool)
    }

    fn const_number(&mut self, value: f64) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::ConstNumber { result, value });
        (result, ValueType::Number)
    }

    fn const_string(&mut self, value: impl Into<String>) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::ConstString {
            result,
            value: value.into(),
        });
        (result, ValueType::String)
    }

    fn create_cell(&mut self, initial: Lowered) -> ValueId {
        let result = self.new_value();
        self.emit(Instruction::CellNew {
            result,
            value: initial.0,
            value_type: initial.1,
        });
        result
    }

    fn read_cell(&mut self, cell: ValueId, value_type: ValueType) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::CellGet {
            result,
            cell,
            value_type,
        });
        (result, value_type)
    }

    fn write_cell(&mut self, cell: ValueId, value: Lowered) {
        self.emit(Instruction::CellSet {
            cell,
            value: value.0,
            value_type: value.1,
        });
    }

    fn find_binding(&self, name: &str) -> Option<&Binding> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name))
    }

    fn find_binding_mut(&mut self, name: &str) -> Option<&mut Binding> {
        self.scopes
            .iter_mut()
            .rev()
            .find_map(|scope| scope.get_mut(name))
    }

    fn lookup(&mut self, name: &str) -> Result<Lowered> {
        if let Some(binding) = self.find_binding(name).cloned() {
            if !binding.initialized {
                bail!("identifier `{name}` đang ở Temporal Dead Zone")
            }
            return Ok(self.read_cell(binding.cell, binding.value_type));
        }
        match name {
            "undefined" => Ok(self.const_undefined()),
            "NaN" => Ok(self.const_number(f64::NAN)),
            "Infinity" => Ok(self.const_number(f64::INFINITY)),
            _ => bail!("identifier `{name}` chưa được khai báo trong generic callable path"),
        }
    }

    fn lower_scope(&mut self, statements: &[Statement]) -> Result<()> {
        self.predeclare(statements)?;
        for statement in statements {
            if self.blocks[self.current].terminator.is_some() {
                break;
            }
            self.lower_statement(statement)?;
        }
        Ok(())
    }

    fn predeclare(&mut self, statements: &[Statement]) -> Result<()> {
        let mut declarations = Vec::<(String, VariableKind)>::new();
        let mut functions = Vec::<HirFunction>::new();

        for statement in statements {
            match &statement.kind {
                StatementKind::VariableDeclaration {
                    kind,
                    declarations: vars,
                } => {
                    declarations.extend(
                        vars.iter()
                            .map(|declaration| (declaration.name.clone(), *kind)),
                    );
                }
                StatementKind::FunctionDeclaration(function) => {
                    let name = function
                        .name
                        .clone()
                        .ok_or_else(|| anyhow::anyhow!("function declaration thiếu tên"))?;
                    declarations.push((name, VariableKind::Var));
                    functions.push(function.clone());
                }
                _ => {}
            }
        }

        for (name, kind) in declarations {
            if self.scopes.last().unwrap().contains_key(&name) {
                bail!("identifier `{name}` được khai báo trùng trong cùng scope")
            }
            let undefined = self.const_undefined();
            let cell = self.create_cell(undefined);
            self.scopes.last_mut().unwrap().insert(
                name,
                Binding {
                    kind,
                    initialized: false,
                    cell,
                    value_type: ValueType::Undefined,
                },
            );
        }

        // All function cells exist before any closure is created. Mutual
        // recursion therefore captures cells, never a placeholder function.
        for function in functions {
            let name = function.name.clone().unwrap();
            let closure = self.lower_function_value(&function)?;
            let cell = self.find_binding(&name).unwrap().cell;
            self.write_cell(cell, closure);
            let binding = self.find_binding_mut(&name).unwrap();
            binding.initialized = true;
            binding.value_type = closure.1;
        }

        Ok(())
    }

    fn lower_statement(&mut self, statement: &Statement) -> Result<()> {
        match &statement.kind {
            StatementKind::Empty | StatementKind::Debugger => Ok(()),
            StatementKind::Expression(expression) => {
                self.lower_expression(expression)?;
                Ok(())
            }
            StatementKind::VariableDeclaration { kind, declarations } => {
                for declaration in declarations {
                    let value = declaration
                        .init
                        .as_ref()
                        .map(|expression| self.lower_expression(expression))
                        .transpose()?
                        .unwrap_or_else(|| self.const_undefined());
                    let binding =
                        self.find_binding(&declaration.name)
                            .cloned()
                            .ok_or_else(|| {
                                anyhow::anyhow!("binding `{}` chưa predeclare", declaration.name)
                            })?;
                    self.write_cell(binding.cell, value);
                    let binding = self.find_binding_mut(&declaration.name).unwrap();
                    binding.kind = *kind;
                    binding.initialized = true;
                    binding.value_type = value.1;
                }
                Ok(())
            }
            StatementKind::FunctionDeclaration(_) => Ok(()),
            StatementKind::Block(statements) => {
                self.scopes.push(HashMap::new());
                let result = self.lower_scope(statements);
                self.scopes.pop();
                result
            }
            StatementKind::If {
                test,
                consequent,
                alternate,
            } => self.lower_if(test, consequent, alternate.as_deref()),
            StatementKind::While { test, body } => self.lower_while(test, body, None),
            StatementKind::DoWhile { body, test } => self.lower_do_while(body, test, None),
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => self.lower_for(init.as_ref(), test.as_ref(), update.as_ref(), body, None),
            StatementKind::Return(value) => {
                if !self.function_mode {
                    bail!("return ngoài function")
                }
                let value = value
                    .as_ref()
                    .map(|expression| self.lower_expression(expression))
                    .transpose()?
                    .unwrap_or_else(|| self.const_undefined());
                self.set_terminator(Terminator::ReturnValue {
                    value: value.0,
                    value_type: value.1,
                });
                Ok(())
            }
            StatementKind::Throw(value) => {
                let value = self.lower_expression(value)?;
                self.set_terminator(Terminator::ThrowValue {
                    value: value.0,
                    value_type: value.1,
                });
                Ok(())
            }
            StatementKind::Break(label) => {
                let target = self.resolve_control(label.as_deref(), false)?;
                self.set_terminator(Terminator::Jump(target));
                Ok(())
            }
            StatementKind::Continue(label) => {
                let target = self.resolve_control(label.as_deref(), true)?;
                self.set_terminator(Terminator::Jump(target));
                Ok(())
            }
            StatementKind::Labeled { label, body } => match &body.kind {
                StatementKind::While { test, body } => self.lower_while(test, body, Some(label)),
                StatementKind::DoWhile { body, test } => {
                    self.lower_do_while(body, test, Some(label))
                }
                StatementKind::For {
                    init,
                    test,
                    update,
                    body,
                } => self.lower_for(
                    init.as_ref(),
                    test.as_ref(),
                    update.as_ref(),
                    body,
                    Some(label),
                ),
                _ => self.lower_labeled_block(label, body),
            },
            StatementKind::ForIn { .. } | StatementKind::ForOf { .. } => {
                bail!("generic callable path chưa hạ iterator protocol")
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => self.lower_switch(discriminant, cases),
            StatementKind::Try { .. } => {
                bail!("generic callable path chưa hạ try/catch/finally LLVM completion")
            }
        }
    }

    fn resolve_control(&self, label: Option<&str>, want_continue: bool) -> Result<BlockId> {
        for target in self.controls.iter().rev() {
            if label.is_some() && target.label.as_deref() != label {
                continue;
            }
            if want_continue {
                if let Some(continue_target) = target.continue_target {
                    return Ok(continue_target);
                }
            } else {
                return Ok(target.break_target);
            }
        }
        bail!(
            "{} target không tồn tại",
            if want_continue { "continue" } else { "break" }
        )
    }

    fn lower_if(
        &mut self,
        test: &Expression,
        consequent: &Statement,
        alternate: Option<&Statement>,
    ) -> Result<()> {
        let condition_value = self.lower_expression(test)?;
        let condition = self.to_boolean(condition_value)?;
        let then_block = self.new_block("generic.if.then");
        let else_block = self.new_block("generic.if.else");
        let merge_block = self.new_block("generic.if.merge");
        self.set_terminator(Terminator::Branch {
            condition,
            then_block,
            else_block,
        });

        let base_state = self.snapshot_scopes();

        self.current = then_block.0 as usize;
        self.scopes = base_state.clone();
        self.lower_statement(consequent)?;
        let then_reaches = self.blocks[self.current].terminator.is_none();
        let then_state = self.snapshot_scopes();
        if then_reaches {
            self.set_terminator(Terminator::Jump(merge_block));
        }

        self.current = else_block.0 as usize;
        self.scopes = base_state.clone();
        if let Some(alternate) = alternate {
            self.lower_statement(alternate)?;
        }
        let else_reaches = self.blocks[self.current].terminator.is_none();
        let else_state = self.snapshot_scopes();
        if else_reaches {
            self.set_terminator(Terminator::Jump(merge_block));
        }

        self.scopes = Self::merge_scope_states(
            &base_state,
            &then_state,
            &else_state,
            then_reaches,
            else_reaches,
        );
        self.current = merge_block.0 as usize;
        if !then_reaches && !else_reaches {
            self.set_terminator(Terminator::Unreachable);
        }
        Ok(())
    }

    /// General generator runtime switch invariant:
    ///
    /// generator_cfg emits one outer `while (true) { switch (frame.pc) {...} }`
    /// dispatcher. Lower it to explicit IR CFG exactly once; never recursively
    /// macro-expand it through static_graph.
    fn lower_switch(
        &mut self,
        discriminant: &Expression,
        cases: &[ecmora_hir::SwitchCase],
    ) -> Result<()> {
        if cases
            .iter()
            .flat_map(|case| &case.consequent)
            .any(|statement| {
                matches!(
                    &statement.kind,
                    StatementKind::VariableDeclaration { .. }
                        | StatementKind::FunctionDeclaration(_)
                )
            })
        {
            bail!(
                "generic switch with direct lexical declarations needs shared CaseBlock TDZ lowering"
            )
        }

        // Any outer mutable cell written by a case must have one representation
        // valid for every dispatch/fallthrough path.
        let mut writes = HashMap::new();
        for case in cases {
            if let Some(test) = &case.test {
                self.collect_expression_writes(test, &mut writes);
            }
            for statement in &case.consequent {
                self.collect_statement_writes(statement, &mut writes);
            }
        }
        for (name, written_type) in writes {
            if let Some(binding) = self.find_binding_mut(&name) {
                binding.value_type = Self::join_type(binding.value_type, written_type);
            }
        }

        let discriminant = self.lower_expression(discriminant)?;
        let exit = self.new_block("generic.switch.exit");
        let case_blocks = (0..cases.len())
            .map(|index| self.new_block(format!("generic.switch.case.{index}")))
            .collect::<Vec<_>>();

        let default_target = cases
            .iter()
            .position(|case| case.test.is_none())
            .and_then(|index| case_blocks.get(index).copied())
            .unwrap_or(exit);

        let tested_cases = cases
            .iter()
            .enumerate()
            .filter_map(|(index, case)| case.test.as_ref().map(|test| (index, test)))
            .collect::<Vec<_>>();

        let test_blocks = tested_cases
            .iter()
            .enumerate()
            .map(|(order, _)| self.new_block(format!("generic.switch.test.{order}")))
            .collect::<Vec<_>>();

        let dispatch = test_blocks.first().copied().unwrap_or(default_target);
        self.set_terminator(Terminator::Jump(dispatch));

        // Case selectors are evaluated in source order. `default` is the
        // final no-match target even when it appears in the middle.
        for (order, ((case_index, test), test_block)) in
            tested_cases.iter().zip(test_blocks.iter()).enumerate()
        {
            self.current = test_block.0 as usize;
            let test_value = self.lower_expression(test)?;
            let equal = self.emit_dynamic_binary(
                DynamicBinaryOperator::StrictEqual,
                discriminant,
                test_value,
            );
            let condition = self.to_boolean(equal)?;
            let miss = test_blocks
                .get(order + 1)
                .copied()
                .unwrap_or(default_target);

            self.set_terminator(Terminator::Branch {
                condition,
                then_block: case_blocks[*case_index],
                else_block: miss,
            });
        }

        let base_state = self.snapshot_scopes();
        self.controls.push(ControlTarget {
            label: None,
            break_target: exit,
            continue_target: None,
        });

        for (index, case) in cases.iter().enumerate() {
            self.current = case_blocks[index].0 as usize;
            self.scopes = base_state.clone();

            for statement in &case.consequent {
                if self.blocks[self.current].terminator.is_some() {
                    break;
                }
                self.lower_statement(statement)?;
            }

            if self.blocks[self.current].terminator.is_none() {
                let fallthrough = case_blocks.get(index + 1).copied().unwrap_or(exit);
                self.set_terminator(Terminator::Jump(fallthrough));
            }
        }

        self.controls.pop();
        self.current = exit.0 as usize;
        self.scopes = base_state;
        Ok(())
    }

    /// completion_native erases try/catch/finally into labeled CFG regions.
    fn lower_labeled_block(&mut self, label: &str, body: &Statement) -> Result<()> {
        let exit = self.new_block(format!("generic.label.{label}.exit"));
        self.controls.push(ControlTarget {
            label: Some(label.to_owned()),
            break_target: exit,
            continue_target: None,
        });

        self.lower_statement(body)?;
        self.controls.pop();

        if self.blocks[self.current].terminator.is_none() {
            self.set_terminator(Terminator::Jump(exit));
        }

        self.current = exit.0 as usize;
        Ok(())
    }

    fn lower_while(
        &mut self,
        test: &Expression,
        body: &Statement,
        label: Option<&str>,
    ) -> Result<()> {
        self.widen_loop_types(body, Some(test), None);
        let header_state = self.snapshot_scopes();

        let header = self.new_block("generic.while.header");
        let body_block = self.new_block("generic.while.body");
        let exit = self.new_block("generic.while.exit");
        self.set_terminator(Terminator::Jump(header));

        self.current = header.0 as usize;
        self.scopes = header_state.clone();
        let condition_value = self.lower_expression(test)?;
        let condition = self.to_boolean(condition_value)?;
        self.set_terminator(Terminator::Branch {
            condition,
            then_block: body_block,
            else_block: exit,
        });

        self.current = body_block.0 as usize;
        self.scopes = header_state.clone();
        self.controls.push(ControlTarget {
            label: label.map(str::to_owned),
            break_target: exit,
            continue_target: Some(header),
        });
        self.lower_statement(body)?;
        self.controls.pop();
        if self.blocks[self.current].terminator.is_none() {
            self.set_terminator(Terminator::Jump(header));
        }

        self.current = exit.0 as usize;
        self.scopes = header_state;
        Ok(())
    }

    fn lower_do_while(
        &mut self,
        body: &Statement,
        test: &Expression,
        label: Option<&str>,
    ) -> Result<()> {
        self.widen_loop_types(body, Some(test), None);
        let header_state = self.snapshot_scopes();

        let body_block = self.new_block("generic.do.body");
        let test_block = self.new_block("generic.do.test");
        let exit = self.new_block("generic.do.exit");
        self.set_terminator(Terminator::Jump(body_block));

        self.current = body_block.0 as usize;
        self.scopes = header_state.clone();
        self.controls.push(ControlTarget {
            label: label.map(str::to_owned),
            break_target: exit,
            continue_target: Some(test_block),
        });
        self.lower_statement(body)?;
        self.controls.pop();
        if self.blocks[self.current].terminator.is_none() {
            self.set_terminator(Terminator::Jump(test_block));
        }

        self.current = test_block.0 as usize;
        let condition_value = self.lower_expression(test)?;
        let condition = self.to_boolean(condition_value)?;
        self.set_terminator(Terminator::Branch {
            condition,
            then_block: body_block,
            else_block: exit,
        });

        self.current = exit.0 as usize;
        self.scopes = header_state;
        Ok(())
    }

    fn lower_for(
        &mut self,
        init: Option<&ForInit>,
        test: Option<&Expression>,
        update: Option<&Expression>,
        body: &Statement,
        label: Option<&str>,
    ) -> Result<()> {
        self.scopes.push(HashMap::new());
        if let Some(init) = init {
            match init {
                ForInit::Expression(expression) => {
                    self.lower_expression(expression)?;
                }
                ForInit::VariableDeclaration { kind, declarations } => {
                    for declaration in declarations {
                        if self.scopes.last().unwrap().contains_key(&declaration.name) {
                            bail!("duplicate for binding `{}`", declaration.name)
                        }
                        let undefined = self.const_undefined();
                        let cell = self.create_cell(undefined);
                        self.scopes.last_mut().unwrap().insert(
                            declaration.name.clone(),
                            Binding {
                                kind: *kind,
                                initialized: false,
                                cell,
                                value_type: ValueType::Undefined,
                            },
                        );
                    }
                    for declaration in declarations {
                        let value = declaration
                            .init
                            .as_ref()
                            .map(|value| self.lower_expression(value))
                            .transpose()?
                            .unwrap_or_else(|| self.const_undefined());
                        let cell = self.find_binding(&declaration.name).unwrap().cell;
                        self.write_cell(cell, value);
                        let binding = self.find_binding_mut(&declaration.name).unwrap();
                        binding.initialized = true;
                        binding.value_type = value.1;
                    }
                }
            }
        }

        self.widen_loop_types(body, test, update);
        let header_state = self.snapshot_scopes();

        let header = self.new_block("generic.for.header");
        let body_block = self.new_block("generic.for.body");
        let update_block = self.new_block("generic.for.update");
        let exit = self.new_block("generic.for.exit");
        self.set_terminator(Terminator::Jump(header));

        self.current = header.0 as usize;
        self.scopes = header_state.clone();
        let condition = match test {
            Some(test) => {
                let value = self.lower_expression(test)?;
                self.to_boolean(value)?
            }
            None => self.const_bool(true).0,
        };
        self.set_terminator(Terminator::Branch {
            condition,
            then_block: body_block,
            else_block: exit,
        });

        self.current = body_block.0 as usize;
        self.scopes = header_state.clone();
        self.controls.push(ControlTarget {
            label: label.map(str::to_owned),
            break_target: exit,
            continue_target: Some(update_block),
        });
        self.lower_statement(body)?;
        self.controls.pop();
        if self.blocks[self.current].terminator.is_none() {
            self.set_terminator(Terminator::Jump(update_block));
        }

        self.current = update_block.0 as usize;
        if let Some(update) = update {
            self.lower_expression(update)?;
        }
        if self.blocks[self.current].terminator.is_none() {
            self.set_terminator(Terminator::Jump(header));
        }

        self.current = exit.0 as usize;
        self.scopes = header_state;
        self.scopes.pop();
        Ok(())
    }

    fn to_boolean(&mut self, value: Lowered) -> Result<ValueId> {
        if value.1 == ValueType::Bool {
            return Ok(value.0);
        }
        let result = self.new_value();
        self.emit(Instruction::ToBoolean {
            result,
            operand: value.0,
            operand_type: value.1,
        });
        Ok(result)
    }

    fn emit_unary_value(&mut self, operator: UnaryOperator, operand: Lowered) -> Lowered {
        match operator {
            UnaryOperator::Not => {
                let boolean = self
                    .to_boolean(operand)
                    .expect("ToBoolean lowering cannot fail");
                self.invert_bool(boolean)
            }
            UnaryOperator::Typeof => {
                let text = match operand.1 {
                    ValueType::Undefined => Some("undefined"),
                    ValueType::Null | ValueType::Object | ValueType::Promise | ValueType::Cell => {
                        Some("object")
                    }
                    ValueType::Number => Some("number"),
                    ValueType::Bool => Some("boolean"),
                    ValueType::String => Some("string"),
                    ValueType::Callable => Some("function"),
                    ValueType::Dynamic => None,
                };
                if let Some(text) = text {
                    self.const_string(text)
                } else {
                    let result = self.new_value();
                    self.emit(Instruction::TypeOfDynamic {
                        result,
                        operand: operand.0,
                    });
                    (result, ValueType::String)
                }
            }
            UnaryOperator::Void => self.const_undefined(),
            UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitwiseNot => {
                if let Some(number) = self.coerce_to_number(operand) {
                    let result = self.new_value();
                    self.emit(Instruction::UnaryNumber {
                        result,
                        operator: match operator {
                            UnaryOperator::Plus => UnaryNumberOperator::Plus,
                            UnaryOperator::Minus => UnaryNumberOperator::Minus,
                            UnaryOperator::BitwiseNot => UnaryNumberOperator::BitwiseNot,
                            _ => unreachable!(),
                        },
                        operand: number.0,
                    });
                    (result, ValueType::Number)
                } else {
                    let result = self.new_value();
                    self.emit(Instruction::DynamicUnary {
                        result,
                        operator: map_unary(operator).expect("numeric unary mapping"),
                        operand: operand.0,
                        operand_type: operand.1,
                    });
                    (result, ValueType::Dynamic)
                }
            }
            UnaryOperator::Delete => unreachable!("delete handled before emit_unary_value"),
        }
    }

    fn emit_raw_dynamic_binary(
        &mut self,
        operator: DynamicBinaryOperator,
        left: Lowered,
        right: Lowered,
    ) -> Lowered {
        let result = self.new_value();
        self.emit(Instruction::DynamicBinary {
            result,
            operator,
            left: left.0,
            left_type: left.1,
            right: right.0,
            right_type: right.1,
        });
        (result, ValueType::Dynamic)
    }

    fn emit_number_binary(
        &mut self,
        operator: DynamicBinaryOperator,
        left: Lowered,
        right: Lowered,
    ) -> Option<Lowered> {
        let left = self.coerce_to_number(left)?;
        let right = self.coerce_to_number(right)?;
        let operator = map_number_binary(operator)?;
        let result = self.new_value();
        self.emit(Instruction::BinaryNumber {
            result,
            operator,
            left: left.0,
            right: right.0,
        });
        Some((result, ValueType::Number))
    }

    fn emit_number_compare(
        &mut self,
        operator: DynamicBinaryOperator,
        left: Lowered,
        right: Lowered,
    ) -> Option<Lowered> {
        let left = self.coerce_to_number(left)?;
        let right = self.coerce_to_number(right)?;
        let operator = map_number_compare(operator)?;
        let result = self.new_value();
        self.emit(Instruction::CompareNumber {
            result,
            operator,
            left: left.0,
            right: right.0,
        });
        Some((result, ValueType::Bool))
    }

    fn emit_known_equality(
        &mut self,
        operator: DynamicBinaryOperator,
        left: Lowered,
        right: Lowered,
    ) -> Option<Lowered> {
        let strict = matches!(
            operator,
            DynamicBinaryOperator::StrictEqual | DynamicBinaryOperator::StrictNotEqual
        );
        let negate = matches!(
            operator,
            DynamicBinaryOperator::NotEqual | DynamicBinaryOperator::StrictNotEqual
        );

        if left.1 == right.1 {
            return match left.1 {
                ValueType::Undefined | ValueType::Null => Some(self.const_bool(!negate)),
                ValueType::Number => self.emit_number_compare(operator, left, right),
                ValueType::String => {
                    let result = self.new_value();
                    self.emit(Instruction::CompareString {
                        result,
                        left: left.0,
                        right: right.0,
                    });
                    Some(if negate {
                        self.invert_bool(result)
                    } else {
                        (result, ValueType::Bool)
                    })
                }
                ValueType::Object => {
                    let result = self.new_value();
                    self.emit(Instruction::CompareObject {
                        result,
                        operator: if negate {
                            CompareNumberOperator::StrictNotEqual
                        } else {
                            CompareNumberOperator::StrictEqual
                        },
                        left: left.0,
                        right: right.0,
                    });
                    Some((result, ValueType::Bool))
                }
                ValueType::Bool
                | ValueType::Callable
                | ValueType::Cell
                | ValueType::Promise
                | ValueType::Dynamic => None,
            };
        }

        if strict && left.1 != ValueType::Dynamic && right.1 != ValueType::Dynamic {
            return Some(self.const_bool(negate));
        }

        let left_nullish = matches!(left.1, ValueType::Undefined | ValueType::Null);
        let right_nullish = matches!(right.1, ValueType::Undefined | ValueType::Null);
        if left_nullish || right_nullish {
            if left_nullish && right_nullish {
                return Some(self.const_bool(!negate));
            }
            if left.1 != ValueType::Dynamic && right.1 != ValueType::Dynamic {
                return Some(self.const_bool(negate));
            }
            return None;
        }

        let primitive_numeric = |value_type: ValueType| {
            matches!(
                value_type,
                ValueType::Number | ValueType::Bool | ValueType::String
            )
        };
        if !strict && primitive_numeric(left.1) && primitive_numeric(right.1) {
            return self.emit_number_compare(
                if negate {
                    DynamicBinaryOperator::NotEqual
                } else {
                    DynamicBinaryOperator::Equal
                },
                left,
                right,
            );
        }

        None
    }

    fn emit_dynamic_binary(
        &mut self,
        operator: DynamicBinaryOperator,
        left: Lowered,
        right: Lowered,
    ) -> Lowered {
        match operator {
            DynamicBinaryOperator::Add => {
                if left.1 != ValueType::String
                    && right.1 != ValueType::String
                    && Self::is_number_coercible(left.1)
                    && Self::is_number_coercible(right.1)
                {
                    if let Some(value) = self.emit_number_binary(operator, left, right) {
                        return value;
                    }
                }
            }
            DynamicBinaryOperator::Subtract
            | DynamicBinaryOperator::Multiply
            | DynamicBinaryOperator::Divide
            | DynamicBinaryOperator::Remainder
            | DynamicBinaryOperator::Exponential
            | DynamicBinaryOperator::ShiftLeft
            | DynamicBinaryOperator::ShiftRight
            | DynamicBinaryOperator::ShiftRightZeroFill
            | DynamicBinaryOperator::BitwiseOr
            | DynamicBinaryOperator::BitwiseXor
            | DynamicBinaryOperator::BitwiseAnd => {
                if Self::is_number_coercible(left.1) && Self::is_number_coercible(right.1) {
                    if let Some(value) = self.emit_number_binary(operator, left, right) {
                        return value;
                    }
                }
            }
            DynamicBinaryOperator::Equal
            | DynamicBinaryOperator::NotEqual
            | DynamicBinaryOperator::StrictEqual
            | DynamicBinaryOperator::StrictNotEqual => {
                if let Some(value) = self.emit_known_equality(operator, left, right) {
                    return value;
                }
            }
            DynamicBinaryOperator::LessThan
            | DynamicBinaryOperator::LessEqual
            | DynamicBinaryOperator::GreaterThan
            | DynamicBinaryOperator::GreaterEqual => {
                if !(left.1 == ValueType::String && right.1 == ValueType::String)
                    && Self::is_number_coercible(left.1)
                    && Self::is_number_coercible(right.1)
                {
                    if let Some(value) = self.emit_number_compare(operator, left, right) {
                        return value;
                    }
                }
            }
            DynamicBinaryOperator::In | DynamicBinaryOperator::InstanceOf => {}
        }
        self.emit_raw_dynamic_binary(operator, left, right)
    }

    fn lower_expression(&mut self, expression: &Expression) -> Result<Lowered> {
        match &expression.kind {
            ExpressionKind::String(value) => Ok(self.const_string(value.clone())),
            ExpressionKind::Number(value) => Ok(self.const_number(*value)),
            ExpressionKind::BigInt(_) => {
                bail!("BigInt chưa thuộc native generic callable numeric ABI")
            }
            ExpressionKind::Bool(value) => Ok(self.const_bool(*value)),
            ExpressionKind::Null => Ok(self.const_null()),
            ExpressionKind::This => {
                let result = self.new_value();
                self.emit(Instruction::CurrentThis { result });
                Ok((result, ValueType::Dynamic))
            }
            ExpressionKind::Global(name) => self.lookup(name),
            ExpressionKind::Member { object, property } => {
                let object = self.lower_expression(object)?;
                let key = self.property_key(property)?;
                let result = self.new_value();
                self.emit(Instruction::DynamicGet {
                    result,
                    object: object.0,
                    object_type: object.1,
                    key,
                });
                Ok((result, ValueType::Dynamic))
            }
            ExpressionKind::Object(entries) => self.lower_object(entries),
            ExpressionKind::Array(elements) => self.lower_array(elements),
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => self.lower_conditional(test, consequent, alternate),
            ExpressionKind::Unary { operator, argument } => {
                if *operator == UnaryOperator::Delete {
                    let ExpressionKind::Member { object, property } = &argument.kind else {
                        self.lower_expression(argument)?;
                        return Ok(self.const_bool(true));
                    };
                    let object = self.lower_expression(object)?;
                    let key = self.property_key(property)?;
                    let result = self.new_value();
                    self.emit(Instruction::DynamicDelete {
                        result,
                        object: object.0,
                        object_type: object.1,
                        key,
                    });
                    return Ok((result, ValueType::Bool));
                }
                let operand = self.lower_expression(argument)?;
                Ok(self.emit_unary_value(*operator, operand))
            }
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => {
                let left = self.lower_expression(left)?;
                let right = self.lower_expression(right)?;
                Ok(self.emit_dynamic_binary(map_binary(*operator), left, right))
            }
            ExpressionKind::Logical {
                left,
                operator,
                right,
            } => self.lower_logical(left, *operator, right),
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => self.lower_assignment(target, *operator, value),
            ExpressionKind::Update {
                target,
                operator,
                prefix,
            } => self.lower_update(target, *operator, *prefix),
            ExpressionKind::Call { callee, arguments } => self.lower_call(callee, arguments),
            ExpressionKind::New { callee, arguments } => {
                let callee = self.lower_expression(callee)?;
                let arguments = self.lower_call_arguments(arguments)?;
                let result = self.new_value();
                self.emit(Instruction::ConstructValue {
                    result,
                    callee: callee.0,
                    callee_type: callee.1,
                    arguments,
                });
                Ok((result, ValueType::Dynamic))
            }
            ExpressionKind::Function(function) => self.lower_function_value(function),
            ExpressionKind::Await(_) => {
                bail!("await chưa được nối vào generic callable continuation ABI")
            }
        }
    }

    fn lower_object(&mut self, entries: &[ObjectEntry]) -> Result<Lowered> {
        let result = self.new_value();
        self.emit(Instruction::ObjectNew { result });
        for entry in entries {
            match entry {
                ObjectEntry::Property(property) => {
                    let key = self.property_key(&property.key)?;
                    let value = self.lower_expression(&property.value)?;
                    self.emit(Instruction::ObjectSet {
                        object: result,
                        key,
                        value: value.0,
                        value_type: value.1,
                    });
                }
                ObjectEntry::Spread(_) => {
                    bail!("dynamic object spread chưa được hạ trong generic callable path")
                }
                ObjectEntry::Accessor { key, get, set } => {
                    let getter = get
                        .as_ref()
                        .map(|value| self.lower_expression(value))
                        .transpose()?;
                    let setter = set
                        .as_ref()
                        .map(|value| self.lower_expression(value))
                        .transpose()?;
                    if getter
                        .as_ref()
                        .is_some_and(|value| value.1 != ValueType::Callable)
                        || setter
                            .as_ref()
                            .is_some_and(|value| value.1 != ValueType::Callable)
                    {
                        bail!("accessor phải là callable")
                    }
                    self.emit(Instruction::ObjectDefineAccessor {
                        object: result,
                        key: key.clone(),
                        getter: getter.map(|value| value.0),
                        setter: setter.map(|value| value.0),
                        enumerable: true,
                        configurable: true,
                    });
                }
            }
        }
        Ok((result, ValueType::Object))
    }

    fn lower_array(&mut self, elements: &[ArrayElement]) -> Result<Lowered> {
        let array = self.new_value();
        self.emit(Instruction::ObjectNew { result: array });
        for element in elements {
            match element {
                ArrayElement::Expression(value) => {
                    let value = self.lower_expression(value)?;
                    self.emit(Instruction::ArrayPush {
                        array,
                        value: value.0,
                        value_type: value.1,
                    });
                }
                ArrayElement::Spread(value) => {
                    let value = self.lower_expression(value)?;
                    self.emit(Instruction::ArraySpread {
                        array,
                        iterable: value.0,
                        iterable_type: value.1,
                    });
                }
                ArrayElement::Hole => {
                    let value = self.const_undefined();
                    self.emit(Instruction::ArrayPush {
                        array,
                        value: value.0,
                        value_type: value.1,
                    });
                }
            }
        }
        Ok((array, ValueType::Object))
    }

    fn property_key(&mut self, property: &MemberProperty) -> Result<String> {
        match property {
            MemberProperty::Static(key) => Ok(key.clone()),
            MemberProperty::Computed(expression) => match &expression.kind {
                ExpressionKind::String(value) => Ok(value.clone()),
                ExpressionKind::Number(value) => Ok(value.to_string()),
                _ => bail!("computed property key động cần ToPropertyKey IR"),
            },
        }
    }

    fn lower_conditional(
        &mut self,
        test: &Expression,
        consequent: &Expression,
        alternate: &Expression,
    ) -> Result<Lowered> {
        let initial = self.const_undefined();
        let cell = self.create_cell(initial);
        let condition_value = self.lower_expression(test)?;
        let condition = self.to_boolean(condition_value)?;
        let then_block = self.new_block("generic.conditional.then");
        let else_block = self.new_block("generic.conditional.else");
        let merge = self.new_block("generic.conditional.merge");
        self.set_terminator(Terminator::Branch {
            condition,
            then_block,
            else_block,
        });

        let base_state = self.snapshot_scopes();

        self.current = then_block.0 as usize;
        self.scopes = base_state.clone();
        let then_value = self.lower_expression(consequent)?;
        self.write_cell(cell, then_value);
        let then_state = self.snapshot_scopes();
        let then_end = BlockId(self.current as u32);
        if self.blocks[self.current].terminator.is_none() {
            self.set_terminator(Terminator::Jump(merge));
        }

        self.current = else_block.0 as usize;
        self.scopes = base_state.clone();
        let else_value = self.lower_expression(alternate)?;
        self.write_cell(cell, else_value);
        let else_state = self.snapshot_scopes();
        let else_end = BlockId(self.current as u32);
        if self.blocks[self.current].terminator.is_none() {
            self.set_terminator(Terminator::Jump(merge));
        }

        let _ = (then_end, else_end);
        self.scopes = Self::merge_scope_states(&base_state, &then_state, &else_state, true, true);
        self.current = merge.0 as usize;
        let value_type = Self::join_type(then_value.1, else_value.1);
        Ok(self.read_cell(cell, value_type))
    }

    fn lower_logical(
        &mut self,
        left: &Expression,
        operator: LogicalOperator,
        right: &Expression,
    ) -> Result<Lowered> {
        let left = self.lower_expression(left)?;

        if matches!(operator, LogicalOperator::Nullish) {
            if matches!(left.1, ValueType::Null | ValueType::Undefined) {
                return self.lower_expression(right);
            }
            if left.1 != ValueType::Dynamic {
                return Ok(left);
            }
        }

        let cell = self.create_cell(left);
        let rhs_block = self.new_block("generic.logical.rhs");
        let short_block = self.new_block("generic.logical.short");
        let merge = self.new_block("generic.logical.merge");
        let base_state = self.snapshot_scopes();

        if matches!(operator, LogicalOperator::Nullish) {
            let null = self.const_null();
            let undefined = self.const_undefined();
            let left_null =
                self.emit_raw_dynamic_binary(DynamicBinaryOperator::StrictEqual, left, null);
            let left_undefined =
                self.emit_raw_dynamic_binary(DynamicBinaryOperator::StrictEqual, left, undefined);
            let nullish = self.emit_raw_dynamic_binary(
                DynamicBinaryOperator::BitwiseOr,
                left_null,
                left_undefined,
            );
            let condition = self.to_boolean(nullish)?;
            self.set_terminator(Terminator::Branch {
                condition,
                then_block: rhs_block,
                else_block: short_block,
            });
        } else {
            let condition = self.to_boolean(left)?;
            let (then_block, else_block) = match operator {
                LogicalOperator::Or => (short_block, rhs_block),
                LogicalOperator::And => (rhs_block, short_block),
                LogicalOperator::Nullish => unreachable!(),
            };
            self.set_terminator(Terminator::Branch {
                condition,
                then_block,
                else_block,
            });
        }

        self.current = short_block.0 as usize;
        self.scopes = base_state.clone();
        let short_state = self.snapshot_scopes();
        self.set_terminator(Terminator::Jump(merge));

        self.current = rhs_block.0 as usize;
        self.scopes = base_state.clone();
        let rhs = self.lower_expression(right)?;
        self.write_cell(cell, rhs);
        let rhs_state = self.snapshot_scopes();
        self.set_terminator(Terminator::Jump(merge));

        self.scopes = Self::merge_scope_states(&base_state, &short_state, &rhs_state, true, true);
        self.current = merge.0 as usize;
        let value_type = Self::join_type(left.1, rhs.1);
        Ok(self.read_cell(cell, value_type))
    }

    fn lower_assignment(
        &mut self,
        target: &AssignmentTarget,
        operator: AssignmentOperator,
        expression: &Expression,
    ) -> Result<Lowered> {
        if matches!(
            operator,
            AssignmentOperator::LogicalOr
                | AssignmentOperator::LogicalAnd
                | AssignmentOperator::LogicalNullish
        ) {
            bail!("generic logical assignment cần dedicated short-circuit IR")
        }

        match target {
            AssignmentTarget::Identifier(name) => {
                let binding = self
                    .find_binding(name)
                    .cloned()
                    .ok_or_else(|| anyhow::anyhow!("identifier `{name}` chưa được khai báo"))?;
                if binding.kind == VariableKind::Const && binding.initialized {
                    bail!("không thể gán lại const `{name}`")
                }
                let value = if operator == AssignmentOperator::Assign {
                    self.lower_expression(expression)?
                } else {
                    let old = self.read_cell(binding.cell, binding.value_type);
                    let right = self.lower_expression(expression)?;
                    self.emit_dynamic_binary(map_assignment(operator)?, old, right)
                };
                self.write_cell(binding.cell, value);
                let binding = self.find_binding_mut(name).unwrap();
                binding.initialized = true;
                binding.value_type = value.1;
                Ok(value)
            }
            AssignmentTarget::Member { object, property } => {
                let object = self.lower_expression(object)?;
                let key = self.property_key(property)?;
                let value = if operator == AssignmentOperator::Assign {
                    self.lower_expression(expression)?
                } else {
                    let old_result = self.new_value();
                    self.emit(Instruction::DynamicGet {
                        result: old_result,
                        object: object.0,
                        object_type: object.1,
                        key: key.clone(),
                    });
                    let right = self.lower_expression(expression)?;
                    self.emit_dynamic_binary(
                        map_assignment(operator)?,
                        (old_result, ValueType::Dynamic),
                        right,
                    )
                };
                self.emit(Instruction::DynamicSet {
                    object: object.0,
                    object_type: object.1,
                    key,
                    value: value.0,
                    value_type: value.1,
                });
                Ok(value)
            }
        }
    }

    fn lower_update(
        &mut self,
        target: &AssignmentTarget,
        operator: UpdateOperator,
        prefix: bool,
    ) -> Result<Lowered> {
        let one = self.const_number(1.0);
        let binary = if operator == UpdateOperator::Increment {
            DynamicBinaryOperator::Add
        } else {
            DynamicBinaryOperator::Subtract
        };
        match target {
            AssignmentTarget::Identifier(name) => {
                let binding = self
                    .find_binding(name)
                    .cloned()
                    .ok_or_else(|| anyhow::anyhow!("identifier `{name}` chưa được khai báo"))?;
                if binding.kind == VariableKind::Const {
                    bail!("không thể update const `{name}`")
                }
                let old = self.read_cell(binding.cell, binding.value_type);
                let new = self.emit_dynamic_binary(binary, old, one);
                self.write_cell(binding.cell, new);
                self.find_binding_mut(name).unwrap().value_type = new.1;
                Ok(if prefix { new } else { old })
            }
            AssignmentTarget::Member { object, property } => {
                let object = self.lower_expression(object)?;
                let key = self.property_key(property)?;
                let old_result = self.new_value();
                self.emit(Instruction::DynamicGet {
                    result: old_result,
                    object: object.0,
                    object_type: object.1,
                    key: key.clone(),
                });
                let old = (old_result, ValueType::Dynamic);
                let new = self.emit_dynamic_binary(binary, old, one);
                self.emit(Instruction::DynamicSet {
                    object: object.0,
                    object_type: object.1,
                    key,
                    value: new.0,
                    value_type: new.1,
                });
                Ok(if prefix { new } else { old })
            }
        }
    }

    fn lower_call(&mut self, callee: &Expression, arguments: &[Expression]) -> Result<Lowered> {
        if is_console_log(callee) {
            let lowered = self.lower_call_arguments(arguments)?;
            if lowered.iter().any(|argument| argument.spread) {
                bail!("console.log(...spread) chưa được hạ")
            }
            let values = lowered
                .iter()
                .map(|argument| argument.value)
                .collect::<Vec<_>>();
            self.emit(Instruction::CallBuiltin {
                builtin: Builtin::ConsoleLog,
                display_values: vec![None; values.len()],
                arguments: values,
            });
            return Ok(self.const_undefined());
        }

        if let ExpressionKind::Member { object, property } = &callee.kind {
            if let MemberProperty::Static(method) = property {
                match method.as_str() {
                    "call" => {
                        let target = self.lower_expression(object)?;
                        let receiver = arguments
                            .first()
                            .map(|value| self.lower_expression(value))
                            .transpose()?
                            .unwrap_or_else(|| self.const_undefined());
                        let call_arguments =
                            self.lower_call_arguments(arguments.get(1..).unwrap_or_default())?;
                        return Ok(self.emit_call_value(target, Some(receiver), call_arguments));
                    }
                    "apply" => {
                        let target = self.lower_expression(object)?;
                        let receiver = arguments
                            .first()
                            .map(|value| self.lower_expression(value))
                            .transpose()?
                            .unwrap_or_else(|| self.const_undefined());
                        let mut call_arguments = Vec::new();
                        if let Some(argument_array) = arguments.get(1) {
                            if !is_nullish_literal(argument_array) {
                                let value = self.lower_expression(argument_array)?;
                                call_arguments.push(CallArgument {
                                    value: value.0,
                                    value_type: value.1,
                                    spread: true,
                                });
                            }
                        }
                        for extra in arguments.iter().skip(2) {
                            self.lower_expression(extra)?;
                        }
                        return Ok(self.emit_call_value(target, Some(receiver), call_arguments));
                    }
                    "bind" => {
                        let target = self.lower_expression(object)?;
                        let this_arg = arguments
                            .first()
                            .map(|value| self.lower_expression(value))
                            .transpose()?
                            .unwrap_or_else(|| self.const_undefined());
                        let bound_arguments =
                            self.lower_call_arguments(arguments.get(1..).unwrap_or_default())?;
                        let result = self.new_value();
                        self.emit(Instruction::BindValue {
                            result,
                            target: target.0,
                            target_type: target.1,
                            this_arg: this_arg.0,
                            this_type: this_arg.1,
                            arguments: bound_arguments,
                        });
                        return Ok((result, ValueType::Callable));
                    }
                    _ => {}
                }
            }

            let receiver = self.lower_expression(object)?;
            let key = self.property_key(property)?;
            let callee_result = self.new_value();
            self.emit(Instruction::DynamicGet {
                result: callee_result,
                object: receiver.0,
                object_type: receiver.1,
                key,
            });
            let call_arguments = self.lower_call_arguments(arguments)?;
            return Ok(self.emit_call_value(
                (callee_result, ValueType::Dynamic),
                Some(receiver),
                call_arguments,
            ));
        }

        let callee = self.lower_expression(callee)?;
        let call_arguments = self.lower_call_arguments(arguments)?;
        Ok(self.emit_call_value(callee, None, call_arguments))
    }

    fn emit_call_value(
        &mut self,
        callee: Lowered,
        receiver: Option<Lowered>,
        arguments: Vec<CallArgument>,
    ) -> Lowered {
        let result = self.new_value();
        let (receiver, receiver_type) = match receiver {
            Some(value) => (Some(value.0), Some(value.1)),
            None => (None, None),
        };
        self.emit(Instruction::CallValue {
            result,
            callee: callee.0,
            callee_type: callee.1,
            receiver,
            receiver_type,
            arguments,
        });
        (result, ValueType::Dynamic)
    }

    fn lower_call_arguments(&mut self, arguments: &[Expression]) -> Result<Vec<CallArgument>> {
        let mut output = Vec::with_capacity(arguments.len());
        for argument in arguments {
            if let Some(spread) = spread_source(argument) {
                let value = self.lower_expression(spread)?;
                output.push(CallArgument {
                    value: value.0,
                    value_type: value.1,
                    spread: true,
                });
            } else {
                let value = self.lower_expression(argument)?;
                output.push(CallArgument {
                    value: value.0,
                    value_type: value.1,
                    spread: false,
                });
            }
        }
        Ok(output)
    }

    fn lower_function_value(&mut self, function: &HirFunction) -> Result<Lowered> {
        if let Some(error) = &function.lowering_error {
            bail!("reachable function frontend lowering thất bại: {error}")
        }
        if function.r#async || function.generator {
            bail!("generic callable path chưa hạ async/generator state machine")
        }

        let mut free_names = super::support::collect_free_variables(function)
            .into_iter()
            .filter(|name| !is_builtin_name(name) && (function.arrow || name != "arguments"))
            .collect::<Vec<_>>();
        free_names.sort();

        let mut captures = Vec::<(String, ValueId, ValueType)>::new();
        for name in free_names {
            if let Some(binding) = self.find_binding(&name).cloned() {
                let captured_type = if binding.kind == VariableKind::Const && binding.initialized {
                    binding.value_type
                } else {
                    // A mutable captured cell can be changed by any later
                    // invocation of the closure. Widen both parent and child
                    // views instead of speculating across call boundaries.
                    self.find_binding_mut(&name).unwrap().value_type = ValueType::Dynamic;
                    ValueType::Dynamic
                };
                captures.push((name, binding.cell, captured_type));
            }
        }

        let function_name = self.compile_function(function, &captures)?;
        let lexical_this = if function.arrow {
            let result = self.new_value();
            self.emit(Instruction::CurrentThis { result });
            Some((result, ValueType::Dynamic))
        } else {
            None
        };

        let result = self.new_value();
        let (lexical_this, lexical_this_type) = match lexical_this {
            Some(value) => (Some(value.0), Some(value.1)),
            None => (None, None),
        };
        self.emit(Instruction::ClosureNewGeneric {
            result,
            function: function_name,
            captures: captures.iter().map(|(_, cell, _)| *cell).collect(),
            capture_types: vec![ValueType::Cell; captures.len()],
            constructable: !function.arrow,
            strict: self.strict,
            lexical_this,
            lexical_this_type,
        });
        Ok((result, ValueType::Callable))
    }

    fn compile_function(
        &mut self,
        function: &HirFunction,
        captures: &[(String, ValueId, ValueType)],
    ) -> Result<String> {
        let id = self.next_function;
        self.next_function += 1;
        let base = function
            .name
            .as_deref()
            .unwrap_or("anonymous")
            .chars()
            .map(|character| {
                if character.is_ascii_alphanumeric() || character == '_' {
                    character
                } else {
                    '_'
                }
            })
            .collect::<String>();
        let ir_name = format!("js.generic.{base}.{id}");

        let mut child = GenericLowerer::new(self.strict, true);
        child.next_value = self.next_value;
        child.next_function = self.next_function;

        let mut ir_captures = Vec::new();
        for (index, (name, _, captured_type)) in captures.iter().enumerate() {
            let value = child.new_value();
            child.emit(Instruction::Capture {
                result: value,
                index: index as u32,
                value_type: ValueType::Cell,
            });
            ir_captures.push(Parameter {
                name: name.clone(),
                value,
                value_type: ValueType::Cell,
            });
            child.scopes[0].insert(
                name.clone(),
                Binding {
                    kind: VariableKind::Let,
                    initialized: true,
                    cell: value,
                    value_type: *captured_type,
                },
            );
        }

        if let Some(name) = &function.name {
            let callable = child.new_value();
            child.emit(Instruction::CurrentCallable { result: callable });
            let cell = child.create_cell((callable, ValueType::Callable));
            child.scopes[0].insert(
                name.clone(),
                Binding {
                    kind: VariableKind::Const,
                    initialized: true,
                    cell,
                    value_type: ValueType::Callable,
                },
            );
        }

        let mut ir_parameters = Vec::new();
        let mut normal_index = 0_u32;
        let mut rest_parameter = None::<String>;
        for parameter in &function.parameters {
            if let Some(rest) = parameter.strip_prefix("@rest:") {
                if rest_parameter.replace(rest.to_owned()).is_some() {
                    bail!("function có nhiều rest parameters")
                }
                continue;
            }
            let value = child.new_value();
            child.emit(Instruction::Parameter {
                result: value,
                index: normal_index,
                value_type: ValueType::Dynamic,
            });
            normal_index += 1;
            ir_parameters.push(Parameter {
                name: parameter.clone(),
                value,
                value_type: ValueType::Dynamic,
            });
            let cell = child.create_cell((value, ValueType::Dynamic));
            child.scopes[0].insert(
                parameter.clone(),
                Binding {
                    kind: VariableKind::Let,
                    initialized: true,
                    cell,
                    value_type: ValueType::Dynamic,
                },
            );
        }

        if let Some(rest) = rest_parameter {
            let value = child.new_value();
            child.emit(Instruction::RestArray {
                result: value,
                start: normal_index,
            });
            let cell = child.create_cell((value, ValueType::Object));
            child.scopes[0].insert(
                rest,
                Binding {
                    kind: VariableKind::Let,
                    initialized: true,
                    cell,
                    value_type: ValueType::Object,
                },
            );
        }

        if !function.arrow && !child.scopes[0].contains_key("arguments") {
            let value = child.new_value();
            child.emit(Instruction::ArgumentsObject { result: value });
            let cell = child.create_cell((value, ValueType::Object));
            child.scopes[0].insert(
                "arguments".to_owned(),
                Binding {
                    kind: VariableKind::Let,
                    initialized: true,
                    cell,
                    value_type: ValueType::Object,
                },
            );
        }

        child.lower_scope(&function.body)?;
        if child.blocks[child.current].terminator.is_none() {
            let undefined = child.const_undefined();
            child.set_terminator(Terminator::ReturnValue {
                value: undefined.0,
                value_type: undefined.1,
            });
        }

        let blocks = child.finish_blocks(Terminator::Unreachable);
        let generated = Function {
            name: ir_name.clone(),
            parameters: ir_parameters,
            captures: ir_captures,
            return_type: Some(ValueType::Dynamic),
            blocks,
        };

        self.next_value = child.next_value;
        self.next_function = child.next_function;
        self.generated_functions
            .append(&mut child.generated_functions);
        self.generated_functions.push(generated);
        Ok(ir_name)
    }
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

fn is_console_log(expression: &Expression) -> bool {
    matches!(
        &expression.kind,
        ExpressionKind::Member {
            object,
            property: MemberProperty::Static(method),
        } if method == "log"
            && matches!(&object.kind, ExpressionKind::Global(name) if name == "console")
    )
}

fn is_builtin_name(name: &str) -> bool {
    matches!(
        name,
        "undefined"
            | "NaN"
            | "Infinity"
            | "console"
            | "Object"
            | "Promise"
            | "Number"
            | "String"
            | "Boolean"
    )
}

fn map_unary(operator: UnaryOperator) -> Result<DynamicUnaryOperator> {
    Ok(match operator {
        UnaryOperator::Plus => DynamicUnaryOperator::Plus,
        UnaryOperator::Minus => DynamicUnaryOperator::Minus,
        UnaryOperator::Not => DynamicUnaryOperator::Not,
        UnaryOperator::BitwiseNot => DynamicUnaryOperator::BitwiseNot,
        UnaryOperator::Typeof => DynamicUnaryOperator::TypeOf,
        UnaryOperator::Void => DynamicUnaryOperator::Void,
        UnaryOperator::Delete => bail!("delete phải được xử lý trên member target"),
    })
}

fn map_binary(operator: BinaryOperator) -> DynamicBinaryOperator {
    match operator {
        BinaryOperator::Add => DynamicBinaryOperator::Add,
        BinaryOperator::Subtract => DynamicBinaryOperator::Subtract,
        BinaryOperator::Multiply => DynamicBinaryOperator::Multiply,
        BinaryOperator::Divide => DynamicBinaryOperator::Divide,
        BinaryOperator::Remainder => DynamicBinaryOperator::Remainder,
        BinaryOperator::Exponential => DynamicBinaryOperator::Exponential,
        BinaryOperator::Equal => DynamicBinaryOperator::Equal,
        BinaryOperator::NotEqual => DynamicBinaryOperator::NotEqual,
        BinaryOperator::StrictEqual => DynamicBinaryOperator::StrictEqual,
        BinaryOperator::StrictNotEqual => DynamicBinaryOperator::StrictNotEqual,
        BinaryOperator::LessThan => DynamicBinaryOperator::LessThan,
        BinaryOperator::LessEqual => DynamicBinaryOperator::LessEqual,
        BinaryOperator::GreaterThan => DynamicBinaryOperator::GreaterThan,
        BinaryOperator::GreaterEqual => DynamicBinaryOperator::GreaterEqual,
        BinaryOperator::ShiftLeft => DynamicBinaryOperator::ShiftLeft,
        BinaryOperator::ShiftRight => DynamicBinaryOperator::ShiftRight,
        BinaryOperator::ShiftRightZeroFill => DynamicBinaryOperator::ShiftRightZeroFill,
        BinaryOperator::BitwiseOr => DynamicBinaryOperator::BitwiseOr,
        BinaryOperator::BitwiseXor => DynamicBinaryOperator::BitwiseXor,
        BinaryOperator::BitwiseAnd => DynamicBinaryOperator::BitwiseAnd,
        BinaryOperator::In => DynamicBinaryOperator::In,
        BinaryOperator::InstanceOf => DynamicBinaryOperator::InstanceOf,
    }
}

fn map_assignment(operator: AssignmentOperator) -> Result<DynamicBinaryOperator> {
    Ok(match operator {
        AssignmentOperator::Add => DynamicBinaryOperator::Add,
        AssignmentOperator::Subtract => DynamicBinaryOperator::Subtract,
        AssignmentOperator::Multiply => DynamicBinaryOperator::Multiply,
        AssignmentOperator::Divide => DynamicBinaryOperator::Divide,
        AssignmentOperator::Remainder => DynamicBinaryOperator::Remainder,
        AssignmentOperator::Exponential => DynamicBinaryOperator::Exponential,
        AssignmentOperator::ShiftLeft => DynamicBinaryOperator::ShiftLeft,
        AssignmentOperator::ShiftRight => DynamicBinaryOperator::ShiftRight,
        AssignmentOperator::ShiftRightZeroFill => DynamicBinaryOperator::ShiftRightZeroFill,
        AssignmentOperator::BitwiseOr => DynamicBinaryOperator::BitwiseOr,
        AssignmentOperator::BitwiseXor => DynamicBinaryOperator::BitwiseXor,
        AssignmentOperator::BitwiseAnd => DynamicBinaryOperator::BitwiseAnd,
        AssignmentOperator::Assign
        | AssignmentOperator::LogicalOr
        | AssignmentOperator::LogicalAnd
        | AssignmentOperator::LogicalNullish => {
            bail!("operator không phải compound binary")
        }
    })
}

fn map_number_binary(operator: DynamicBinaryOperator) -> Option<BinaryNumberOperator> {
    Some(match operator {
        DynamicBinaryOperator::Add => BinaryNumberOperator::Add,
        DynamicBinaryOperator::Subtract => BinaryNumberOperator::Subtract,
        DynamicBinaryOperator::Multiply => BinaryNumberOperator::Multiply,
        DynamicBinaryOperator::Divide => BinaryNumberOperator::Divide,
        DynamicBinaryOperator::Remainder => BinaryNumberOperator::Remainder,
        DynamicBinaryOperator::Exponential => BinaryNumberOperator::Exponential,
        DynamicBinaryOperator::ShiftLeft => BinaryNumberOperator::ShiftLeft,
        DynamicBinaryOperator::ShiftRight => BinaryNumberOperator::ShiftRight,
        DynamicBinaryOperator::ShiftRightZeroFill => BinaryNumberOperator::ShiftRightZeroFill,
        DynamicBinaryOperator::BitwiseOr => BinaryNumberOperator::BitwiseOr,
        DynamicBinaryOperator::BitwiseXor => BinaryNumberOperator::BitwiseXor,
        DynamicBinaryOperator::BitwiseAnd => BinaryNumberOperator::BitwiseAnd,
        _ => return None,
    })
}

fn map_number_compare(operator: DynamicBinaryOperator) -> Option<CompareNumberOperator> {
    Some(match operator {
        DynamicBinaryOperator::Equal => CompareNumberOperator::Equal,
        DynamicBinaryOperator::NotEqual => CompareNumberOperator::NotEqual,
        DynamicBinaryOperator::StrictEqual => CompareNumberOperator::StrictEqual,
        DynamicBinaryOperator::StrictNotEqual => CompareNumberOperator::StrictNotEqual,
        DynamicBinaryOperator::LessThan => CompareNumberOperator::LessThan,
        DynamicBinaryOperator::LessEqual => CompareNumberOperator::LessEqual,
        DynamicBinaryOperator::GreaterThan => CompareNumberOperator::GreaterThan,
        DynamicBinaryOperator::GreaterEqual => CompareNumberOperator::GreaterEqual,
        _ => return None,
    })
}

fn direct_function_names(statements: &[Statement]) -> HashSet<String> {
    statements
        .iter()
        .filter_map(|statement| match &statement.kind {
            StatementKind::FunctionDeclaration(function) => function.name.clone(),
            _ => None,
        })
        .collect()
}

fn scope_uses_runtime_callable_values(statements: &[Statement]) -> bool {
    let declarations = direct_function_names(statements);
    let mut function_values = HashSet::new();
    for statement in statements {
        let StatementKind::VariableDeclaration {
            declarations: variables,
            ..
        } = &statement.kind
        else {
            continue;
        };
        for declaration in variables {
            if matches!(
                declaration.init.as_ref().map(|value| &value.kind),
                Some(ExpressionKind::Function(_))
            ) {
                function_values.insert(declaration.name.clone());
            }
        }
    }

    // Propagate simple aliases until stable.
    loop {
        let mut changed = false;
        for statement in statements {
            let StatementKind::VariableDeclaration {
                declarations: vars, ..
            } = &statement.kind
            else {
                continue;
            };
            for declaration in vars {
                let Some(Expression {
                    kind: ExpressionKind::Global(source),
                    ..
                }) = &declaration.init
                else {
                    continue;
                };
                if (function_values.contains(source) || declarations.contains(source))
                    && function_values.insert(declaration.name.clone())
                {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    statements
        .iter()
        .any(|statement| statement_uses_callable_value(statement, &declarations, &function_values))
}

fn statement_uses_callable_value(
    statement: &Statement,
    declarations: &HashSet<String>,
    function_values: &HashSet<String>,
) -> bool {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            expression_uses_callable_value(
                value,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            )
        }
        StatementKind::VariableDeclaration {
            declarations: vars, ..
        } => vars.iter().any(|item| {
            item.init.as_ref().is_some_and(|value| match &value.kind {
                ExpressionKind::Function(_) => false,
                ExpressionKind::Global(name)
                    if declarations.contains(name) || function_values.contains(name) =>
                {
                    true
                }
                _ => expression_uses_callable_value(
                    value,
                    declarations,
                    function_values,
                    CallableUseContext::Ordinary,
                ),
            })
        }),
        StatementKind::Block(body) => {
            scope_uses_runtime_callable_values(body)
                || body.iter().any(|statement| {
                    statement_uses_callable_value(statement, declarations, function_values)
                })
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression_uses_callable_value(
                test,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || statement_uses_callable_value(consequent, declarations, function_values)
                || alternate.as_deref().is_some_and(|value| {
                    statement_uses_callable_value(value, declarations, function_values)
                })
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression_uses_callable_value(
                test,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || statement_uses_callable_value(body, declarations, function_values)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => expression_uses_callable_value(
                    value,
                    declarations,
                    function_values,
                    CallableUseContext::Ordinary,
                ),
                ForInit::VariableDeclaration {
                    declarations: vars, ..
                } => vars.iter().any(|item| {
                    item.init.as_ref().is_some_and(|value| {
                        expression_uses_callable_value(
                            value,
                            declarations,
                            function_values,
                            CallableUseContext::Ordinary,
                        )
                    })
                }),
            }) || test.as_ref().is_some_and(|value| {
                expression_uses_callable_value(
                    value,
                    declarations,
                    function_values,
                    CallableUseContext::Ordinary,
                )
            }) || update.as_ref().is_some_and(|value| {
                expression_uses_callable_value(
                    value,
                    declarations,
                    function_values,
                    CallableUseContext::Ordinary,
                )
            }) || statement_uses_callable_value(body, declarations, function_values)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expression_uses_callable_value(
                right,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || statement_uses_callable_value(body, declarations, function_values)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expression_uses_callable_value(
                discriminant,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || cases.iter().any(|case| {
                case.test.as_ref().is_some_and(|value| {
                    expression_uses_callable_value(
                        value,
                        declarations,
                        function_values,
                        CallableUseContext::Ordinary,
                    )
                }) || case.consequent.iter().any(|statement| {
                    statement_uses_callable_value(statement, declarations, function_values)
                })
            })
        }
        StatementKind::Labeled { body, .. } => {
            statement_uses_callable_value(body, declarations, function_values)
        }
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_uses_callable_value(block, declarations, function_values)
                || handler.as_ref().is_some_and(|handler| {
                    statement_uses_callable_value(&handler.body, declarations, function_values)
                })
                || finalizer.as_deref().is_some_and(|value| {
                    statement_uses_callable_value(value, declarations, function_values)
                })
        }
        StatementKind::FunctionDeclaration(function) => {
            scope_uses_runtime_callable_values(&function.body)
        }
        StatementKind::Return(Some(value)) => expression_uses_callable_value(
            value,
            declarations,
            function_values,
            CallableUseContext::Escaping,
        ),
        StatementKind::Return(None)
        | StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

#[derive(Clone, Copy)]
enum CallableUseContext {
    Ordinary,
    Escaping,
    DirectCallee,
    PromiseArgument,
}

fn expression_uses_callable_value(
    expression: &Expression,
    declarations: &HashSet<String>,
    function_values: &HashSet<String>,
    context: CallableUseContext,
) -> bool {
    match &expression.kind {
        ExpressionKind::Global(name) => match context {
            CallableUseContext::Escaping => {
                declarations.contains(name) || function_values.contains(name)
            }
            CallableUseContext::DirectCallee => function_values.contains(name),
            CallableUseContext::Ordinary | CallableUseContext::PromiseArgument => false,
        },
        ExpressionKind::Function(function) => {
            !matches!(context, CallableUseContext::PromiseArgument)
                && matches!(
                    context,
                    CallableUseContext::Escaping | CallableUseContext::DirectCallee
                )
                || function_requires_generic(function)
        }
        ExpressionKind::Member { object, property } => {
            expression_uses_callable_value(
                object,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || matches!(
                property,
                MemberProperty::Computed(value)
                    if expression_uses_callable_value(
                        value,
                        declarations,
                        function_values,
                        CallableUseContext::Ordinary,
                    )
            )
        }
        ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
            ObjectEntry::Property(property) => expression_uses_callable_value(
                &property.value,
                declarations,
                function_values,
                CallableUseContext::Escaping,
            ),
            ObjectEntry::Spread(value) => expression_uses_callable_value(
                value,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ),
            ObjectEntry::Accessor { get, set, .. } => {
                get.as_ref().is_some_and(|value| {
                    expression_uses_callable_value(
                        value,
                        declarations,
                        function_values,
                        CallableUseContext::Escaping,
                    )
                }) || set.as_ref().is_some_and(|value| {
                    expression_uses_callable_value(
                        value,
                        declarations,
                        function_values,
                        CallableUseContext::Escaping,
                    )
                })
            }
        }),
        ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
            ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                expression_uses_callable_value(
                    value,
                    declarations,
                    function_values,
                    CallableUseContext::Escaping,
                )
            }
            ArrayElement::Hole => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            expression_uses_callable_value(
                test,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || expression_uses_callable_value(consequent, declarations, function_values, context)
                || expression_uses_callable_value(alternate, declarations, function_values, context)
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            expression_uses_callable_value(
                argument,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            )
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            expression_uses_callable_value(
                left,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || expression_uses_callable_value(
                right,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            )
        }
        ExpressionKind::Assignment { target, value, .. } => {
            target_uses_callable_value(target, declarations, function_values)
                || expression_uses_callable_value(
                    value,
                    declarations,
                    function_values,
                    CallableUseContext::Escaping,
                )
        }
        ExpressionKind::Update { target, .. } => {
            target_uses_callable_value(target, declarations, function_values)
        }
        ExpressionKind::Call { callee, arguments } => {
            let promise_like = matches!(
                &callee.kind,
                ExpressionKind::Member {
                    object,
                    property: MemberProperty::Static(method),
                } if matches!(method.as_str(), "then" | "catch" | "finally")
                    || matches!(&object.kind, ExpressionKind::Global(name) if name == "Promise")
            );
            expression_uses_callable_value(
                callee,
                declarations,
                function_values,
                CallableUseContext::DirectCallee,
            ) || arguments.iter().any(|argument| {
                expression_uses_callable_value(
                    argument,
                    declarations,
                    function_values,
                    if promise_like {
                        CallableUseContext::PromiseArgument
                    } else {
                        CallableUseContext::Escaping
                    },
                )
            })
        }
        ExpressionKind::New { callee, arguments } => {
            expression_uses_callable_value(
                callee,
                declarations,
                function_values,
                CallableUseContext::DirectCallee,
            ) || arguments.iter().any(|argument| {
                expression_uses_callable_value(
                    argument,
                    declarations,
                    function_values,
                    CallableUseContext::Escaping,
                )
            })
        }
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null
        | ExpressionKind::This => false,
    }
}

fn target_uses_callable_value(
    target: &AssignmentTarget,
    declarations: &HashSet<String>,
    function_values: &HashSet<String>,
) -> bool {
    match target {
        AssignmentTarget::Identifier(_) => false,
        AssignmentTarget::Member { object, property } => {
            expression_uses_callable_value(
                object,
                declarations,
                function_values,
                CallableUseContext::Ordinary,
            ) || matches!(
                property,
                MemberProperty::Computed(value)
                    if expression_uses_callable_value(
                        value,
                        declarations,
                        function_values,
                        CallableUseContext::Ordinary,
                    )
            )
        }
    }
}

fn statement_requires_generic(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            expression_requires_generic(value, &HashSet::new(), false)
        }
        StatementKind::VariableDeclaration { declarations, .. } => declarations.iter().any(|d| {
            d.init
                .as_ref()
                .is_some_and(|value| expression_requires_generic(value, &HashSet::new(), false))
        }),
        StatementKind::Block(body) => body.iter().any(statement_requires_generic),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression_requires_generic(test, &HashSet::new(), false)
                || statement_requires_generic(consequent)
                || alternate.as_deref().is_some_and(statement_requires_generic)
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression_requires_generic(test, &HashSet::new(), false)
                || statement_requires_generic(body)
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|init| match init {
                ForInit::Expression(value) => {
                    expression_requires_generic(value, &HashSet::new(), false)
                }
                ForInit::VariableDeclaration { declarations, .. } => declarations.iter().any(|d| {
                    d.init.as_ref().is_some_and(|value| {
                        expression_requires_generic(value, &HashSet::new(), false)
                    })
                }),
            }) || test
                .as_ref()
                .is_some_and(|value| expression_requires_generic(value, &HashSet::new(), false))
                || update
                    .as_ref()
                    .is_some_and(|value| expression_requires_generic(value, &HashSet::new(), false))
                || statement_requires_generic(body)
        }
        StatementKind::ForIn { right, body, .. } | StatementKind::ForOf { right, body, .. } => {
            expression_requires_generic(right, &HashSet::new(), false)
                || statement_requires_generic(body)
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            expression_requires_generic(discriminant, &HashSet::new(), false)
                || cases.iter().any(|case| {
                    case.test.as_ref().is_some_and(|value| {
                        expression_requires_generic(value, &HashSet::new(), false)
                    }) || case.consequent.iter().any(statement_requires_generic)
                })
        }
        StatementKind::Labeled { body, .. } => statement_requires_generic(body),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_requires_generic(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| statement_requires_generic(&handler.body))
                || finalizer.as_deref().is_some_and(statement_requires_generic)
        }
        StatementKind::FunctionDeclaration(function) => function_requires_generic(function),
        StatementKind::Return(value) => value
            .as_ref()
            .is_some_and(|value| expression_requires_generic(value, &HashSet::new(), true)),
        StatementKind::Empty
        | StatementKind::Debugger
        | StatementKind::Break(_)
        | StatementKind::Continue(_) => false,
    }
}

fn function_requires_generic(function: &HirFunction) -> bool {
    if function
        .parameters
        .iter()
        .any(|name| name.starts_with("@rest:"))
    {
        return true;
    }
    let local_functions = function
        .body
        .iter()
        .filter_map(|statement| match &statement.kind {
            StatementKind::FunctionDeclaration(function) => function.name.clone(),
            _ => None,
        })
        .collect::<HashSet<_>>();
    function
        .body
        .iter()
        .any(|statement| statement_requires_generic_with_functions(statement, &local_functions))
        || scope_uses_runtime_callable_values(&function.body)
}

fn statement_requires_generic_with_functions(
    statement: &Statement,
    functions: &HashSet<String>,
) -> bool {
    match &statement.kind {
        StatementKind::Return(Some(value)) => expression_requires_generic(value, functions, true),
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            expression_requires_generic(value, functions, false)
        }
        StatementKind::VariableDeclaration { declarations, .. } => declarations.iter().any(|d| {
            d.init.as_ref().is_some_and(|value| {
                matches!(&value.kind, ExpressionKind::Global(name) if functions.contains(name))
                    || expression_requires_generic(value, functions, false)
            })
        }),
        StatementKind::Block(body) => body
            .iter()
            .any(|value| statement_requires_generic_with_functions(value, functions)),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            expression_requires_generic(test, functions, false)
                || statement_requires_generic_with_functions(consequent, functions)
                || alternate.as_deref().is_some_and(|value| {
                    statement_requires_generic_with_functions(value, functions)
                })
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            expression_requires_generic(test, functions, false)
                || statement_requires_generic_with_functions(body, functions)
        }
        StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => {
            statement_requires_generic_with_functions(body, functions)
        }
        StatementKind::FunctionDeclaration(nested) => function_requires_generic(nested),
        _ => statement_requires_generic(statement),
    }
}

fn expression_requires_generic(
    expression: &Expression,
    local_functions: &HashSet<String>,
    value_position: bool,
) -> bool {
    match &expression.kind {
        ExpressionKind::This => true,
        ExpressionKind::Global(name) => {
            name == "arguments"
                || name == "@spread"
                || (value_position && local_functions.contains(name))
        }
        ExpressionKind::Member { object, property } => {
            expression_requires_generic(object, local_functions, true)
                || matches!(
                    property,
                    MemberProperty::Computed(value)
                        if expression_requires_generic(value, local_functions, false)
                )
        }
        ExpressionKind::Object(entries) => entries.iter().any(|entry| match entry {
            ObjectEntry::Property(property) => {
                expression_requires_generic(&property.value, local_functions, true)
            }
            ObjectEntry::Spread(value) => {
                expression_requires_generic(value, local_functions, false)
            }
            ObjectEntry::Accessor { get, set, .. } => {
                get.as_ref()
                    .is_some_and(|value| expression_requires_generic(value, local_functions, true))
                    || set.as_ref().is_some_and(|value| {
                        expression_requires_generic(value, local_functions, true)
                    })
            }
        }),
        ExpressionKind::Array(elements) => elements.iter().any(|element| match element {
            ArrayElement::Expression(value) => {
                expression_requires_generic(value, local_functions, true)
            }
            ArrayElement::Spread(_) => true,
            ArrayElement::Hole => false,
        }),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            expression_requires_generic(test, local_functions, false)
                || expression_requires_generic(consequent, local_functions, value_position)
                || expression_requires_generic(alternate, local_functions, value_position)
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            expression_requires_generic(argument, local_functions, false)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            expression_requires_generic(left, local_functions, false)
                || expression_requires_generic(right, local_functions, false)
        }
        ExpressionKind::Assignment { target, value, .. } => {
            target_requires_generic(target, local_functions)
                || expression_requires_generic(value, local_functions, true)
        }
        ExpressionKind::Update { target, .. } => target_requires_generic(target, local_functions),
        ExpressionKind::Call { callee, arguments } => {
            let promise_like = matches!(
                &callee.kind,
                ExpressionKind::Member {
                    object,
                    property: MemberProperty::Static(method),
                } if matches!(method.as_str(), "then" | "catch" | "finally")
                    || matches!(&object.kind, ExpressionKind::Global(name) if name == "Promise")
            );
            let generic_member = matches!(
                &callee.kind,
                ExpressionKind::Member {
                    object,
                    property: MemberProperty::Static(method),
                } if matches!(method.as_str(), "call" | "apply" | "bind")
                    || (!promise_like
                        && !matches!(
                            &object.kind,
                            ExpressionKind::Global(name)
                                if name == "console" || name == "Promise" || name == "Object"
                        ))
            );
            generic_member
                || spread_source(expression).is_some()
                || expression_requires_generic(callee, local_functions, false)
                || arguments.iter().any(|argument| {
                    spread_source(argument).is_some()
                        || expression_requires_generic(argument, local_functions, !promise_like)
                })
        }
        ExpressionKind::New { .. } => true,
        ExpressionKind::Function(function) => function_requires_generic(function),
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::BigInt(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null => false,
    }
}

fn target_requires_generic(target: &AssignmentTarget, local_functions: &HashSet<String>) -> bool {
    match target {
        AssignmentTarget::Identifier(_) => false,
        AssignmentTarget::Member { object, property } => {
            expression_requires_generic(object, local_functions, false)
                || matches!(
                    property,
                    MemberProperty::Computed(value)
                        if expression_requires_generic(value, local_functions, false)
                )
        }
    }
}

fn statement_contains_async_or_generator(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::FunctionDeclaration(function) => {
            function.r#async
                || function.generator
                || function
                    .body
                    .iter()
                    .any(statement_contains_async_or_generator)
        }
        StatementKind::Block(body) => body.iter().any(statement_contains_async_or_generator),
        StatementKind::If {
            consequent,
            alternate,
            ..
        } => {
            statement_contains_async_or_generator(consequent)
                || alternate
                    .as_deref()
                    .is_some_and(statement_contains_async_or_generator)
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::For { body, .. }
        | StatementKind::ForIn { body, .. }
        | StatementKind::ForOf { body, .. }
        | StatementKind::Labeled { body, .. } => statement_contains_async_or_generator(body),
        StatementKind::Switch { cases, .. } => cases
            .iter()
            .flat_map(|case| &case.consequent)
            .any(statement_contains_async_or_generator),
        StatementKind::Try {
            block,
            handler,
            finalizer,
        } => {
            statement_contains_async_or_generator(block)
                || handler
                    .as_ref()
                    .is_some_and(|handler| statement_contains_async_or_generator(&handler.body))
                || finalizer
                    .as_deref()
                    .is_some_and(statement_contains_async_or_generator)
        }
        _ => false,
    }
}
