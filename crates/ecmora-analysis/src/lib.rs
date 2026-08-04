use anyhow::{Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, Expression, ExpressionKind,
    ForInit, Function as HirFunction, LogicalOperator, MemberProperty, ObjectEntry,
    Program as HirProgram, Span, Statement, StatementKind, UnaryOperator, UpdateOperator,
    VariableKind,
};
use ecmora_ir::{
    BasicBlock, BinaryNumberOperator, BlockId, Builtin, CompareNumberOperator, Function,
    Instruction, Parameter, Program, Terminator, UnaryNumberOperator, ValueId, ValueType,
};
use ecmora_value::{BinaryOperator as SemBinary, UnaryOperator as SemUnary, Value};
use std::collections::{HashMap, HashSet};

mod abstract_value;
mod async_normalize;
pub mod effects;
mod specialization;
mod support;

use abstract_value::AbstractValue;
use async_normalize::normalize_async_function;
use effects::validate_native_semantics;
use specialization::*;
use support::*;

pub fn analyze(hir: &HirProgram) -> Result<Program> {
    validate_native_semantics(hir)?;
    if !hir.promise_subclasses.is_empty() {
        bail!("Promise subclass/@@species requires compatibility constructor objects")
    }
    let mut lowerer = Lowerer {
        blocks: vec![PendingBlock {
            name: "entry".to_owned(),
            instructions: Vec::new(),
            terminator: None,
        }],
        current: 0,
        scopes: vec![HashMap::new()],
        strict: hir.strict,
        ..Default::default()
    };
    lowerer.lower_scope(&hir.statements)?;
    // An abrupt top-level completion must not execute queued work that appears
    // after the throw. The ThrowValue terminator goes straight to LLVM.
    if lowerer.blocks[lowerer.current].terminator.is_none() {
        lowerer.drain_promise_jobs()?;
    }
    if lowerer.blocks[lowerer.current].terminator.is_none() {
        lowerer.blocks[lowerer.current].terminator = Some(Terminator::ReturnI32(0));
    }
    let blocks = std::mem::take(&mut lowerer.blocks)
        .into_iter()
        .map(|block| BasicBlock {
            name: block.name,
            instructions: block.instructions,
            terminator: block.terminator.unwrap_or(Terminator::ReturnI32(0)),
        })
        .collect();
    let mut functions = vec![Function {
        name: "main".to_owned(),
        parameters: Vec::new(),
        captures: Vec::new(),
        return_type: None,
        blocks,
    }];
    functions.append(&mut lowerer.generated_functions);
    let program = Program { functions };
    ecmora_ir::verify_program(&program)?;
    Ok(program)
}

#[derive(Debug, Clone)]
struct Binding {
    kind: VariableKind,
    initialized: bool,
    value_id: ValueId,
    value_type: ValueType,
    value: Option<Value>,
    cell: Option<ValueId>,
}

#[derive(Debug, Clone)]
struct CapturedBinding {
    name: String,
    kind: VariableKind,
    cell: ValueId,
    value_type: ValueType,
}

#[derive(Debug, Clone)]
struct ClosureBinding {
    function: HirFunction,
    captures: Vec<CapturedBinding>,
}

#[derive(Debug, Clone)]
struct ActiveSpecialization {
    /// Tên function trong IR, ví dụ `js.__m0_sum.0`.
    function_name: String,

    /// Return type được suy ra trước khi lower body.
    ///
    /// Recursive call cần biết type ngay lập tức, trước khi body của function
    /// hiện tại được hoàn tất.
    return_type: ValueType,
}

#[derive(Debug, Clone, Default)]
struct StaticAccessor {
    getter: Option<ClosureBinding>,
    setter: Option<ClosureBinding>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PromiseState {
    Fulfilled,
    Rejected,
}

#[derive(Debug, Clone)]
struct PromiseSettlement {
    state: PromiseState,
    value: (ValueId, ValueType, Option<Value>),
}

#[derive(Debug, Clone)]
enum PromiseHandlerOutcome {
    Return((ValueId, ValueType, Option<Value>)),
    Throw((ValueId, ValueType, Option<Value>)),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PromiseChainKind {
    Then,
    Finally,
}

#[derive(Debug, Clone)]
struct PromiseChain {
    parent: ValueId,
    on_fulfilled: Option<ClosureBinding>,
    on_rejected: Option<ClosureBinding>,
    kind: PromiseChainKind,
}

#[derive(Debug)]
struct PendingBlock {
    name: String,
    instructions: Vec<Instruction>,
    terminator: Option<Terminator>,
}

#[derive(Debug, Default)]
struct Lowerer {
    next_value: u32,
    blocks: Vec<PendingBlock>,
    current: usize,
    scopes: Vec<HashMap<String, Binding>>,
    strict: bool,
    break_targets: Vec<BlockId>,
    continue_targets: Vec<BlockId>,
    continue_edges: Vec<Vec<(BlockId, Vec<HashMap<String, Binding>>)>>,
    break_edges: Vec<Vec<(BlockId, Vec<HashMap<String, Binding>>)>>,
    function_defs: HashMap<String, HirFunction>,
    inline_callables: HashMap<String, ClosureBinding>,
    closure_callables: HashMap<String, ClosureBinding>,
    generated_functions: Vec<Function>,
    function_mode: bool,
    return_types: Vec<ValueType>,
    next_function: u32,
    specializations: HashMap<SpecializationKey, (String, ValueType)>,
    active_specializations: HashMap<SpecializationKey, ActiveSpecialization>,
    specialization_counts: HashMap<String, usize>,
    expected_type_hint: Option<ValueType>,
    function_return_hint: Option<ValueType>,
    function_arity: Option<usize>,
    static_accessors: HashMap<(ValueId, String), StaticAccessor>,
    static_object_callables: HashMap<(ValueId, String), ClosureBinding>,
    promise_settlements: HashMap<ValueId, PromiseSettlement>,
    promise_chains: HashMap<ValueId, PromiseChain>,
    promise_order: Vec<ValueId>,
    promise_resolution_stack: HashSet<ValueId>,
    thenable_resolution_stack: HashSet<ValueId>,
    last_callable: Option<ValueId>,
    used_bindings: Vec<HashSet<String>>,
}

impl Lowerer {
    fn new_value(&mut self) -> ValueId {
        let value = ValueId(self.next_value);
        self.next_value += 1;
        value
    }

    fn emit(&mut self, instruction: Instruction) {
        self.blocks[self.current].instructions.push(instruction);
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

    fn set_terminator(&mut self, terminator: Terminator) {
        self.blocks[self.current].terminator = Some(terminator);
    }

    fn lower_scope(&mut self, statements: &[Statement]) -> Result<()> {
        self.used_bindings.push(collect_used_names(statements));
        self.predeclare(statements)?;
        let result = (|| {
            for statement in statements {
                if self.blocks[self.current].terminator.is_some() {
                    break;
                }
                self.lower_statement(statement)?;
            }
            Ok(())
        })();
        self.used_bindings.pop();
        result
    }

    fn predeclare(&mut self, statements: &[Statement]) -> Result<()> {
        for statement in statements {
            if let StatementKind::FunctionDeclaration(function) = &statement.kind {
                let name = function
                    .name
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("function declaration thiếu tên"))?;
                self.function_defs.insert(name.clone(), function.clone());
            }
        }
        let names = statements
            .iter()
            .flat_map(|statement| match &statement.kind {
                StatementKind::VariableDeclaration { declarations, .. } => declarations
                    .iter()
                    .map(|d| d.name.as_str())
                    .collect::<Vec<_>>(),
                _ => Vec::new(),
            })
            .collect::<Vec<_>>();
        for name in names {
            if self
                .scopes
                .last()
                .is_some_and(|scope| scope.contains_key(name))
            {
                bail!("identifier `{name}` được khai báo trùng trong cùng lexical scope")
            }
            let id = self.new_value();
            self.scopes.last_mut().unwrap().insert(
                name.to_owned(),
                Binding {
                    kind: VariableKind::Let,
                    initialized: false,
                    value_id: id,
                    value_type: ValueType::Undefined,
                    value: None,
                    cell: None,
                },
            );
        }
        for statement in statements {
            if let StatementKind::VariableDeclaration { kind, declarations } = &statement.kind {
                for declaration in declarations {
                    self.scopes
                        .last_mut()
                        .unwrap()
                        .get_mut(&declaration.name)
                        .unwrap()
                        .kind = *kind;
                }
            }
        }
        Ok(())
    }

    fn is_pure_initializer(&self, expression: &Expression) -> bool {
        let functions = self.function_defs.keys().cloned().collect::<HashSet<_>>();
        effects::expression_effects(expression).is_empty()
            && is_pure_expression_known(expression, &functions)
    }

    fn lower_statement(&mut self, statement: &Statement) -> Result<()> {
        match &statement.kind {
            StatementKind::Expression(expression) => {
                self.lower_expression(expression)?;
                Ok(())
            }
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
            StatementKind::While { test, body } => self.lower_loop(None, Some(test), None, body),
            StatementKind::DoWhile { body, test } => self.lower_do_while(body, test),
            StatementKind::For {
                init,
                test,
                update,
                body,
            } => self.lower_loop(init.as_ref(), test.as_ref(), update.as_ref(), body),
            StatementKind::ForIn {
                name,
                kind,
                right,
                body,
            } => self.lower_static_for_each(name, *kind, right, body, false),
            StatementKind::ForOf {
                name,
                kind,
                right,
                body,
            } => self.lower_static_for_each(name, *kind, right, body, true),
            StatementKind::FunctionDeclaration(_) => Ok(()),
            StatementKind::Return(expression) => {
                if !self.function_mode {
                    bail!("return ngoài function")
                }
                let return_hint = self.function_return_hint;
                let value = match expression {
                    Some(expression) => self.lower_expression_with_hint(expression, return_hint)?,
                    None => self.emit_value(Value::Undefined),
                };
                self.return_types.push(value.1);
                if let Some(tail_call) = self.take_direct_tail_call(value.0) {
                    self.set_terminator(tail_call);
                } else {
                    self.set_terminator(Terminator::ReturnValue {
                        value: value.0,
                        value_type: value.1,
                    });
                }
                Ok(())
            }
            StatementKind::Throw(expression) => {
                let value = self.lower_expression(expression)?;
                // ECMAScript ThrowCompletion is not a ReturnCompletion. Keep
                // the operand typed, but do not add it to normal return types.
                self.set_terminator(Terminator::ThrowValue {
                    value: value.0,
                    value_type: value.1,
                });
                Ok(())
            }
            StatementKind::Switch {
                discriminant,
                cases,
            } => self.lower_switch(discriminant, cases),
            StatementKind::Break => {
                let target = self
                    .break_targets
                    .last()
                    .copied()
                    .ok_or_else(|| anyhow::anyhow!("break ngoài loop/switch"))?;
                let scopes = self.scopes.clone();
                if let Some(edges) = self.break_edges.last_mut() {
                    edges.push((BlockId(self.current as u32), scopes));
                }
                self.set_terminator(Terminator::Jump(target));
                Ok(())
            }
            StatementKind::Continue => {
                let target = self
                    .continue_targets
                    .last()
                    .copied()
                    .ok_or_else(|| anyhow::anyhow!("continue ngoài loop"))?;
                let scopes = self.scopes.clone();
                if let Some(edges) = self.continue_edges.last_mut() {
                    edges.push((BlockId(self.current as u32), scopes));
                }
                self.set_terminator(Terminator::Jump(target));
                Ok(())
            }
            StatementKind::VariableDeclaration { kind, declarations } => {
                for declaration in declarations {
                    let is_used = self
                        .used_bindings
                        .last()
                        .is_none_or(|used| used.contains(&declaration.name));
                    if !is_used
                        && declaration
                            .init
                            .as_ref()
                            .is_none_or(|expression| self.is_pure_initializer(expression))
                    {
                        let undefined = self.emit_value(Value::Undefined);
                        let binding =
                            self.find_binding_mut(&declaration.name).ok_or_else(|| {
                                anyhow::anyhow!("binding `{}` không tồn tại", declaration.name)
                            })?;
                        binding.kind = *kind;
                        binding.initialized = true;
                        binding.value_id = undefined.0;
                        binding.value_type = ValueType::Undefined;
                        binding.value = Some(Value::Undefined);
                        continue;
                    }
                    if let Some(Expression {
                        kind: ExpressionKind::Function(function),
                        ..
                    }) = &declaration.init
                    {
                        let captures = self.capture_environment_for(function);
                        self.closure_callables.insert(
                            declaration.name.clone(),
                            ClosureBinding {
                                function: function.clone(),
                                captures,
                            },
                        );
                        let value = self.emit_value(Value::Undefined);
                        let binding =
                            self.find_binding_mut(&declaration.name).ok_or_else(|| {
                                anyhow::anyhow!("binding `{}` không tồn tại", declaration.name)
                            })?;
                        binding.kind = *kind;
                        binding.initialized = true;
                        binding.value_id = value.0;
                        binding.value_type = ValueType::Callable;
                        binding.value = None;
                        continue;
                    }
                    let value = match &declaration.init {
                        Some(init) => self.lower_expression(init)?,
                        None => (
                            self.const_value(Value::Undefined),
                            ValueType::Undefined,
                            Some(Value::Undefined),
                        ),
                    };
                    let binding = self.find_binding_mut(&declaration.name).ok_or_else(|| {
                        anyhow::anyhow!("binding `{}` không tồn tại", declaration.name)
                    })?;
                    binding.kind = *kind;
                    binding.initialized = true;
                    binding.value_id = value.0;
                    binding.value_type = value.1;
                    binding.value = value.2;
                }
                Ok(())
            }
        }
    }

    fn lower_loop(
        &mut self,
        init: Option<&ForInit>,
        test: Option<&Expression>,
        update: Option<&Expression>,
        body: &Statement,
    ) -> Result<()> {
        let has_for_scope = init.is_some();
        if has_for_scope {
            self.scopes.push(HashMap::new());
        }
        if let Some(init) = init {
            match init {
                ForInit::Expression(expression) => {
                    self.lower_expression(expression)?;
                }
                ForInit::VariableDeclaration { kind, declarations } => {
                    for declaration in declarations {
                        if self.scopes.last().unwrap().contains_key(&declaration.name) {
                            bail!(
                                "identifier `{}` được khai báo trùng trong for",
                                declaration.name
                            )
                        }
                        let placeholder = self.new_value();
                        self.scopes.last_mut().unwrap().insert(
                            declaration.name.clone(),
                            Binding {
                                kind: *kind,
                                initialized: false,
                                value_id: placeholder,
                                value_type: ValueType::Undefined,
                                value: None,
                                cell: None,
                            },
                        );
                    }
                    for declaration in declarations {
                        let value = match &declaration.init {
                            Some(expression) => self.lower_expression(expression)?,
                            None => self.emit_value(Value::Undefined),
                        };
                        let binding = self.find_binding_mut(&declaration.name).unwrap();
                        binding.initialized = true;
                        binding.value_id = value.0;
                        binding.value_type = value.1;
                        binding.value = value.2;
                    }
                }
            }
        }

        let preheader = BlockId(self.current as u32);
        let header = self.new_block("loop.header");
        let body_block = self.new_block("loop.body");
        let update_block = update.map(|_| self.new_block("loop.update"));
        let exit = self.new_block("loop.exit");
        self.set_terminator(Terminator::Jump(header));

        self.current = header.0 as usize;
        let mut phis = Vec::<(usize, String, usize, ValueId, ValueType, Option<Value>)>::new();
        for scope_index in 0..self.scopes.len() {
            let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
            for name in names {
                let binding = self.scopes[scope_index].get(&name).unwrap().clone();
                if !binding.initialized {
                    continue;
                }
                let result = self.new_value();
                let instruction_index = self.blocks[self.current].instructions.len();
                self.emit(Instruction::Phi {
                    result,
                    value_type: binding.value_type,
                    incoming: vec![(preheader, binding.value_id)],
                });
                let header_binding = self.scopes[scope_index].get_mut(&name).unwrap();
                header_binding.value_id = result;
                header_binding.value = if binding.value_type == ValueType::Object {
                    binding.value.clone()
                } else {
                    None
                };
                phis.push((
                    scope_index,
                    name,
                    instruction_index,
                    result,
                    binding.value_type,
                    binding.value.clone(),
                ));
            }
        }

        let condition = match test {
            Some(test) => {
                let value = self.lower_expression(test)?;
                self.to_boolean(value)?
            }
            None => self.emit_value(Value::Bool(true)).0,
        };
        self.set_terminator(Terminator::Branch {
            condition,
            then_block: body_block,
            else_block: exit,
        });

        self.current = body_block.0 as usize;
        self.break_targets.push(exit);
        self.break_edges.push(Vec::new());
        self.continue_edges.push(Vec::new());
        self.continue_targets.push(update_block.unwrap_or(header));
        self.lower_statement(body)?;
        self.continue_targets.pop();
        let continue_edges = self.continue_edges.pop().unwrap();
        self.break_targets.pop();
        let break_edges = self.break_edges.pop().unwrap();

        let body_reaches_backedge = self.blocks[self.current].terminator.is_none();
        let body_end = BlockId(self.current as u32);
        if body_reaches_backedge {
            self.set_terminator(Terminator::Jump(update_block.unwrap_or(header)));
        }
        if let Some(update_block) = update_block {
            self.current = update_block.0 as usize;
            if !continue_edges.is_empty() {
                for scope_index in 0..self.scopes.len() {
                    let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
                    for name in names {
                        let mut incoming = Vec::new();
                        if body_reaches_backedge {
                            incoming.push((
                                body_end,
                                self.scopes[scope_index].get(&name).unwrap().value_id,
                            ));
                        }
                        for (block, scopes) in &continue_edges {
                            incoming
                                .push((*block, scopes[scope_index].get(&name).unwrap().value_id));
                        }
                        if incoming.len() > 1 {
                            let binding = self.scopes[scope_index].get(&name).unwrap().clone();
                            let result = self.new_value();
                            self.emit(Instruction::Phi {
                                result,
                                value_type: binding.value_type,
                                incoming,
                            });
                            let binding = self.scopes[scope_index].get_mut(&name).unwrap();
                            binding.value_id = result;
                            binding.value = None;
                        }
                    }
                }
            }
            self.lower_expression(update.unwrap())?;
            if self.blocks[self.current].terminator.is_none() {
                self.set_terminator(Terminator::Jump(header));
            }
        }
        let backedge = BlockId(self.current as u32);
        let backedge_scopes = self.scopes.clone();
        for (scope_index, name, instruction_index, _, _, _) in &phis {
            let back = backedge_scopes[*scope_index].get(name).unwrap();
            let Instruction::Phi {
                value_type,
                incoming,
                ..
            } = &mut self.blocks[header.0 as usize].instructions[*instruction_index]
            else {
                unreachable!()
            };
            if *value_type != back.value_type {
                bail!(
                    "loop thay đổi kiểu `{name}` từ {:?} sang {:?}; dynamic loop operation chưa được hỗ trợ",
                    value_type,
                    back.value_type
                )
            }
            if body_reaches_backedge {
                incoming.push((backedge, back.value_id));
            }
            if update_block.is_none() {
                for (continue_block, continue_scopes) in &continue_edges {
                    let value = continue_scopes[*scope_index].get(name).unwrap();
                    incoming.push((*continue_block, value.value_id));
                }
            }
        }

        self.current = exit.0 as usize;
        // Values visible after the loop are the header phi values and are unknown.
        for (scope_index, name, _, result, value_type, shape) in phis {
            let binding = self.scopes[scope_index].get_mut(&name).unwrap();
            binding.value_id = result;
            binding.value_type = value_type;
            binding.value = if value_type == ValueType::Object {
                shape
            } else {
                None
            };
        }
        if !break_edges.is_empty() {
            for scope_index in 0..self.scopes.len() {
                let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
                for name in names {
                    let normal = self.scopes[scope_index].get(&name).unwrap().clone();
                    let mut incoming = vec![(header, normal.value_id)];
                    let mut value_type = normal.value_type;
                    for (block, scopes) in &break_edges {
                        let binding = scopes[scope_index].get(&name).unwrap();
                        incoming.push((*block, binding.value_id));
                        if binding.value_type != value_type {
                            value_type = ValueType::Dynamic;
                        }
                    }
                    if incoming.iter().all(|(_, value)| *value == normal.value_id) {
                        continue;
                    }
                    let result = self.new_value();
                    self.emit(Instruction::Phi {
                        result,
                        value_type,
                        incoming,
                    });
                    let binding = self.scopes[scope_index].get_mut(&name).unwrap();
                    binding.value_id = result;
                    binding.value_type = value_type;
                    binding.value = None;
                }
            }
        }
        if has_for_scope {
            self.scopes.pop();
        }
        Ok(())
    }

    fn lower_static_for_each(
        &mut self,
        name: &str,
        kind: VariableKind,
        right: &Expression,
        body: &Statement,
        is_of: bool,
    ) -> Result<()> {
        let iterable = self.lower_expression(right)?;
        let Some(known) = iterable.2 else {
            bail!("for-in/of cần known iterable để static unroll")
        };
        let values = if is_of {
            match known {
                Value::String(value) => value
                    .chars()
                    .map(|character| Value::String(character.to_string()))
                    .collect::<Vec<_>>(),
                Value::Array(array) => array
                    .borrow()
                    .iter()
                    .map(|value| value.clone().unwrap_or(Value::Undefined))
                    .collect::<Vec<_>>(),
                _ => bail!("for-of static chỉ nhận String/Array iterable"),
            }
        } else {
            ecmora_value::own_property_keys(&known)
                .into_iter()
                .map(Value::String)
                .collect::<Vec<_>>()
        };
        for value in values {
            self.scopes.push(HashMap::new());
            let value = self.emit_value(value);
            self.scopes.last_mut().unwrap().insert(
                name.to_owned(),
                Binding {
                    kind,
                    initialized: true,
                    value_id: value.0,
                    value_type: value.1,
                    value: value.2,
                    cell: None,
                },
            );
            let result = self.lower_statement(body);
            self.scopes.pop();
            result?;
        }
        Ok(())
    }

    fn lower_do_while(&mut self, body: &Statement, test: &Expression) -> Result<()> {
        let preheader = BlockId(self.current as u32);
        let body_block = self.new_block("do.body");
        let test_block = self.new_block("do.test");
        let exit = self.new_block("do.exit");
        self.set_terminator(Terminator::Jump(body_block));

        self.current = body_block.0 as usize;
        let mut phis = Vec::new();
        for scope_index in 0..self.scopes.len() {
            let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
            for name in names {
                let binding = self.scopes[scope_index].get(&name).unwrap().clone();
                if !binding.initialized {
                    continue;
                }
                let result = self.new_value();
                let index = self.blocks[self.current].instructions.len();
                self.emit(Instruction::Phi {
                    result,
                    value_type: binding.value_type,
                    incoming: vec![(preheader, binding.value_id)],
                });
                self.scopes[scope_index].get_mut(&name).unwrap().value_id = result;
                phis.push((scope_index, name, index, result, binding.value_type));
            }
        }
        self.break_targets.push(exit);
        self.break_edges.push(Vec::new());
        self.continue_targets.push(test_block);
        self.continue_edges.push(Vec::new());
        self.lower_statement(body)?;
        let continue_edges = self.continue_edges.pop().unwrap();
        self.continue_targets.pop();
        let break_edges = self.break_edges.pop().unwrap();
        self.break_targets.pop();
        let body_reaches_test = self.blocks[self.current].terminator.is_none();
        let body_end = BlockId(self.current as u32);
        if body_reaches_test {
            self.set_terminator(Terminator::Jump(test_block));
        }
        let body_scopes = self.scopes.clone();

        self.current = test_block.0 as usize;
        if !continue_edges.is_empty() {
            for scope_index in 0..self.scopes.len() {
                let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
                for name in names {
                    let mut incoming = Vec::new();
                    if body_reaches_test {
                        incoming.push((
                            body_end,
                            body_scopes[scope_index].get(&name).unwrap().value_id,
                        ));
                    }
                    for (block, scopes) in &continue_edges {
                        incoming.push((*block, scopes[scope_index].get(&name).unwrap().value_id));
                    }
                    if incoming.len() > 1 {
                        let value_type = body_scopes[scope_index].get(&name).unwrap().value_type;
                        let result = self.new_value();
                        self.emit(Instruction::Phi {
                            result,
                            value_type,
                            incoming,
                        });
                        self.scopes[scope_index].get_mut(&name).unwrap().value_id = result;
                    }
                }
            }
        }
        let test_value = self.lower_expression(test)?;
        let condition = self.to_boolean(test_value)?;
        self.set_terminator(Terminator::Branch {
            condition,
            then_block: body_block,
            else_block: exit,
        });
        let backedge = BlockId(self.current as u32);
        let test_scopes = self.scopes.clone();
        for (scope_index, name, index, _, _) in &phis {
            let value = test_scopes[*scope_index].get(name).unwrap();
            let Instruction::Phi {
                incoming,
                value_type,
                ..
            } = &mut self.blocks[body_block.0 as usize].instructions[*index]
            else {
                unreachable!()
            };
            if *value_type != value.value_type {
                bail!("do-while đổi kiểu binding `{name}`")
            }
            incoming.push((backedge, value.value_id));
        }
        self.current = exit.0 as usize;
        for (scope_index, name, _, _result, value_type) in &phis {
            let binding = self.scopes[*scope_index].get_mut(name).unwrap();
            binding.value_id = test_scopes[*scope_index].get(name).unwrap().value_id;
            binding.value_type = *value_type;
            binding.value = None;
        }
        if !break_edges.is_empty() {
            for scope_index in 0..self.scopes.len() {
                let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
                for name in names {
                    let normal = self.scopes[scope_index].get(&name).unwrap().clone();
                    let mut incoming = vec![(test_block, normal.value_id)];
                    for (block, scopes) in &break_edges {
                        incoming.push((*block, scopes[scope_index].get(&name).unwrap().value_id));
                    }
                    if incoming.len() > 1 {
                        let result = self.new_value();
                        self.emit(Instruction::Phi {
                            result,
                            value_type: normal.value_type,
                            incoming,
                        });
                        self.scopes[scope_index].get_mut(&name).unwrap().value_id = result;
                    }
                }
            }
        }
        Ok(())
    }

    fn lower_switch(
        &mut self,
        discriminant: &Expression,
        cases: &[ecmora_hir::SwitchCase],
    ) -> Result<()> {
        let discriminant = self.lower_expression(discriminant)?;
        let outer_scopes = self.scopes.clone();
        let exit = self.new_block("switch.exit");
        let case_blocks = cases
            .iter()
            .enumerate()
            .map(|(index, _)| self.new_block(format!("switch.case.{index}")))
            .collect::<Vec<_>>();
        let default_target = cases
            .iter()
            .position(|case| case.test.is_none())
            .map(|index| case_blocks[index])
            .unwrap_or(exit);

        let tested = cases
            .iter()
            .enumerate()
            .filter(|(_, case)| case.test.is_some())
            .collect::<Vec<_>>();
        let mut no_match_edge = None;
        let mut dispatch_predecessors = vec![None; cases.len()];
        for (position, (case_index, case)) in tested.iter().enumerate() {
            let test = self.lower_expression(case.test.as_ref().unwrap())?;
            let condition = if discriminant.1 == ValueType::Number && test.1 == ValueType::Number {
                let result = self.new_value();
                self.emit(Instruction::CompareNumber {
                    result,
                    operator: CompareNumberOperator::StrictEqual,
                    left: discriminant.0,
                    right: test.0,
                });
                result
            } else if discriminant.1 == ValueType::String && test.1 == ValueType::String {
                let result = self.new_value();
                self.emit(Instruction::CompareString {
                    result,
                    left: discriminant.0,
                    right: test.0,
                });
                result
            } else {
                let known = match (discriminant.2.clone(), test.2.clone()) {
                    (Some(left), Some(right)) => {
                        ecmora_value::binary(SemBinary::StrictEqual, left, right)?
                            == Value::Bool(true)
                    }
                    _ => bail!("switch discriminant động hiện cần Number/String trong native IR"),
                };
                self.emit_value(Value::Bool(known)).0
            };
            let next = if position + 1 == tested.len() {
                default_target
            } else {
                self.new_block(format!("switch.test.{}", position + 1))
            };
            if next == exit {
                no_match_edge = Some(BlockId(self.current as u32));
            }
            let dispatch_block = BlockId(self.current as u32);
            dispatch_predecessors[*case_index] = Some(dispatch_block);
            if next == default_target {
                if let Some(default_index) = cases.iter().position(|case| case.test.is_none()) {
                    dispatch_predecessors[default_index] = Some(dispatch_block);
                }
            }
            self.set_terminator(Terminator::Branch {
                condition,
                then_block: case_blocks[*case_index],
                else_block: next,
            });
            if next != default_target {
                self.current = next.0 as usize;
            }
        }
        if tested.is_empty() {
            if let Some(default_index) = cases.iter().position(|case| case.test.is_none()) {
                dispatch_predecessors[default_index] = Some(BlockId(self.current as u32));
            }
            self.set_terminator(Terminator::Jump(default_target));
            if default_target == exit {
                no_match_edge = Some(BlockId(self.current as u32));
            }
        }

        self.break_targets.push(exit);
        self.break_edges.push(Vec::new());
        let mut natural_exit_edges = Vec::new();
        let mut previous_fallthrough: Option<(BlockId, Vec<HashMap<String, Binding>>)> = None;
        for (index, case) in cases.iter().enumerate() {
            self.current = case_blocks[index].0 as usize;
            self.scopes = outer_scopes.clone();
            if let Some((previous_block, previous_scopes)) = previous_fallthrough.take() {
                if let Some(dispatch_block) = dispatch_predecessors[index] {
                    self.merge_scope_values(
                        &outer_scopes,
                        dispatch_block,
                        &previous_scopes,
                        previous_block,
                        None,
                    )?;
                } else {
                    self.scopes = previous_scopes;
                }
            }
            for statement in &case.consequent {
                if self.blocks[self.current].terminator.is_some() {
                    break;
                }
                self.lower_statement(statement)?;
            }
            if self.blocks[self.current].terminator.is_none() {
                let target = case_blocks.get(index + 1).copied().unwrap_or(exit);
                if target == exit {
                    natural_exit_edges.push((BlockId(self.current as u32), self.scopes.clone()));
                } else {
                    previous_fallthrough =
                        Some((BlockId(self.current as u32), self.scopes.clone()));
                }
                self.set_terminator(Terminator::Jump(target));
            } else {
                previous_fallthrough = None;
            }
        }
        self.break_targets.pop();
        let mut exit_edges = self.break_edges.pop().unwrap();
        exit_edges.extend(natural_exit_edges);
        if let Some(block) = no_match_edge {
            exit_edges.push((block, outer_scopes.clone()));
        }
        self.current = exit.0 as usize;
        self.scopes = outer_scopes;
        if !exit_edges.is_empty() {
            for scope_index in 0..self.scopes.len() {
                let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
                for name in names {
                    let first = exit_edges[0].1[scope_index].get(&name).unwrap().clone();
                    if exit_edges.iter().all(|(_, scopes)| {
                        scopes[scope_index].get(&name).unwrap().value_id == first.value_id
                    }) {
                        *self.scopes[scope_index].get_mut(&name).unwrap() = first;
                        continue;
                    }
                    let mut value_type = first.value_type;
                    let incoming = exit_edges
                        .iter()
                        .map(|(block, scopes)| {
                            let binding = scopes[scope_index].get(&name).unwrap();
                            if binding.value_type != value_type {
                                value_type = ValueType::Dynamic;
                            }
                            (*block, binding.value_id)
                        })
                        .collect::<Vec<_>>();
                    let result = self.new_value();
                    self.emit(Instruction::Phi {
                        result,
                        value_type,
                        incoming,
                    });
                    let binding = self.scopes[scope_index].get_mut(&name).unwrap();
                    binding.value_id = result;
                    binding.value_type = value_type;
                    binding.value = None;
                }
            }
        }
        Ok(())
    }

    fn to_boolean(&mut self, value: (ValueId, ValueType, Option<Value>)) -> Result<ValueId> {
        if value.1 == ValueType::Bool {
            return Ok(value.0);
        }
        if let Some(known) = value.2 {
            return Ok(self
                .emit_value(Value::Bool(ecmora_value::to_boolean(&known)))
                .0);
        }
        let result = self.new_value();
        self.emit(Instruction::ToBoolean {
            result,
            operand: value.0,
            operand_type: value.1,
        });
        Ok(result)
    }

    fn lower_if(
        &mut self,
        test: &Expression,
        consequent: &Statement,
        alternate: Option<&Statement>,
    ) -> Result<()> {
        let condition_value = self.lower_expression(test)?;
        let condition_is_true = condition_value.2.as_ref().map(ecmora_value::to_boolean);
        let condition = self.to_boolean(condition_value)?;
        let then_block = self.new_block("if.then");
        let else_block = self.new_block("if.else");
        let merge_block = self.new_block("if.merge");
        self.set_terminator(Terminator::Branch {
            condition,
            then_block,
            else_block,
        });

        let outer_scopes = self.scopes.clone();

        self.current = then_block.0 as usize;
        self.scopes = outer_scopes.clone();
        self.lower_statement(consequent)?;
        let then_reaches_merge = self.blocks[self.current].terminator.is_none();
        if then_reaches_merge {
            self.set_terminator(Terminator::Jump(merge_block));
        }
        let then_end = BlockId(self.current as u32);
        let then_scopes = self.scopes.clone();

        self.current = else_block.0 as usize;
        self.scopes = outer_scopes.clone();
        if let Some(alternate) = alternate {
            self.lower_statement(alternate)?;
        }
        let else_reaches_merge = self.blocks[self.current].terminator.is_none();
        if else_reaches_merge {
            self.set_terminator(Terminator::Jump(merge_block));
        }
        let else_end = BlockId(self.current as u32);
        let else_scopes = self.scopes.clone();

        self.current = merge_block.0 as usize;
        match (then_reaches_merge, else_reaches_merge) {
            (true, false) => {
                self.scopes = then_scopes;
                return Ok(());
            }
            (false, true) => {
                self.scopes = else_scopes;
                return Ok(());
            }
            (false, false) => {
                self.scopes = outer_scopes;
                self.set_terminator(Terminator::Unreachable);
                return Ok(());
            }
            (true, true) => {}
        }
        self.scopes = outer_scopes;
        for scope_index in 0..self.scopes.len() {
            let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
            for name in names {
                let then_binding = then_scopes[scope_index].get(&name).unwrap();
                let else_binding = else_scopes[scope_index].get(&name).unwrap();
                if then_binding.value_id == else_binding.value_id {
                    let binding = self.scopes[scope_index].get_mut(&name).unwrap();
                    binding.value_id = then_binding.value_id;
                    binding.value_type = then_binding.value_type;
                    binding.value = match condition_is_true {
                        Some(true) => then_binding.value.clone(),
                        Some(false) => else_binding.value.clone(),
                        None if then_binding.value == else_binding.value => {
                            then_binding.value.clone()
                        }
                        None => None,
                    };
                    binding.initialized = then_binding.initialized && else_binding.initialized;
                    continue;
                }
                let value_type = if then_binding.value_type == else_binding.value_type {
                    then_binding.value_type
                } else {
                    ValueType::Dynamic
                };
                let selected_value = match condition_is_true {
                    Some(true) => then_binding.value.clone(),
                    Some(false) => else_binding.value.clone(),
                    None if then_binding.value == else_binding.value => then_binding.value.clone(),
                    None => None,
                };
                let then_value_id = then_binding.value_id;
                let else_value_id = else_binding.value_id;
                let initialized = then_binding.initialized && else_binding.initialized;
                let result = self.new_value();
                self.emit(Instruction::Phi {
                    result,
                    value_type,
                    incoming: vec![(then_end, then_value_id), (else_end, else_value_id)],
                });
                let binding = self.scopes[scope_index].get_mut(&name).unwrap();
                binding.value_id = result;
                binding.value_type = value_type;
                binding.value = selected_value;
                binding.initialized = initialized;
            }
        }
        Ok(())
    }

    fn lower_expression_with_hint(
        &mut self,
        expression: &Expression,
        expected: Option<ValueType>,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let previous = self.expected_type_hint;
        self.expected_type_hint = expected;
        let result = self.lower_expression(expression);
        self.expected_type_hint = previous;
        result
    }

    fn expression_type_hint(&self, expression: &Expression) -> Option<ValueType> {
        let mut abstract_bindings = HashMap::new();
        let mut simple_bindings = HashMap::new();
        for scope in &self.scopes {
            for (name, binding) in scope {
                if binding.initialized {
                    abstract_bindings.insert(
                        name.clone(),
                        AbstractValue::from_type(binding.value_type, binding.value.clone()),
                    );
                    simple_bindings.insert(name.clone(), binding.value_type);
                }
            }
        }
        abstract_value::evaluate(expression, &abstract_bindings)
            .single_type()
            .or_else(|| infer_expression_type_hint(expression, &simple_bindings, None))
    }

    fn take_direct_tail_call(&mut self, result: ValueId) -> Option<Terminator> {
        let is_tail_call = matches!(
            self.blocks[self.current].instructions.last(),
            Some(Instruction::CallDirect {
                result: call_result,
                ..
            }) if *call_result == result
        );
        if !is_tail_call {
            return None;
        }
        let expected_arity = self.function_arity?;
        let argument_count = match self.blocks[self.current].instructions.last() {
            Some(Instruction::CallDirect { arguments, .. }) => arguments.len(),
            _ => return None,
        };
        if argument_count != expected_arity {
            return None;
        }
        let Instruction::CallDirect {
            function,
            arguments,
            argument_types,
            ..
        } = self.blocks[self.current]
            .instructions
            .pop()
            .expect("tail call instruction disappeared")
        else {
            unreachable!()
        };
        Some(Terminator::TailCallDirect {
            function,
            arguments,
            argument_types,
        })
    }

    fn lower_expression(
        &mut self,
        expression: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        match &expression.kind {
            ExpressionKind::String(value) => Ok(self.emit_value(Value::String(value.clone()))),
            ExpressionKind::Number(value) => Ok(self.emit_value(Value::Number(*value))),
            ExpressionKind::Bool(value) => Ok(self.emit_value(Value::Bool(*value))),
            ExpressionKind::Null => Ok(self.emit_value(Value::Null)),
            ExpressionKind::This => bail!(
                "`this` requires runtime receiver ABI; route this function to compatibility backend"
            ),
            ExpressionKind::Global(name) if name == "@yield" => {
                bail!("async generator cần compatibility request-queue lowering")
            }
            ExpressionKind::Global(name) if name == "@super" => {
                bail!("super reference cần compatibility class-object lowering")
            }
            ExpressionKind::Global(name) => self.lookup(name),
            ExpressionKind::Member { object, property } => self.lower_object_get(object, property),
            ExpressionKind::Object(properties) => {
                let object_id = self.new_value();
                self.emit(Instruction::ObjectNew { result: object_id });
                let object = ecmora_value::object();
                for entry in properties {
                    match entry {
                        ObjectEntry::Property(property) => {
                            let key = self.lower_property_key(&property.key)?;
                            let callable = match &property.value.kind {
                                ExpressionKind::Function(function) => {
                                    let captures = self.capture_environment_for(function);
                                    Some(ClosureBinding {
                                        function: function.clone(),
                                        captures,
                                    })
                                }
                                ExpressionKind::Global(name) => {
                                    if let Some(closure) = self.closure_callables.get(name).cloned()
                                    {
                                        Some(closure)
                                    } else if let Some(function) =
                                        self.function_defs.get(name).cloned()
                                    {
                                        let captures = self.capture_environment_for(&function);
                                        Some(ClosureBinding { function, captures })
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            };
                            if let Some(callable) = callable {
                                self.static_object_callables
                                    .insert((object_id, key), callable);
                                continue;
                            }
                            let value = self.lower_expression(&property.value)?;
                            self.emit(Instruction::ObjectSet {
                                object: object_id,
                                key: key.clone(),
                                value: value.0,
                                value_type: value.1,
                            });
                            if let Some(known) = value.2 {
                                ecmora_value::set_property(&object, key, known)?;
                            }
                        }
                        ObjectEntry::Spread(expression) => {
                            let source = self.lower_expression(expression)?;
                            let Some(source) = source.2 else {
                                bail!("object spread cần known source")
                            };
                            for key in ecmora_value::own_property_keys(&source) {
                                let Some(known) = (match ecmora_value::get_accessor(&source, &key) {
                                    Some(_) => None,
                                    None => Some(ecmora_value::get_property(&source, &key)),
                                }) else {
                                    bail!("object spread accessor cần runtime get")
                                };
                                let value = self.emit_value(known.clone());
                                self.emit(Instruction::ObjectSet {
                                    object: object_id,
                                    key: key.clone(),
                                    value: value.0,
                                    value_type: value.1,
                                });
                                ecmora_value::set_property(&object, key, known)?;
                            }
                        }
                        ObjectEntry::Accessor { key, get, set } => {
                            let getter = if let Some(expression) = get {
                                let ExpressionKind::Function(function) = &expression.kind else {
                                    unreachable!("frontend accessor getter phải là function")
                                };

                                let captures = self.capture_environment_for(function);

                                Some(ClosureBinding {
                                    function: function.clone(),
                                    captures,
                                })
                            } else {
                                None
                            };
                            let setter = if let Some(expression) = set {
                                let ExpressionKind::Function(function) = &expression.kind else {
                                    unreachable!("frontend accessor setter phải là function")
                                };

                                let captures = self.capture_environment_for(function);

                                Some(ClosureBinding {
                                    function: function.clone(),
                                    captures,
                                })
                            } else {
                                None
                            };
                            let entry = self
                                .static_accessors
                                .entry((object_id, key.clone()))
                                .or_default();
                            if getter.is_some() {
                                entry.getter = getter;
                            }
                            if setter.is_some() {
                                entry.setter = setter;
                            }
                            ecmora_value::define_accessor(
                                &object,
                                key.clone(),
                                get.as_ref().map(|_| 0),
                                set.as_ref().map(|_| 0),
                            )?;
                        }
                    }
                }
                Ok((object_id, ValueType::Object, Some(object)))
            }
            ExpressionKind::Array(elements) => {
                let object_id = self.new_value();
                self.emit(Instruction::ObjectNew { result: object_id });
                let mut array_values = Vec::new();
                for element in elements {
                    let values = match element {
                        ArrayElement::Expression(expression) => {
                            vec![Some(self.lower_expression(expression)?)]
                        }
                        ArrayElement::Hole => vec![None],
                        ArrayElement::Spread(expression) => {
                            let source = self.lower_expression(expression)?;
                            let Some(source) = source.2 else {
                                bail!("array spread cần known iterable")
                            };
                            match source {
                                Value::Array(array) => {
                                    array
                                        .borrow()
                                        .iter()
                                        .map(|value| {
                                            Some(self.emit_value(
                                                value.clone().unwrap_or(Value::Undefined),
                                            ))
                                        })
                                        .collect()
                                }
                                Value::String(string) => string
                                    .chars()
                                    .map(|character| {
                                        Some(self.emit_value(Value::String(character.to_string())))
                                    })
                                    .collect(),
                                _ => bail!("array spread static chỉ nhận String/Array"),
                            }
                        }
                    };
                    for value in values {
                        array_values.push(value);
                    }
                }
                let object = ecmora_value::array_with_holes(
                    array_values
                        .iter()
                        .map(|value| value.as_ref().and_then(|value| value.2.clone()))
                        .collect(),
                );
                for (index, value) in array_values.iter().enumerate() {
                    let Some(value) = value else { continue };
                    let key = index.to_string();
                    self.emit(Instruction::ObjectSet {
                        object: object_id,
                        key: key.clone(),
                        value: value.0,
                        value_type: value.1,
                    });
                    if let Some(known) = &value.2 {
                        ecmora_value::set_property(&object, key, known.clone())?;
                    }
                }
                let length = self.emit_value(Value::Number(array_values.len() as f64));
                self.emit(Instruction::ObjectSet {
                    object: object_id,
                    key: "length".to_owned(),
                    value: length.0,
                    value_type: ValueType::Number,
                });
                ecmora_value::set_property(
                    &object,
                    "length".to_owned(),
                    Value::Number(array_values.len() as f64),
                )?;
                Ok((object_id, ValueType::Object, Some(object)))
            }
            ExpressionKind::Conditional {
                test,
                consequent,
                alternate,
            } => self.lower_conditional(test, consequent, alternate),
            ExpressionKind::Unary { operator, argument } => {
                if *operator == UnaryOperator::Delete {
                    return match &argument.kind {
                        ExpressionKind::Member { object, property } => {
                            let object = self.lower_expression(object)?;
                            if object.1 != ValueType::Object {
                                bail!("delete property cần Object")
                            }
                            let key = self.lower_property_key(property)?;
                            let result = self.new_value();
                            self.emit(Instruction::ObjectDelete {
                                result,
                                object: object.0,
                                key: key.clone(),
                            });
                            if let Some(known) = object.2.as_ref() {
                                ecmora_value::delete_property(known, &key);
                            }
                            Ok((result, ValueType::Bool, None))
                        }
                        ExpressionKind::Global(_) => Ok(self.emit_value(Value::Bool(false))),
                        _ => {
                            self.lower_expression(argument)?;
                            Ok(self.emit_value(Value::Bool(true)))
                        }
                    };
                }
                if *operator == UnaryOperator::Typeof {
                    if let ExpressionKind::Global(name) = &argument.kind {
                        if !self.has_binding(name)
                            && !matches!(name.as_str(), "undefined" | "NaN" | "Infinity")
                        {
                            return Ok(self.emit_value(Value::String("undefined".to_owned())));
                        }
                    }
                }
                let operand = self.lower_expression(argument)?;
                if *operator == UnaryOperator::Void {
                    let _ = operand;
                    return Ok(self.emit_value(Value::Undefined));
                }
                if *operator == UnaryOperator::Typeof {
                    let value = match operand.1 {
                        ValueType::Undefined => "undefined",
                        ValueType::Null | ValueType::Object => "object",
                        ValueType::Callable => "function",
                        ValueType::Cell => "object",
                        ValueType::Promise => "object",
                        ValueType::Bool => "boolean",
                        ValueType::Number => "number",
                        ValueType::String => "string",
                        ValueType::Dynamic => {
                            let result = self.new_value();
                            self.emit(Instruction::TypeOfDynamic {
                                result,
                                operand: operand.0,
                            });
                            return Ok((result, ValueType::String, None));
                        }
                    };
                    return Ok(self.emit_value(Value::String(value.to_owned())));
                }
                if operand.1 == ValueType::Number
                    && matches!(
                        operator,
                        UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitwiseNot
                    )
                {
                    let id = self.new_value();
                    self.emit(Instruction::UnaryNumber {
                        result: id,
                        operator: if *operator == UnaryOperator::Plus {
                            UnaryNumberOperator::Plus
                        } else if *operator == UnaryOperator::Minus {
                            UnaryNumberOperator::Minus
                        } else {
                            UnaryNumberOperator::BitwiseNot
                        },
                        operand: operand.0,
                    });
                    let known = operand
                        .2
                        .map(|value| ecmora_value::unary(to_sem_unary(*operator), value));
                    return Ok((id, ValueType::Number, known));
                }
                match operand.2 {
                    Some(value) => {
                        Ok(self.emit_value(ecmora_value::unary(to_sem_unary(*operator), value)))
                    }
                    None => bail!(
                        "unary operation động cho kiểu {:?} chưa được hỗ trợ",
                        operand.1
                    ),
                }
            }
            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => {
                let numeric_context = matches!(
                    operator,
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
                        | BinaryOperator::BitwiseAnd
                );
                let right_hint = self.expression_type_hint(right);
                let left_hint = if numeric_context
                    || (*operator == BinaryOperator::Add && right_hint == Some(ValueType::Number))
                {
                    Some(ValueType::Number)
                } else {
                    None
                };
                let left = self.lower_expression_with_hint(left, left_hint)?;
                if *operator == BinaryOperator::InstanceOf {
                    if let ExpressionKind::Global(name) = &right.kind {
                        if name == "Object" && !self.has_binding(name) {
                            return Ok(self.emit_value(Value::Bool(left.1 == ValueType::Object)));
                        }
                    }
                }
                let right_hint = if numeric_context
                    || (*operator == BinaryOperator::Add && left.1 == ValueType::Number)
                {
                    Some(ValueType::Number)
                } else {
                    None
                };
                let right = self.lower_expression_with_hint(right, right_hint)?;
                let known = match (left.2.clone(), right.2.clone()) {
                    (Some(left), Some(right)) => {
                        Some(ecmora_value::binary(to_sem_binary(*operator), left, right)?)
                    }
                    _ => None,
                };
                if matches!(operator, BinaryOperator::In | BinaryOperator::InstanceOf) {
                    return match known {
                        Some(value) => Ok(self.emit_value(value)),
                        None => bail!("in/instanceof dynamic native IR chưa được hỗ trợ"),
                    };
                }
                if left.1 == ValueType::Number && right.1 == ValueType::Number {
                    if let Some(operator) = number_operator(*operator) {
                        let id = self.new_value();
                        self.emit(Instruction::BinaryNumber {
                            result: id,
                            operator,
                            left: left.0,
                            right: right.0,
                        });
                        return Ok((id, ValueType::Number, known));
                    }
                    if let Some(operator) = compare_operator(*operator) {
                        let id = self.new_value();
                        self.emit(Instruction::CompareNumber {
                            result: id,
                            operator,
                            left: left.0,
                            right: right.0,
                        });
                        return Ok((id, ValueType::Bool, known));
                    }
                }
                if left.1 == ValueType::String
                    && right.1 == ValueType::String
                    && matches!(
                        operator,
                        BinaryOperator::Equal | BinaryOperator::StrictEqual
                    )
                {
                    let id = self.new_value();
                    self.emit(Instruction::CompareString {
                        result: id,
                        left: left.0,
                        right: right.0,
                    });
                    return Ok((id, ValueType::Bool, known));
                }
                if left.1 == ValueType::Object
                    && right.1 == ValueType::Object
                    && matches!(
                        operator,
                        BinaryOperator::Equal
                            | BinaryOperator::NotEqual
                            | BinaryOperator::StrictEqual
                            | BinaryOperator::StrictNotEqual
                    )
                {
                    let id = self.new_value();
                    self.emit(Instruction::CompareObject {
                        result: id,
                        operator: compare_operator(*operator).unwrap(),
                        left: left.0,
                        right: right.0,
                    });
                    return Ok((id, ValueType::Bool, known));
                }
                match known {
                    Some(value) => Ok(self.emit_value(value)),
                    None => {
                        bail!("dynamic/coercing binary operation chưa được hỗ trợ trong native IR")
                    }
                }
            }
            ExpressionKind::Logical {
                left,
                operator,
                right,
            } => {
                let left = self.lower_expression(left)?;
                let Some(known_left) = left.2.as_ref() else {
                    return self.lower_logical_cfg(left, *operator, right);
                };
                let short = match operator {
                    LogicalOperator::Or => ecmora_value::to_boolean(known_left),
                    LogicalOperator::And => !ecmora_value::to_boolean(known_left),
                    LogicalOperator::Nullish => {
                        !matches!(known_left, Value::Null | Value::Undefined)
                    }
                };
                if short {
                    Ok(left)
                } else {
                    self.lower_expression(right)
                }
            }
            ExpressionKind::Assignment {
                target,
                operator,
                value,
            } => match target {
                AssignmentTarget::Identifier(name) => self.lower_assignment(name, *operator, value),
                AssignmentTarget::Member { object, property } => {
                    self.lower_object_assignment(object, property, *operator, value)
                }
            },
            ExpressionKind::Update {
                target,
                operator,
                prefix,
            } => {
                if let AssignmentTarget::Member { object, property } = target {
                    let old = self.lower_object_get(object, property)?;
                    if old.1 != ValueType::Number {
                        bail!("object update ++/-- hiện cần Number")
                    }
                    let one = self.emit_value(Value::Number(1.0));
                    let result = self.new_value();
                    self.emit(Instruction::BinaryNumber {
                        result,
                        operator: if *operator == UpdateOperator::Increment {
                            BinaryNumberOperator::Add
                        } else {
                            BinaryNumberOperator::Subtract
                        },
                        left: old.0,
                        right: one.0,
                    });
                    let object_value = self.lower_expression(object)?;
                    let key = self.lower_property_key(property)?;
                    self.emit(Instruction::ObjectSet {
                        object: object_value.0,
                        key,
                        value: result,
                        value_type: ValueType::Number,
                    });
                    let new = (result, ValueType::Number, None);
                    return Ok(if *prefix { new } else { old });
                }
                let AssignmentTarget::Identifier(name) = target else {
                    unreachable!()
                };
                let old = self.lookup(name)?;
                if old.1 != ValueType::Number {
                    bail!("update ++/-- hiện cần Number trong native IR")
                }
                let one = self.emit_value(Value::Number(1.0));
                let result = self.new_value();
                self.emit(Instruction::BinaryNumber {
                    result,
                    operator: if *operator == UpdateOperator::Increment {
                        BinaryNumberOperator::Add
                    } else {
                        BinaryNumberOperator::Subtract
                    },
                    left: old.0,
                    right: one.0,
                });
                let known = old.2.as_ref().map(|value| {
                    Value::Number(
                        ecmora_value::to_number(value)
                            + if *operator == UpdateOperator::Increment {
                                1.0
                            } else {
                                -1.0
                            },
                    )
                });
                let new = (result, ValueType::Number, known);
                self.store_assignment(name, new.clone(), false)?;
                Ok(if *prefix { new } else { old })
            }
            ExpressionKind::Call { callee, arguments } => self.lower_call(callee, arguments),
            ExpressionKind::New { callee, arguments } => {
                let ExpressionKind::Global(name) = &callee.kind else {
                    bail!("constructor native cần known constructor")
                };
                if name != "Promise" || self.has_binding(name) || arguments.len() != 1 {
                    bail!("constructor native chưa hỗ trợ")
                }
                let ExpressionKind::Function(executor) = &arguments[0].kind else {
                    bail!("Promise executor phải là function")
                };
                self.lower_promise_constructor(executor)
            }
            ExpressionKind::Function(_) => {
                bail!("function value cần closure lowering")
            }
            ExpressionKind::Await(_) => {
                bail!("await cần async continuation lowering")
            }
        }
    }

    fn lower_property_key(&mut self, property: &MemberProperty) -> Result<String> {
        match property {
            MemberProperty::Static(key) => Ok(key.clone()),
            MemberProperty::Computed(expression) => {
                let value = self.lower_expression(expression)?;
                Ok(ecmora_value::to_string(value.2.as_ref().ok_or_else(
                    || {
                        anyhow::anyhow!(
                            "computed property key động chưa được hỗ trợ trong native IR"
                        )
                    },
                )?))
            }
        }
    }

    fn lower_object_get(
        &mut self,
        object_expression: &Expression,
        property: &MemberProperty,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let retain_known_shape = matches!(
            &object_expression.kind,
            ExpressionKind::Global(name) if name.starts_with("@destructure.")
        );
        let object = self.lower_expression(object_expression)?;
        if object.1 != ValueType::Object {
            bail!("property access hiện cần Object")
        }
        let key = self.lower_property_key(property)?;
        if let Some(accessor) = self.static_accessors.get(&(object.0, key.clone())).cloned() {
            if let Some(getter) = accessor.getter {
                let value = self.lower_inline_call(
                    "accessor.get",
                    &getter.function,
                    &[],
                    Some(&getter.captures),
                )?;
                if let Some(callable) = self.last_callable.take() {
                    self.emit(Instruction::ObjectDefineAccessor {
                        object: object.0,
                        key: key.clone(),
                        getter: Some(callable),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    });
                }
                return Ok(value);
            }
            return Ok(self.emit_value(Value::Undefined));
        }
        let shape_value = object
            .2
            .as_ref()
            .map(|object| ecmora_value::get_property(object, &key));
        let value_type = shape_value
            .as_ref()
            .map(type_of)
            .unwrap_or(ValueType::Dynamic);
        if value_type == ValueType::Dynamic {
            bail!("không suy ra được kiểu property `{key}`")
        }
        let result = self.new_value();
        self.emit(Instruction::ObjectGet {
            result,
            object: object.0,
            key,
            value_type,
        });
        // Loads are runtime values; retaining a literal here would make loop
        // exits print the state from the compiler's first abstract iteration.
        Ok((
            result,
            value_type,
            if retain_known_shape {
                shape_value
            } else {
                None
            },
        ))
    }

    fn lower_object_assignment(
        &mut self,
        object_expression: &Expression,
        property: &MemberProperty,
        operator: AssignmentOperator,
        rhs_expression: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let object = self.lower_expression(object_expression)?;
        if object.1 != ValueType::Object {
            bail!("property assignment hiện cần Object")
        }
        let key = self.lower_property_key(property)?;
        if operator == AssignmentOperator::Assign {
            if let Some(accessor) = self.static_accessors.get(&(object.0, key.clone())).cloned() {
                if let Some(setter) = accessor.setter {
                    let value = self.lower_expression(rhs_expression)?;
                    let temporary = format!("@accessor.arg.{}", self.next_value);
                    self.scopes.last_mut().unwrap().insert(
                        temporary.clone(),
                        Binding {
                            kind: VariableKind::Let,
                            initialized: true,
                            value_id: value.0,
                            value_type: value.1,
                            value: value.2.clone(),
                            cell: None,
                        },
                    );
                    let argument = Expression {
                        kind: ExpressionKind::Global(temporary.clone()),
                        span: rhs_expression.span,
                    };
                    self.lower_inline_call(
                        "accessor.set",
                        &setter.function,
                        &[argument],
                        Some(&setter.captures),
                    )?;
                    if let Some(callable) = self.last_callable.take() {
                        self.emit(Instruction::ObjectDefineAccessor {
                            object: object.0,
                            key: key.clone(),
                            getter: None,
                            setter: Some(callable),
                            enumerable: true,
                            configurable: true,
                        });
                    }
                    self.scopes.last_mut().unwrap().remove(&temporary);
                    return Ok(value);
                }
            }
        }
        let value = if operator == AssignmentOperator::Assign {
            self.lower_expression(rhs_expression)?
        } else {
            let old_shape = object
                .2
                .as_ref()
                .map(|object| ecmora_value::get_property(object, &key));
            let old_type = old_shape
                .as_ref()
                .map(type_of)
                .unwrap_or(ValueType::Dynamic);
            let old_id = self.new_value();
            self.emit(Instruction::ObjectGet {
                result: old_id,
                object: object.0,
                key: key.clone(),
                value_type: old_type,
            });
            let rhs = self.lower_expression(rhs_expression)?;
            let binary = assignment_binary(operator).ok_or_else(|| {
                anyhow::anyhow!("logical object assignment động chưa được hỗ trợ")
            })?;
            if old_type != ValueType::Number || rhs.1 != ValueType::Number {
                bail!("compound object assignment hiện cần Number")
            }
            let native_operator = number_operator_for_sem(binary)
                .ok_or_else(|| anyhow::anyhow!("compound object operator chưa được hỗ trợ"))?;
            let result = self.new_value();
            self.emit(Instruction::BinaryNumber {
                result,
                operator: native_operator,
                left: old_id,
                right: rhs.0,
            });
            (result, ValueType::Number, None)
        };
        self.emit(Instruction::ObjectSet {
            object: object.0,
            key: key.clone(),
            value: value.0,
            value_type: value.1,
        });
        if let (Some(object), Some(known)) = (object.2.as_ref(), value.2.clone()) {
            ecmora_value::set_property(object, key, known)?;
        }
        Ok(value)
    }

    fn lower_conditional(
        &mut self,
        test: &Expression,
        consequent: &Expression,
        alternate: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let test = self.lower_expression(test)?;
        let known_test = test.2.as_ref().map(ecmora_value::to_boolean);
        let condition = self.to_boolean(test)?;
        let then_block = self.new_block("conditional.then");
        let else_block = self.new_block("conditional.else");
        let merge_block = self.new_block("conditional.merge");
        self.set_terminator(Terminator::Branch {
            condition,
            then_block,
            else_block,
        });
        let scopes = self.scopes.clone();

        self.current = then_block.0 as usize;
        self.scopes = scopes.clone();
        let then_value = self.lower_expression(consequent)?;
        let then_end = BlockId(self.current as u32);
        self.set_terminator(Terminator::Jump(merge_block));
        let then_scopes = self.scopes.clone();

        self.current = else_block.0 as usize;
        self.scopes = scopes.clone();
        let else_value = self.lower_expression(alternate)?;
        let else_end = BlockId(self.current as u32);
        self.set_terminator(Terminator::Jump(merge_block));
        let else_scopes = self.scopes.clone();

        self.current = merge_block.0 as usize;
        self.scopes = scopes;
        self.merge_scope_values(&then_scopes, then_end, &else_scopes, else_end, known_test)?;
        let value_type = if then_value.1 == else_value.1 {
            then_value.1
        } else {
            ValueType::Dynamic
        };
        let result = self.new_value();
        self.emit(Instruction::Phi {
            result,
            value_type,
            incoming: vec![(then_end, then_value.0), (else_end, else_value.0)],
        });
        let known = match known_test {
            Some(true) => then_value.2,
            Some(false) => else_value.2,
            None if then_value.2 == else_value.2 => then_value.2,
            None => None,
        };
        Ok((result, value_type, known))
    }

    fn lower_logical_cfg(
        &mut self,
        left: (ValueId, ValueType, Option<Value>),
        operator: LogicalOperator,
        right: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        if operator == LogicalOperator::Nullish {
            return match left.1 {
                ValueType::Undefined | ValueType::Null => self.lower_expression(right),
                ValueType::Dynamic => bail!("dynamic ?? chưa được hỗ trợ trong native IR"),
                _ => Ok(left),
            };
        }
        let condition = self.to_boolean(left.clone())?;
        let rhs_block = self.new_block("logical.rhs");
        let short_block = self.new_block("logical.short");
        let merge_block = self.new_block("logical.merge");
        let (then_block, else_block) = if operator == LogicalOperator::Or {
            (short_block, rhs_block)
        } else {
            (rhs_block, short_block)
        };
        self.set_terminator(Terminator::Branch {
            condition,
            then_block,
            else_block,
        });
        self.current = short_block.0 as usize;
        self.set_terminator(Terminator::Jump(merge_block));
        self.current = rhs_block.0 as usize;
        let rhs = self.lower_expression(right)?;
        let rhs_end = BlockId(self.current as u32);
        self.set_terminator(Terminator::Jump(merge_block));
        self.current = merge_block.0 as usize;
        let value_type = if left.1 == rhs.1 {
            left.1
        } else {
            ValueType::Dynamic
        };
        let result = self.new_value();
        self.emit(Instruction::Phi {
            result,
            value_type,
            incoming: vec![(short_block, left.0), (rhs_end, rhs.0)],
        });
        Ok((result, value_type, None))
    }

    fn merge_scope_values(
        &mut self,
        left_scopes: &[HashMap<String, Binding>],
        left_block: BlockId,
        right_scopes: &[HashMap<String, Binding>],
        right_block: BlockId,
        selected: Option<bool>,
    ) -> Result<()> {
        for scope_index in 0..self.scopes.len() {
            let names = self.scopes[scope_index].keys().cloned().collect::<Vec<_>>();
            for name in names {
                let left = left_scopes[scope_index].get(&name).unwrap();
                let right = right_scopes[scope_index].get(&name).unwrap();
                let binding = self.scopes[scope_index].get_mut(&name).unwrap();
                binding.initialized = left.initialized && right.initialized;
                if left.value_id == right.value_id {
                    *binding = left.clone();
                    if selected.is_none() && left.value != right.value {
                        binding.value = None;
                    }
                    continue;
                }
                let value_type = if left.value_type == right.value_type {
                    left.value_type
                } else {
                    ValueType::Dynamic
                };
                let result = self.new_value();
                self.emit(Instruction::Phi {
                    result,
                    value_type,
                    incoming: vec![(left_block, left.value_id), (right_block, right.value_id)],
                });
                let binding = self.scopes[scope_index].get_mut(&name).unwrap();
                binding.value_id = result;
                binding.value_type = value_type;
                binding.value = match selected {
                    Some(true) => left.value.clone(),
                    Some(false) => right.value.clone(),
                    None if left.value == right.value => left.value.clone(),
                    None => None,
                };
            }
        }
        Ok(())
    }

    fn lower_assignment(
        &mut self,
        name: &str,
        operator: AssignmentOperator,
        expression: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let old = match self.lookup(name) {
            Ok(value) => Some(value),
            Err(error) if self.has_binding(name) => return Err(error),
            Err(_) => None,
        };
        if operator == AssignmentOperator::Assign {
            if let ExpressionKind::Function(function) = &expression.kind {
                let captures = self.capture_environment_for(function);
                self.closure_callables.insert(
                    name.to_owned(),
                    ClosureBinding {
                        function: function.clone(),
                        captures,
                    },
                );
                let placeholder = self.emit_value(Value::Undefined);
                let value = (placeholder.0, ValueType::Callable, None);
                return self.store_assignment(name, value, old.is_none());
            }
            self.closure_callables.remove(name);
            let value = self.lower_expression(expression)?;
            return self.store_assignment(name, value, old.is_none());
        }
        let Some(old) = old else {
            bail!("identifier `{name}` chưa được khai báo")
        };
        let should_skip = match (operator, old.2.as_ref()) {
            (AssignmentOperator::LogicalOr, Some(value)) => ecmora_value::to_boolean(value),
            (AssignmentOperator::LogicalAnd, Some(value)) => !ecmora_value::to_boolean(value),
            (AssignmentOperator::LogicalNullish, Some(value)) => {
                !matches!(value, Value::Null | Value::Undefined)
            }
            (
                AssignmentOperator::LogicalOr
                | AssignmentOperator::LogicalAnd
                | AssignmentOperator::LogicalNullish,
                None,
            ) => bail!("logical assignment động chưa được hỗ trợ trong native IR"),
            _ => false,
        };
        if should_skip {
            return Ok(old);
        }
        let rhs = self.lower_expression(expression)?;
        let value = match operator {
            AssignmentOperator::LogicalOr
            | AssignmentOperator::LogicalAnd
            | AssignmentOperator::LogicalNullish => rhs,
            _ => {
                let binary = assignment_binary(operator)
                    .ok_or_else(|| anyhow::anyhow!("assignment operator chưa hỗ trợ"))?;
                let known = match (old.2.clone(), rhs.2.clone()) {
                    (Some(left), Some(right)) => Some(ecmora_value::binary(binary, left, right)?),
                    _ => None,
                };
                if old.1 == ValueType::Number && rhs.1 == ValueType::Number {
                    let native_operator = number_operator_for_sem(binary).ok_or_else(|| {
                        anyhow::anyhow!("compound operator động chưa được hỗ trợ")
                    })?;
                    let result = self.new_value();
                    self.emit(Instruction::BinaryNumber {
                        result,
                        operator: native_operator,
                        left: old.0,
                        right: rhs.0,
                    });
                    (result, ValueType::Number, known)
                } else if let Some(value) = known {
                    self.emit_value(value)
                } else {
                    bail!("compound coercion động chưa được hỗ trợ")
                }
            }
        };
        self.store_assignment(name, value, false)
    }

    fn store_assignment(
        &mut self,
        name: &str,
        value: (ValueId, ValueType, Option<Value>),
        create_global: bool,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let Some(existing) = self
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .cloned()
        else {
            if create_global && !self.strict {
                self.scopes[0].insert(
                    name.to_owned(),
                    Binding {
                        kind: VariableKind::Let,
                        initialized: true,
                        value_id: value.0,
                        value_type: value.1,
                        value: value.2.clone(),
                        cell: None,
                    },
                );
                return Ok(value);
            }
            bail!("identifier `{name}` chưa được khai báo")
        };
        if !existing.initialized {
            bail!("identifier `{name}` đang ở Temporal Dead Zone")
        }
        if existing.kind == VariableKind::Const {
            bail!("không thể gán lại const `{name}`")
        }
        if let Some(cell) = existing.cell {
            self.emit(Instruction::CellSet {
                cell,
                value: value.0,
                value_type: value.1,
            });
        }
        let binding = self.find_binding_mut(name).unwrap();
        binding.initialized = true;
        binding.value_id = value.0;
        binding.value_type = value.1;
        binding.value = if binding.cell.is_some() {
            None
        } else {
            value.2.clone()
        };
        Ok(value)
    }

    fn lower_call(
        &mut self,
        callee: &Expression,
        arguments: &[Expression],
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        if let ExpressionKind::Global(name) = &callee.kind {
            if name == "@yield" {
                bail!("async generator cần compatibility request-queue lowering")
            }
            if name == "@super" {
                bail!("super() cần compatibility class-constructor lowering")
            }
            if name == "__ecmora_dynamic_import" {
                if arguments.len() != 1 {
                    bail!("import() cần đúng một argument")
                }
                let source = self.lower_expression(&arguments[0])?;
                if source.1 != ValueType::String {
                    bail!("dynamic import source chưa chứng minh được là string")
                }
                let value = self.emit_value(Value::Undefined);
                return self.create_settled_promise(PromiseState::Fulfilled, value);
            }
            if name == "require" {
                if arguments.len() != 1 {
                    bail!("require() cần đúng một argument")
                }
                let source = self.lower_expression(&arguments[0])?;
                if source.1 != ValueType::String {
                    bail!("require source chưa chứng minh được là string")
                }
                let result = self.new_value();
                self.emit(Instruction::ObjectNew { result });
                return Ok((result, ValueType::Object, None));
            }
            if let Some(closure) = self.closure_callables.get(name).cloned() {
                return self.lower_inline_call(
                    name,
                    &closure.function,
                    arguments,
                    Some(&closure.captures),
                );
            }
        }
        if let ExpressionKind::Global(name) = &callee.kind {
            if let Some(callback) = self.inline_callables.get(name).cloned() {
                if callback.function.r#async {
                    return self.lower_async_call(
                        name,
                        &callback.function,
                        arguments,
                        Some(&callback.captures),
                    );
                }

                return self.lower_inline_call(
                    name,
                    &callback.function,
                    arguments,
                    Some(&callback.captures),
                );
            }

            if let Some(function) = self.function_defs.get(name).cloned() {
                if function.r#async {
                    let captures = self.capture_environment_for(&function);
                    return self.lower_async_call(name, &function, arguments, Some(&captures));
                }

                let captures = self.capture_environment_for(&function);

                return self.lower_inline_call(name, &function, arguments, Some(&captures));
            }
        }
        if let ExpressionKind::Global(name) = &callee.kind {
            if matches!(name.as_str(), "Number" | "String" | "Boolean") && !self.has_binding(name) {
                if arguments.len() > 1 {
                    bail!("{name}(...) chỉ nhận tối đa một argument");
                }
                let value = match name.as_str() {
                    "Number" => match arguments.first() {
                        Some(argument) => Value::Number(ecmora_value::to_number(
                            self.lower_expression(argument)?.2.as_ref().ok_or_else(|| {
                                anyhow::anyhow!("Number(dynamic) chưa được hỗ trợ")
                            })?,
                        )),
                        None => Value::Number(0.0),
                    },
                    "String" => match arguments.first() {
                        Some(argument) => Value::String(ecmora_value::to_string(
                            self.lower_expression(argument)?.2.as_ref().ok_or_else(|| {
                                anyhow::anyhow!("String(dynamic) chưa được hỗ trợ")
                            })?,
                        )),
                        None => Value::String(String::new()),
                    },
                    "Boolean" => match arguments.first() {
                        Some(argument) => Value::Bool(ecmora_value::to_boolean(
                            self.lower_expression(argument)?.2.as_ref().ok_or_else(|| {
                                anyhow::anyhow!("Boolean(dynamic) chưa được hỗ trợ")
                            })?,
                        )),
                        None => Value::Bool(false),
                    },
                    _ => unreachable!(),
                };
                return Ok(self.emit_value(value));
            }
        }
        if let ExpressionKind::Member { object, property } = &callee.kind {
            if let MemberProperty::Static(key) = property
                && !matches!(&object.kind, ExpressionKind::Global(name) if name == "console" || name == "Promise" || name == "Object")
            {
                let object_value = self.lower_expression(object)?;
                if let Some(callable) = self
                    .static_object_callables
                    .get(&(object_value.0, key.clone()))
                    .cloned()
                {
                    return self.lower_inline_call(
                        "object.callback",
                        &callable.function,
                        arguments,
                        Some(&callable.captures),
                    );
                }
            }
            if let (ExpressionKind::Global(object_name), MemberProperty::Static(method)) =
                (&object.kind, property)
            {
                if object_name == "Promise" && !self.has_binding(object_name) {
                    match method.as_str() {
                        "resolve" => {
                            let value = match arguments.first() {
                                Some(argument) => self.lower_expression(argument)?,
                                None => self.emit_value(Value::Undefined),
                            };
                            for extra in arguments.iter().skip(1) {
                                self.lower_expression(extra)?;
                            }
                            if value.1 == ValueType::Promise {
                                // Built-in Promise.resolve identity fast path.
                                return Ok(value);
                            }
                            return self.create_settled_promise(PromiseState::Fulfilled, value);
                        }
                        "reject" => {
                            let reason = match arguments.first() {
                                Some(argument) => self.lower_expression(argument)?,
                                None => self.emit_value(Value::Undefined),
                            };
                            for extra in arguments.iter().skip(1) {
                                self.lower_expression(extra)?;
                            }
                            return self.create_settled_promise(PromiseState::Rejected, reason);
                        }
                        _ => {}
                    }
                }
            }

            let promise_object = if matches!(
                &object.kind,
                ExpressionKind::Global(name)
                    if name == "Promise" || name == "Object" || name == "console"
            ) {
                None
            } else {
                Some(self.lower_expression(object)?)
            };
            if let Some(promise_object) =
                promise_object.filter(|value| value.1 == ValueType::Promise)
            {
                let MemberProperty::Static(method) = property else {
                    bail!("computed Promise method chưa hỗ trợ")
                };
                let (on_fulfilled, on_rejected, kind, consumed) = match method.as_str() {
                    "then" => (
                        self.promise_handler_from_argument(arguments.first())?,
                        self.promise_handler_from_argument(arguments.get(1))?,
                        PromiseChainKind::Then,
                        2,
                    ),
                    "catch" => (
                        None,
                        self.promise_handler_from_argument(arguments.first())?,
                        PromiseChainKind::Then,
                        1,
                    ),
                    "finally" => (
                        self.promise_handler_from_argument(arguments.first())?,
                        None,
                        PromiseChainKind::Finally,
                        1,
                    ),
                    _ => bail!("Promise method `{method}` chưa hỗ trợ"),
                };
                for extra in arguments.iter().skip(consumed) {
                    self.lower_expression(extra)?;
                }

                let result = self.create_pending_promise();
                self.promise_chains.insert(
                    result.0,
                    PromiseChain {
                        parent: promise_object.0,
                        on_fulfilled,
                        on_rejected,
                        kind,
                    },
                );
                return Ok(result);
            }
            if let (ExpressionKind::Global(object_name), MemberProperty::Static(method)) =
                (&object.kind, property)
            {
                if object_name == "Object" && !self.has_binding(object_name) {
                    match method.as_str() {
                        "create" => {
                            if arguments.len() != 1 {
                                bail!("Object.create cần đúng một argument")
                            }
                            let prototype = self.lower_expression(&arguments[0])?;
                            if !matches!(prototype.1, ValueType::Object | ValueType::Null) {
                                bail!("Object.create prototype phải là Object hoặc null")
                            }
                            let result = self.new_value();
                            self.emit(Instruction::ObjectNewWithPrototype {
                                result,
                                prototype: prototype.0,
                            });
                            let known = prototype.2.as_ref().map(|prototype| {
                                ecmora_value::object_with_prototype(match prototype {
                                    Value::Object(object) => Some(object.clone()),
                                    Value::Null => None,
                                    _ => unreachable!(),
                                })
                            });
                            return Ok((result, ValueType::Object, known));
                        }
                        "setPrototypeOf" => {
                            if arguments.len() != 2 {
                                bail!("Object.setPrototypeOf cần đúng hai argument")
                            }
                            let target = self.lower_expression(&arguments[0])?;
                            let prototype = self.lower_expression(&arguments[1])?;
                            if target.1 != ValueType::Object
                                || !matches!(prototype.1, ValueType::Object | ValueType::Null)
                            {
                                bail!("Object.setPrototypeOf target/prototype không hợp lệ")
                            }
                            self.emit(Instruction::ObjectSetPrototype {
                                object: target.0,
                                prototype: prototype.0,
                            });
                            if let (Some(Value::Object(target)), Some(prototype)) =
                                (target.2.as_ref(), prototype.2.as_ref())
                            {
                                ecmora_value::set_prototype(
                                    &Value::Object(target.clone()),
                                    match prototype {
                                        Value::Object(object) => Some(object.clone()),
                                        Value::Null => None,
                                        _ => unreachable!(),
                                    },
                                )?;
                            }
                            return Ok(target);
                        }
                        "getPrototypeOf" => {
                            if arguments.len() != 1 {
                                bail!("Object.getPrototypeOf cần đúng một argument")
                            }
                            let target = self.lower_expression(&arguments[0])?;
                            if target.1 != ValueType::Object {
                                bail!("Object.getPrototypeOf target phải là Object")
                            }
                            let result = self.new_value();
                            self.emit(Instruction::ObjectGetPrototype {
                                result,
                                object: target.0,
                            });
                            return Ok((result, ValueType::Object, None));
                        }
                        "getOwnPropertyDescriptor" => {
                            if arguments.len() != 2 {
                                bail!("Object.getOwnPropertyDescriptor cần đúng hai argument")
                            }
                            let ExpressionKind::Global(global) = &arguments[0].kind else {
                                bail!("descriptor native cần globalThis làm target")
                            };
                            if global != "globalThis" {
                                bail!("descriptor native hiện chỉ hỗ trợ globalThis")
                            }
                            let Some(Expression {
                                kind: ExpressionKind::String(name),
                                ..
                            }) = arguments.get(1)
                            else {
                                bail!("descriptor key phải là string literal")
                            };
                            let has_global_function = self.function_defs.contains_key(name)
                                || self
                                    .function_defs
                                    .keys()
                                    .any(|candidate| candidate.ends_with(&format!("_{}", name)));
                            if !has_global_function {
                                return Ok(self.emit_value(Value::Undefined));
                            }
                            let object_id = self.new_value();
                            self.emit(Instruction::ObjectNew { result: object_id });
                            let descriptor = ecmora_value::object();
                            for (key, value) in [
                                ("writable", Value::Bool(true)),
                                ("enumerable", Value::Bool(true)),
                                ("configurable", Value::Bool(false)),
                            ] {
                                let value_id = self.emit_value(value.clone());
                                self.emit(Instruction::ObjectSet {
                                    object: object_id,
                                    key: key.to_owned(),
                                    value: value_id.0,
                                    value_type: value_id.1,
                                });
                                ecmora_value::set_property(&descriptor, key.to_owned(), value)?;
                            }
                            // The callable is represented by the function table at
                            // runtime; descriptor metadata remains statically known.
                            let value = self.emit_value(Value::Undefined);
                            self.emit(Instruction::ObjectSet {
                                object: object_id,
                                key: "value".to_owned(),
                                value: value.0,
                                value_type: value.1,
                            });
                            ecmora_value::set_property(
                                &descriptor,
                                "value".to_owned(),
                                Value::Undefined,
                            )?;
                            return Ok((object_id, ValueType::Object, Some(descriptor)));
                        }
                        _ => {}
                    }
                }
            }
        }
        let ExpressionKind::Member { object, property } = &callee.kind else {
            bail!("chỉ hỗ trợ gọi console.log(...)")
        };
        let ExpressionKind::Global(name) = &object.kind else {
            bail!("callee object phải là console")
        };
        let MemberProperty::Static(property) = property else {
            bail!("computed builtin callee chưa được hỗ trợ")
        };
        if self.has_binding(name) || name != "console" || property != "log" {
            bail!("builtin chưa hỗ trợ: {name}.{property}")
        }
        let mut values = Vec::with_capacity(arguments.len());
        let mut display_values = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let value = self.lower_expression(argument)?;
            values.push(value.0);
            display_values.push(value.2.as_ref().map(ecmora_value::to_string));
        }
        self.emit(Instruction::CallBuiltin {
            builtin: Builtin::ConsoleLog,
            arguments: values,
            display_values,
        });
        Ok(self.emit_value(Value::Undefined))
    }

    fn lower_async_call(
        &mut self,
        name: &str,
        function: &HirFunction,
        arguments: &[Expression],
        captures: Option<&[CapturedBinding]>,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        if function.generator {
            bail!("async generator `{name}` cần compatibility request-queue lowering")
        }
        let normalized_function = normalize_async_function(function)?;
        let function = &normalized_function;
        if let Some(error) = &function.lowering_error {
            bail!("async function `{name}` reachable nhưng frontend không hạ được: {error}")
        }

        let mut values = Vec::with_capacity(function.parameters.len());
        for index in 0..function.parameters.len() {
            values.push(match arguments.get(index) {
                Some(argument) => self.lower_expression(argument)?,
                None => self.emit_value(Value::Undefined),
            });
        }
        for extra in arguments.iter().skip(function.parameters.len()) {
            self.lower_expression(extra)?;
        }

        self.scopes.push(HashMap::new());
        for capture in captures.unwrap_or_default() {
            self.scopes.last_mut().unwrap().insert(
                capture.name.clone(),
                Binding {
                    kind: capture.kind,
                    initialized: true,
                    value_id: capture.cell,
                    value_type: capture.value_type,
                    value: None,
                    cell: Some(capture.cell),
                },
            );
        }
        self.predeclare(&function.body)?;
        for (parameter, value) in function.parameters.iter().zip(&values) {
            self.scopes.last_mut().unwrap().insert(
                parameter.clone(),
                Binding {
                    kind: VariableKind::Let,
                    initialized: true,
                    value_id: value.0,
                    value_type: value.1,
                    value: value.2.clone(),
                    cell: None,
                },
            );
        }

        for (index, statement) in function.body.iter().enumerate() {
            let await_declaration = match &statement.kind {
                StatementKind::VariableDeclaration { declarations, .. }
                    if declarations.len() == 1 =>
                {
                    match &declarations[0].init {
                        Some(Expression {
                            kind: ExpressionKind::Await(argument),
                            ..
                        }) => Some((&declarations[0].name, argument.as_ref())),
                        _ => None,
                    }
                }
                _ => None,
            };
            let await_expression = match &statement.kind {
                StatementKind::Expression(Expression {
                    kind: ExpressionKind::Await(argument),
                    ..
                }) => Some(argument.as_ref()),
                _ => None,
            };
            let return_await = match &statement.kind {
                StatementKind::Return(Some(Expression {
                    kind: ExpressionKind::Await(argument),
                    ..
                })) => Some(argument.as_ref()),
                _ => None,
            };

            let is_boundary = await_declaration.is_some()
                || await_expression.is_some()
                || return_await.is_some()
                || matches!(
                    &statement.kind,
                    StatementKind::Return(_) | StatementKind::Throw(_)
                );
            if !is_boundary {
                continue;
            }

            for previous in &function.body[..index] {
                self.lower_statement(previous)?;
                if self.blocks[self.current].terminator.is_some() {
                    self.scopes.pop();
                    bail!("async control-flow trước await cần general completion CFG lowering")
                }
            }

            if let StatementKind::Throw(reason) = &statement.kind {
                let reason = self.lower_expression(reason)?;
                self.scopes.pop();
                return self.create_settled_promise(PromiseState::Rejected, reason);
            }

            if let StatementKind::Return(value) = &statement.kind {
                if return_await.is_none() {
                    let value = match value {
                        Some(value) => self.lower_expression(value)?,
                        None => self.emit_value(Value::Undefined),
                    };
                    self.scopes.pop();
                    return self.create_settled_promise(PromiseState::Fulfilled, value);
                }
            }

            let awaited_expression = await_declaration
                .map(|(_, expression)| expression)
                .or(await_expression)
                .or(return_await)
                .expect("await boundary");
            let awaited_value = self.lower_expression(awaited_expression)?;
            let awaited_promise = self.coerce_to_promise(awaited_value)?;
            let settlement = self.resolve_promise(awaited_promise.0)?;

            if return_await.is_some() {
                self.scopes.pop();
                return self.create_settled_promise(settlement.state, settlement.value);
            }

            if settlement.state == PromiseState::Rejected {
                self.scopes.pop();
                return self.create_settled_promise(PromiseState::Rejected, settlement.value);
            }

            if let Some((name, _)) = await_declaration {
                let binding = self
                    .find_binding_mut(name)
                    .ok_or_else(|| anyhow::anyhow!("async binding `{name}` không tồn tại"))?;
                binding.initialized = true;
                binding.value_id = settlement.value.0;
                binding.value_type = settlement.value.1;
                binding.value = settlement.value.2.clone();
            }

            let continuation = HirFunction {
                name: None,
                parameters: Vec::new(),
                body: function.body[index + 1..].to_vec(),
                // Recursive continuation lowering supports more than one await.
                r#async: true,
                generator: false,
                arrow: true,
                lowering_error: function.lowering_error.clone(),
            };
            let continuation_captures = self.capture_environment_for(&continuation);
            self.scopes.pop();

            let result = self.create_pending_promise();
            self.promise_chains.insert(
                result.0,
                PromiseChain {
                    parent: awaited_promise.0,
                    on_fulfilled: Some(ClosureBinding {
                        function: continuation,
                        captures: continuation_captures,
                    }),
                    on_rejected: None,
                    kind: PromiseChainKind::Then,
                },
            );
            return Ok(result);
        }

        // No top-level await/return/throw boundary: execute synchronously and
        // fulfill with undefined.
        for statement in &function.body {
            self.lower_statement(statement)?;
            if self.blocks[self.current].terminator.is_some() {
                self.scopes.pop();
                bail!("nested async return/throw cần general completion CFG lowering")
            }
        }
        self.scopes.pop();
        let undefined = self.emit_value(Value::Undefined);
        self.create_settled_promise(PromiseState::Fulfilled, undefined)
    }

    fn emit_specialization_call(
        &mut self,
        function_name: &str,
        return_type: ValueType,
        call_arguments: &[(ValueId, ValueType, Option<Value>)],
        captures: &[CapturedBinding],
    ) -> (ValueId, ValueType, Option<Value>) {
        let result = self.new_value();

        if captures.is_empty() {
            self.last_callable = None;

            self.emit(Instruction::CallDirect {
                result,
                function: function_name.to_owned(),
                arguments: call_arguments.iter().map(|value| value.0).collect(),
                argument_types: call_arguments.iter().map(|value| value.1).collect(),
                return_type,
            });
        } else {
            // Recursive function có closure environment vẫn có thể gọi lại chính
            // nó bằng cách tạo closure mới trỏ tới cùng function body nhưng dùng
            // các Cell capture hiện tại.
            let closure = self.new_value();

            self.emit(Instruction::ClosureNew {
                result: closure,
                function: function_name.to_owned(),
                captures: captures.iter().map(|capture| capture.cell).collect(),
                capture_types: vec![ValueType::Cell; captures.len()],
            });

            self.last_callable = Some(closure);

            self.emit(Instruction::CallIndirect {
                result,
                callee: closure,
                arguments: call_arguments.iter().map(|value| value.0).collect(),
                argument_types: call_arguments.iter().map(|value| value.1).collect(),
                return_type,
            });
        }

        (result, return_type, None)
    }

    fn resolve_callback_argument(&mut self, argument: &Expression) -> Option<ClosureBinding> {
        match &argument.kind {
            ExpressionKind::Function(function) => {
                let captures = self.capture_environment_for(function);
                Some(ClosureBinding {
                    function: function.clone(),
                    captures,
                })
            }
            ExpressionKind::Global(name) => {
                if let Some(callback) = self.inline_callables.get(name).cloned() {
                    Some(callback)
                } else if let Some(callback) = self.closure_callables.get(name).cloned() {
                    Some(callback)
                } else if let Some(function) = self.function_defs.get(name).cloned() {
                    let captures = self.capture_environment_for(&function);
                    Some(ClosureBinding { function, captures })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn lower_inline_call(
        &mut self,
        name: &str,
        function: &HirFunction,
        arguments: &[Expression],
        captures: Option<&[CapturedBinding]>,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        if let Some(error) = &function.lowering_error {
            bail!("function `{name}` reachable nhưng native frontend không hạ được body: {error}")
        }
        if function.generator {
            bail!("generator function `{name}` cần generator state-machine lowering")
        }
        if function.r#async {
            bail!("async function `{name}` phải đi qua async lowering")
        }

        // A call-site specialization keeps concrete ECMAScript types in the
        // function body. Function-valued arguments are devirtualized and do
        // not occupy an argv slot; genuinely unknown callees use CallIndirect.
        let mut call_arguments = Vec::new();
        let mut parameters = Vec::new();
        let mut callbacks = HashMap::new();
        let mut parameter_type_hints = HashMap::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            if let Some(argument) = arguments.get(index) {
                if let Some(callback) = self.resolve_callback_argument(argument) {
                    parameter_type_hints.insert(parameter.clone(), ValueType::Callable);
                    callbacks.insert(parameter.clone(), callback);
                } else {
                    let value = self.lower_expression(argument)?;
                    parameter_type_hints.insert(parameter.clone(), value.1);
                    parameters.push((parameter.clone(), value.1));
                    call_arguments.push(value);
                }
            } else {
                let value = self.emit_value(Value::Undefined);
                parameter_type_hints.insert(parameter.clone(), ValueType::Undefined);
                parameters.push((parameter.clone(), ValueType::Undefined));
                call_arguments.push(value);
            }
        }
        // JavaScript ignores extra arguments unless arguments/rest is observed,
        // but their expressions are still evaluated left-to-right.
        for argument in arguments.iter().skip(function.parameters.len()) {
            self.lower_expression(argument)?;
        }

        let captures = captures.unwrap_or_default();

        let capture_signature = captures
            .iter()
            .map(|capture| (capture.name.clone(), capture.value_type))
            .collect::<Vec<_>>();

        let mut callback_order = callbacks.keys().cloned().collect::<Vec<_>>();
        callback_order.sort();

        let callback_signature = callback_order
            .iter()
            .map(|parameter| {
                (
                    parameter.clone(),
                    callback_specialization_fingerprint(&callbacks[parameter]),
                )
            })
            .collect::<Vec<_>>();

        let mut specialization_captures = captures.to_vec();
        for parameter in &callback_order {
            specialization_captures.extend(callbacks[parameter].captures.iter().cloned());
        }

        let return_seed = self.expected_type_hint.unwrap_or(ValueType::Dynamic);
        let specialization_key = SpecializationKey::new(
            name,
            parameters
                .iter()
                .map(|(_, value_type)| *value_type)
                .collect(),
            capture_signature,
            callback_signature,
            return_seed,
        );

        // Trường hợp function hiện đang được lower: đây chính là recursive
        // hoặc mutually-recursive call.
        if let Some(active) = self
            .active_specializations
            .get(&specialization_key)
            .cloned()
        {
            return Ok(self.emit_specialization_call(
                &active.function_name,
                active.return_type,
                &call_arguments,
                &specialization_captures,
            ));
        }

        // Captures are ABI slots and callback bodies are part of the key, so
        // these specializations are reusable across closure instances.
        let cacheable = true;

        if cacheable {
            if let Some((function_name, return_type)) =
                self.specializations.get(&specialization_key).cloned()
            {
                return Ok(self.emit_specialization_call(
                    &function_name,
                    return_type,
                    &call_arguments,
                    &specialization_captures,
                ));
            }
        }

        let inferred_return_type =
            infer_function_return_type(function, &parameter_type_hints, captures);
        let declared_return_type = if inferred_return_type == ValueType::Dynamic {
            self.expected_type_hint.unwrap_or(ValueType::Dynamic)
        } else {
            inferred_return_type
        };

        let specialization_count = self
            .specialization_counts
            .entry(name.to_owned())
            .or_default();
        if *specialization_count >= MAX_SPECIALIZATIONS_PER_FUNCTION {
            bail!(
                "function `{name}` vượt quá {MAX_SPECIALIZATIONS_PER_FUNCTION} native specializations;                  recursion/callback types không hội tụ"
            )
        }
        *specialization_count += 1;

        let specialization_id = self.next_function;
        self.next_function += 1;

        let function_name = format!("js.{}.{}", sanitize_function_name(name), specialization_id,);

        // Đây là function predeclaration ở tầng analysis.
        //
        // Từ thời điểm này, recursive calls có thể phát CallDirect/CallIndirect
        // tới function_name dù body chưa được lower xong.
        self.active_specializations.insert(
            specialization_key.clone(),
            ActiveSpecialization {
                function_name: function_name.clone(),
                return_type: declared_return_type,
            },
        );
        let mut child = Lowerer {
            next_value: self.next_value,
            blocks: vec![PendingBlock {
                name: "entry".to_owned(),
                instructions: Vec::new(),
                terminator: None,
            }],
            current: 0,
            scopes: vec![HashMap::new()],
            strict: self.strict,
            function_defs: self.function_defs.clone(),
            inline_callables: HashMap::new(),
            closure_callables: self.closure_callables.clone(),
            function_mode: true,
            next_function: self.next_function,
            specializations: self.specializations.clone(),
            active_specializations: self.active_specializations.clone(),
            specialization_counts: self.specialization_counts.clone(),
            function_return_hint: Some(declared_return_type),
            function_arity: Some(parameters.len()),
            ..Default::default()
        };
        let mut ir_captures = Vec::with_capacity(specialization_captures.len());
        for (index, capture) in specialization_captures.iter().enumerate() {
            let value = child.new_value();
            child.emit(Instruction::Capture {
                result: value,
                index: index as u32,
                value_type: ValueType::Cell,
            });
            ir_captures.push(Parameter {
                name: if index < captures.len() {
                    capture.name.clone()
                } else {
                    format!("@callback.capture.{index}.{}", capture.name)
                },
                value,
                value_type: ValueType::Cell,
            });
            if index < captures.len() {
                child.scopes[0].insert(
                    capture.name.clone(),
                    Binding {
                        kind: capture.kind,
                        initialized: true,
                        value_id: value,
                        value_type: capture.value_type,
                        value: None,
                        cell: Some(value),
                    },
                );
            }
        }

        let mut callback_capture_offset = captures.len();
        for parameter in &callback_order {
            let callback = callbacks[parameter].clone();
            let remapped_captures = callback
                .captures
                .iter()
                .enumerate()
                .map(|(index, capture)| CapturedBinding {
                    name: capture.name.clone(),
                    kind: capture.kind,
                    cell: ir_captures[callback_capture_offset + index].value,
                    value_type: capture.value_type,
                })
                .collect::<Vec<_>>();
            callback_capture_offset += callback.captures.len();
            child.inline_callables.insert(
                parameter.clone(),
                ClosureBinding {
                    function: callback.function,
                    captures: remapped_captures,
                },
            );
        }
        let mut ir_parameters = Vec::with_capacity(parameters.len());
        for (index, (parameter, value_type)) in parameters.iter().enumerate() {
            let value = child.new_value();
            child.emit(Instruction::Parameter {
                result: value,
                index: index as u32,
                value_type: *value_type,
            });
            ir_parameters.push(Parameter {
                name: parameter.clone(),
                value,
                value_type: *value_type,
            });
            child.scopes[0].insert(
                parameter.clone(),
                Binding {
                    kind: VariableKind::Let,
                    initialized: true,
                    value_id: value,
                    value_type: *value_type,
                    value: None,
                    cell: None,
                },
            );
        }
        child.lower_scope(&function.body)?;
        if child.blocks[child.current].terminator.is_none() {
            let undefined = child.emit_value(Value::Undefined);
            child.return_types.push(ValueType::Undefined);
            child.set_terminator(Terminator::ReturnValue {
                value: undefined.0,
                value_type: ValueType::Undefined,
            });
        }
        if declared_return_type != ValueType::Dynamic {
            for actual in &child.return_types {
                if *actual != declared_return_type {
                    bail!(
                        "recursive specialization `{name}` được predeclare trả \
                        {:?}, nhưng body có return {:?}",
                        declared_return_type,
                        actual,
                    )
                }
            }
        }

        let return_type = declared_return_type;
        let blocks = std::mem::take(&mut child.blocks)
            .into_iter()
            .map(|block| BasicBlock {
                name: block.name,
                instructions: block.instructions,
                terminator: block.terminator.unwrap_or(Terminator::Unreachable),
            })
            .collect();
        let generated = Function {
            name: function_name.clone(),
            parameters: ir_parameters,
            captures: ir_captures,
            return_type: Some(return_type),
            blocks,
        };
        self.next_value = child.next_value;
        self.next_function = child.next_function;
        self.specializations = child.specializations;
        self.specialization_counts = child.specialization_counts;
        self.active_specializations.remove(&specialization_key);
        self.generated_functions
            .append(&mut child.generated_functions);
        self.generated_functions.push(generated);

        if cacheable {
            self.specializations
                .insert(specialization_key, (function_name.clone(), return_type));
        }

        Ok(self.emit_specialization_call(
            &function_name,
            return_type,
            &call_arguments,
            &specialization_captures,
        ))
    }

    fn capture_environment_for(&mut self, function: &HirFunction) -> Vec<CapturedBinding> {
        let free_names = collect_free_variables(function);

        let callable_names = self
            .closure_callables
            .keys()
            .cloned()
            .collect::<HashSet<_>>();

        // Sắp xếp để thứ tự capture ổn định giữa các lần build.
        let mut free_names = free_names.into_iter().collect::<Vec<_>>();
        free_names.sort();

        let mut bindings = Vec::new();

        for name in free_names {
            // Function-valued binding hiện được lower thông qua closure_callables,
            // chưa được truyền như một runtime Cell thông thường.
            if callable_names.contains(&name) {
                continue;
            }

            // Một identifier có thể bị shadow. Chỉ capture binding gần nhất.
            let binding = self
                .scopes
                .iter()
                .enumerate()
                .rev()
                .find_map(|(scope_index, scope)| {
                    scope
                        .get(&name)
                        .cloned()
                        .map(|binding| (scope_index, binding))
                });

            let Some((scope_index, binding)) = binding else {
                // Builtin như console, Promise, Object hoặc một function được
                // quản lý bởi function_defs không phải lexical capture.
                continue;
            };

            if !binding.initialized {
                // Không capture binding vẫn đang ở TDZ.
                continue;
            }

            bindings.push((scope_index, name, binding));
        }

        let mut captures = Vec::with_capacity(bindings.len());

        for (scope_index, name, binding) in bindings {
            let cell = if let Some(cell) = binding.cell {
                cell
            } else {
                let cell = self.new_value();

                self.emit(Instruction::CellNew {
                    result: cell,
                    value: binding.value_id,
                    value_type: binding.value_type,
                });

                let outer_binding = self.scopes[scope_index]
                    .get_mut(&name)
                    .expect("captured binding phải còn tồn tại");

                outer_binding.cell = Some(cell);

                // Từ thời điểm biến nằm trong Cell, compiler không được giữ
                // literal value cũ làm nguồn chân lý nữa.
                outer_binding.value = None;

                cell
            };

            captures.push(CapturedBinding {
                name,
                kind: binding.kind,
                cell,
                value_type: binding.value_type,
            });
        }

        captures
    }
    fn resolve_static_thenable(
        &mut self,
        object: ValueId,
        then: &ClosureBinding,
    ) -> Result<Option<PromiseSettlement>> {
        if !self.thenable_resolution_stack.insert(object) {
            bail!("cyclic static thenable resolution tại %v{}", object.0)
        }
        let result = (|| {
            let resolve_name = then.function.parameters.first().cloned();
            let reject_name = then.function.parameters.get(1).cloned();

            for statement in &then.function.body {
                if let StatementKind::Throw(reason) = &statement.kind {
                    return Ok(Some(PromiseSettlement {
                        state: PromiseState::Rejected,
                        value: self.lower_expression(reason)?,
                    }));
                }

                let expression = match &statement.kind {
                    StatementKind::Expression(expression)
                    | StatementKind::Return(Some(expression)) => expression,
                    StatementKind::Return(None) => return Ok(None),
                    StatementKind::FunctionDeclaration(_)
                    | StatementKind::VariableDeclaration { .. } => continue,
                    _ => {
                        bail!(
                            "dynamic control flow trong thenable `then` dùng compatibility backend"
                        )
                    }
                };
                let ExpressionKind::Call { callee, arguments } = &expression.kind else {
                    self.lower_expression(expression)?;
                    continue;
                };
                let ExpressionKind::Global(name) = &callee.kind else {
                    bail!("dynamic thenable callee dùng compatibility backend")
                };
                let state = if resolve_name.as_deref() == Some(name.as_str()) {
                    Some(PromiseState::Fulfilled)
                } else if reject_name.as_deref() == Some(name.as_str()) {
                    Some(PromiseState::Rejected)
                } else {
                    None
                };
                let Some(state) = state else {
                    self.lower_expression(expression)?;
                    continue;
                };
                let value = match arguments.first() {
                    Some(argument) => self.lower_expression(argument)?,
                    None => self.emit_value(Value::Undefined),
                };
                for extra in arguments.iter().skip(1) {
                    self.lower_expression(extra)?;
                }
                return Ok(Some(PromiseSettlement { state, value }));
            }
            Ok(None)
        })();
        self.thenable_resolution_stack.remove(&object);
        result
    }

    fn create_pending_promise(&mut self) -> (ValueId, ValueType, Option<Value>) {
        let result = self.new_value();
        self.emit(Instruction::PromisePending { result });
        self.promise_order.push(result);
        (result, ValueType::Promise, None)
    }

    fn create_settled_promise(
        &mut self,
        state: PromiseState,
        value: (ValueId, ValueType, Option<Value>),
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        if state == PromiseState::Fulfilled && value.1 == ValueType::Object {
            if self
                .static_accessors
                .contains_key(&(value.0, "then".to_owned()))
            {
                bail!("observable then accessor requires compatibility Promise resolution")
            }
            if let Some(then) = self
                .static_object_callables
                .get(&(value.0, "then".to_owned()))
                .cloned()
            {
                return match self.resolve_static_thenable(value.0, &then)? {
                    Some(settlement) => {
                        self.create_settled_promise(settlement.state, settlement.value)
                    }
                    None => Ok(self.create_pending_promise()),
                };
            }
            if value.2.is_none() {
                bail!("unknown Object may be a thenable; use compatibility Promise resolution")
            }
        }

        /*
         * Resolving a distinct promise with a native promise adopts it. Keep a
         * distinct capability token; Promise.resolve(x) performs its identity
         * fast path before entering this helper.
         */
        if state == PromiseState::Fulfilled && value.1 == ValueType::Promise {
            let result = self.create_pending_promise();
            self.promise_chains.insert(
                result.0,
                PromiseChain {
                    parent: value.0,
                    on_fulfilled: None,
                    on_rejected: None,
                    kind: PromiseChainKind::Then,
                },
            );
            return Ok(result);
        }

        let result = self.new_value();
        match state {
            PromiseState::Fulfilled => self.emit(Instruction::PromiseResolved {
                result,
                value: value.0,
                value_type: value.1,
            }),
            PromiseState::Rejected => self.emit(Instruction::PromiseRejected {
                result,
                reason: value.0,
                reason_type: value.1,
            }),
        }
        self.promise_settlements
            .insert(result, PromiseSettlement { state, value });
        self.promise_order.push(result);
        Ok((result, ValueType::Promise, None))
    }

    fn settle_existing_promise(
        &mut self,
        token: ValueId,
        settlement: PromiseSettlement,
    ) -> Result<PromiseSettlement> {
        if let Some(existing) = self.promise_settlements.get(&token) {
            return Ok(existing.clone());
        }
        self.emit(Instruction::PromiseSettle {
            promise: token,
            value: settlement.value.0,
            value_type: settlement.value.1,
            rejected: settlement.state == PromiseState::Rejected,
        });
        self.promise_settlements.insert(token, settlement.clone());
        Ok(settlement)
    }

    fn coerce_to_promise(
        &mut self,
        value: (ValueId, ValueType, Option<Value>),
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        if value.1 == ValueType::Promise {
            Ok(value)
        } else {
            self.create_settled_promise(PromiseState::Fulfilled, value)
        }
    }

    fn promise_handler_from_argument(
        &mut self,
        argument: Option<&Expression>,
    ) -> Result<Option<ClosureBinding>> {
        let Some(argument) = argument else {
            return Ok(None);
        };
        match &argument.kind {
            ExpressionKind::Function(function) => {
                let captures = self.capture_environment_for(function);
                Ok(Some(ClosureBinding {
                    function: function.clone(),
                    captures,
                }))
            }
            ExpressionKind::Global(name) if name == "undefined" => Ok(None),
            ExpressionKind::Global(name) => {
                if let Some(handler) = self.inline_callables.get(name).cloned() {
                    return Ok(Some(handler));
                }
                if let Some(handler) = self.closure_callables.get(name).cloned() {
                    return Ok(Some(handler));
                }
                if let Some(function) = self.function_defs.get(name).cloned() {
                    let captures = self.capture_environment_for(&function);
                    return Ok(Some(ClosureBinding { function, captures }));
                }
                let value = self.lower_expression(argument)?;
                if value.1 == ValueType::Callable {
                    bail!("Promise handler `{name}` là callable động; cần runtime completion ABI")
                }
                Ok(None)
            }
            _ => {
                let value = self.lower_expression(argument)?;
                if value.1 == ValueType::Callable {
                    bail!("Promise handler động cần runtime completion ABI")
                }
                Ok(None)
            }
        }
    }

    fn invoke_promise_handler(
        &mut self,
        label: &str,
        handler: &ClosureBinding,
        argument: Option<&(ValueId, ValueType, Option<Value>)>,
    ) -> Result<PromiseHandlerOutcome> {
        if !handler.function.r#async {
            if let Some(reason) = unconditional_function_throw(&handler.function) {
                let reason = self.lower_expression(reason)?;
                return Ok(PromiseHandlerOutcome::Throw(reason));
            }
            if function_contains_direct_throw(&handler.function) {
                bail!(
                    "conditional throw trong Promise handler `{label}` dùng completion-aware                      compatibility backend"
                )
            }
        }

        let temporary = argument.map(|argument| {
            let temporary = format!("@promise.handler.arg.{}", self.next_value);
            self.scopes.last_mut().unwrap().insert(
                temporary.clone(),
                Binding {
                    kind: VariableKind::Let,
                    initialized: true,
                    value_id: argument.0,
                    value_type: argument.1,
                    value: argument.2.clone(),
                    cell: None,
                },
            );
            temporary
        });
        let arguments = temporary
            .as_ref()
            .map(|temporary| {
                vec![Expression {
                    kind: ExpressionKind::Global(temporary.clone()),
                    span: Span::new(0, 0),
                }]
            })
            .unwrap_or_default();

        let value = if handler.function.r#async {
            self.lower_async_call(
                label,
                &handler.function,
                &arguments,
                Some(&handler.captures),
            )?
        } else {
            self.lower_inline_call(
                label,
                &handler.function,
                &arguments,
                Some(&handler.captures),
            )?
        };

        if let Some(temporary) = temporary {
            self.scopes.last_mut().unwrap().remove(&temporary);
        }
        Ok(PromiseHandlerOutcome::Return(value))
    }

    fn settlement_from_handler_value(
        &mut self,
        value: (ValueId, ValueType, Option<Value>),
    ) -> Result<PromiseSettlement> {
        if value.1 == ValueType::Promise {
            self.resolve_promise(value.0)
        } else {
            Ok(PromiseSettlement {
                state: PromiseState::Fulfilled,
                value,
            })
        }
    }

    fn apply_promise_chain(
        &mut self,
        chain: &PromiseChain,
        parent: PromiseSettlement,
    ) -> Result<PromiseSettlement> {
        if chain.kind == PromiseChainKind::Finally {
            let Some(handler) = &chain.on_fulfilled else {
                return Ok(parent);
            };
            let callback = self.invoke_promise_handler("promise.finally", handler, None)?;
            let callback = match callback {
                PromiseHandlerOutcome::Return(value) => {
                    self.settlement_from_handler_value(value)?
                }
                PromiseHandlerOutcome::Throw(reason) => PromiseSettlement {
                    state: PromiseState::Rejected,
                    value: reason,
                },
            };
            return if callback.state == PromiseState::Rejected {
                Ok(callback)
            } else {
                Ok(parent)
            };
        }

        let handler = match parent.state {
            PromiseState::Fulfilled => chain.on_fulfilled.as_ref(),
            PromiseState::Rejected => chain.on_rejected.as_ref(),
        };
        let Some(handler) = handler else {
            // ECMAScript's default identity/thrower handlers.
            return Ok(parent);
        };

        let callback = self.invoke_promise_handler(
            match parent.state {
                PromiseState::Fulfilled => "promise.then.fulfilled",
                PromiseState::Rejected => "promise.then.rejected",
            },
            handler,
            Some(&parent.value),
        )?;
        match callback {
            PromiseHandlerOutcome::Return(value) => self.settlement_from_handler_value(value),
            PromiseHandlerOutcome::Throw(reason) => Ok(PromiseSettlement {
                state: PromiseState::Rejected,
                value: reason,
            }),
        }
    }

    fn drain_promise_jobs(&mut self) -> Result<()> {
        /*
         * promise_order is registration order. Repeated passes allow a reaction
         * whose parent settles later to become runnable without reordering
         * independent reactions that were already runnable.
         */
        loop {
            let mut progress = false;
            let order = self.promise_order.clone();
            for token in order {
                if self.promise_settlements.contains_key(&token) {
                    continue;
                }
                let Some(chain) = self.promise_chains.get(&token).cloned() else {
                    // A genuinely pending, unused executor is legal.
                    continue;
                };
                if !self.promise_settlements.contains_key(&chain.parent) {
                    continue;
                }
                let parent = self
                    .promise_settlements
                    .get(&chain.parent)
                    .cloned()
                    .expect("checked parent settlement");
                let settlement = self.apply_promise_chain(&chain, parent)?;
                self.settle_existing_promise(token, settlement)?;
                progress = true;
            }
            if !progress {
                break;
            }
        }
        Ok(())
    }

    fn resolve_promise(&mut self, token: ValueId) -> Result<PromiseSettlement> {
        if let Some(value) = self.promise_settlements.get(&token).cloned() {
            return Ok(value);
        }
        if !self.promise_resolution_stack.insert(token) {
            bail!("cyclic native Promise resolution tại %v{}", token.0)
        }

        let result = (|| {
            let chain = self.promise_chains.get(&token).cloned().ok_or_else(|| {
                anyhow::anyhow!(
                    "Promise %v{} vẫn pending hoặc không có static resolution",
                    token.0
                )
            })?;
            let parent = self.resolve_promise(chain.parent)?;
            let settlement = self.apply_promise_chain(&chain, parent)?;
            self.settle_existing_promise(token, settlement)
        })();

        self.promise_resolution_stack.remove(&token);
        result
    }

    fn lower_promise_constructor(
        &mut self,
        executor: &HirFunction,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let resolve_name = executor.parameters.first().cloned();
        let reject_name = executor.parameters.get(1).cloned();

        self.scopes.push(HashMap::new());
        self.predeclare(&executor.body)?;
        let result = (|| {
            let mut first_settlement: Option<(PromiseState, (ValueId, ValueType, Option<Value>))> =
                None;

            for statement in &executor.body {
                if let StatementKind::Throw(reason) = &statement.kind {
                    let reason = self.lower_expression(reason)?;
                    if first_settlement.is_none() {
                        first_settlement = Some((PromiseState::Rejected, reason));
                    }
                    // The executor's abrupt completion stops later statements.
                    // If it was already resolved, the implicit reject call is
                    // ignored by the shared AlreadyResolved cell.
                    break;
                }

                let (expression, returns) = match &statement.kind {
                    StatementKind::Expression(expression) => (Some(expression), false),
                    StatementKind::Return(Some(expression)) => (Some(expression), true),
                    StatementKind::Return(None) => break,
                    StatementKind::FunctionDeclaration(_) => continue,
                    _ => {
                        self.lower_statement(statement)?;
                        if self.blocks[self.current].terminator.is_some() {
                            bail!(
                                "Promise executor control-flow completion cần general completion ABI"
                            )
                        }
                        continue;
                    }
                };

                let expression = expression.expect("expression statement");
                let direct_settlement = match &expression.kind {
                    ExpressionKind::Call { callee, arguments } => {
                        if let ExpressionKind::Global(settle) = &callee.kind {
                            let state = if resolve_name.as_deref() == Some(settle.as_str()) {
                                Some(PromiseState::Fulfilled)
                            } else if reject_name.as_deref() == Some(settle.as_str()) {
                                Some(PromiseState::Rejected)
                            } else {
                                None
                            };
                            state.map(|state| (state, arguments))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                if let Some((state, arguments)) = direct_settlement {
                    /*
                     * Call arguments are evaluated even after another resolving
                     * function already won. Only the settlement write is
                     * suppressed by AlreadyResolved.
                     */
                    let value = match arguments.first() {
                        Some(argument) => self.lower_expression(argument)?,
                        None => self.emit_value(Value::Undefined),
                    };
                    for extra in arguments.iter().skip(1) {
                        self.lower_expression(extra)?;
                    }
                    if first_settlement.is_none() {
                        first_settlement = Some((state, value));
                    }
                } else {
                    self.lower_expression(expression)?;
                }

                if returns {
                    break;
                }
            }

            match first_settlement {
                Some((state, value)) => self.create_settled_promise(state, value),
                None => Ok(self.create_pending_promise()),
            }
        })();
        self.scopes.pop();
        result
    }

    fn lookup(&mut self, name: &str) -> Result<(ValueId, ValueType, Option<Value>)> {
        for scope in self.scopes.iter().rev() {
            if let Some(binding) = scope.get(name) {
                if !binding.initialized {
                    bail!("identifier `{name}` đang ở Temporal Dead Zone")
                }
                let binding = binding.clone();
                if let Some(cell) = binding.cell {
                    let result = self.new_value();
                    self.emit(Instruction::CellGet {
                        result,
                        cell,
                        value_type: binding.value_type,
                    });
                    return Ok((result, binding.value_type, None));
                }
                return Ok((binding.value_id, binding.value_type, binding.value));
            }
        }
        match name {
            "undefined" => Ok(self.emit_value(Value::Undefined)),
            "NaN" => Ok(self.emit_value(Value::Number(f64::NAN))),
            "Infinity" => Ok(self.emit_value(Value::Number(f64::INFINITY))),
            _ => bail!("identifier `{name}` chưa được khai báo"),
        }
    }

    fn find_binding_mut(&mut self, name: &str) -> Option<&mut Binding> {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(name) {
                return scope.get_mut(name);
            }
        }
        None
    }

    fn has_binding(&self, name: &str) -> bool {
        self.scopes
            .iter()
            .rev()
            .any(|scope| scope.contains_key(name))
    }
    fn emit_value(&mut self, value: Value) -> (ValueId, ValueType, Option<Value>) {
        let id = self.const_value(value.clone());
        (id, type_of(&value), Some(value))
    }
    fn const_value(&mut self, value: Value) -> ValueId {
        let result = self.new_value();
        self.emit(match value {
            Value::Undefined => Instruction::ConstUndefined { result },
            Value::Null => Instruction::ConstNull { result },
            Value::Number(value) => Instruction::ConstNumber { result, value },
            Value::Bool(value) => Instruction::ConstBool { result, value },
            Value::String(value) => Instruction::ConstString { result, value },
            Value::Object(_) => panic!("object constant chưa có native representation"),
            Value::Array(_) => panic!("array constant chưa có native representation"),
            Value::Function(_) | Value::Promise(_) => {
                panic!("runtime handle không thể là native constant")
            }
        });
        result
    }
}

#[cfg(test)]
mod throw_lowering_tests {
    use super::*;

    fn span() -> Span {
        Span::new(0, 0)
    }

    fn program(statements: Vec<Statement>) -> HirProgram {
        HirProgram {
            statements,
            strict: false,
            imports: Vec::new(),
            exports: Vec::new(),
            export_all: Vec::new(),
            promise_subclasses: Vec::new(),
        }
    }

    #[test]
    fn top_level_throw_is_an_abrupt_terminator() {
        let hir = program(vec![
            Statement {
                kind: StatementKind::Throw(Expression {
                    kind: ExpressionKind::String("boom".to_owned()),
                    span: span(),
                }),
                span: span(),
            },
            Statement {
                kind: StatementKind::Expression(Expression {
                    kind: ExpressionKind::Number(99.0),
                    span: span(),
                }),
                span: span(),
            },
        ]);
        let ir = analyze(&hir).unwrap();
        assert!(matches!(
            &ir.functions[0].blocks[0].terminator,
            Terminator::ThrowValue {
                value_type: ValueType::String,
                ..
            }
        ));
    }
}
