use anyhow::{Result, bail};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Write,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueType {
    Undefined,
    Null,
    Number,
    Bool,
    String,
    Object,
    Callable,
    Cell,
    Promise,
    Dynamic,
}

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Function>,
}
#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub captures: Vec<Parameter>,
    /// `None` is reserved for the native process entry point (`main`).
    /// JavaScript functions always return an ECMAScript value, including
    /// `undefined` for a bare return/fallthrough.
    pub return_type: Option<ValueType>,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub value: ValueId,
    pub value_type: ValueType,
}
#[derive(Debug)]
pub struct BasicBlock {
    pub name: String,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

#[derive(Debug)]
pub enum Instruction {
    Parameter {
        result: ValueId,
        index: u32,
        value_type: ValueType,
    },
    Capture {
        result: ValueId,
        index: u32,
        value_type: ValueType,
    },
    CellNew {
        result: ValueId,
        value: ValueId,
        value_type: ValueType,
    },
    CellGet {
        result: ValueId,
        cell: ValueId,
        value_type: ValueType,
    },
    CellSet {
        cell: ValueId,
        value: ValueId,
        value_type: ValueType,
    },
    PromiseResolved {
        result: ValueId,
        value: ValueId,
        value_type: ValueType,
    },
    PromisePending {
        result: ValueId,
    },
    PromiseThen {
        result: ValueId,
        promise: ValueId,
        callback: ValueId,
    },
    MicrotaskDrain,
    ConstUndefined {
        result: ValueId,
    },
    ConstNull {
        result: ValueId,
    },
    ConstNumber {
        result: ValueId,
        value: f64,
    },
    ConstBool {
        result: ValueId,
        value: bool,
    },
    ConstString {
        result: ValueId,
        value: String,
    },
    ObjectNew {
        result: ValueId,
    },
    ObjectNewWithPrototype {
        result: ValueId,
        prototype: ValueId,
    },
    ObjectGet {
        result: ValueId,
        object: ValueId,
        key: String,
        value_type: ValueType,
    },
    ObjectSet {
        object: ValueId,
        key: String,
        value: ValueId,
        value_type: ValueType,
    },
    ObjectDelete {
        result: ValueId,
        object: ValueId,
        key: String,
    },
    ObjectSetPrototype {
        object: ValueId,
        prototype: ValueId,
    },
    ObjectDefineAccessor {
        object: ValueId,
        key: String,
        getter: Option<ValueId>,
        setter: Option<ValueId>,
        enumerable: bool,
        configurable: bool,
    },
    ObjectGetPrototype {
        result: ValueId,
        object: ValueId,
    },
    ToBoolean {
        result: ValueId,
        operand: ValueId,
        operand_type: ValueType,
    },
    UnaryNumber {
        result: ValueId,
        operator: UnaryNumberOperator,
        operand: ValueId,
    },
    UnaryBool {
        result: ValueId,
        operator: UnaryBoolOperator,
        operand: ValueId,
    },
    BinaryNumber {
        result: ValueId,
        operator: BinaryNumberOperator,
        left: ValueId,
        right: ValueId,
    },
    CompareNumber {
        result: ValueId,
        operator: CompareNumberOperator,
        left: ValueId,
        right: ValueId,
    },
    CompareString {
        result: ValueId,
        left: ValueId,
        right: ValueId,
    },
    CompareObject {
        result: ValueId,
        operator: CompareNumberOperator,
        left: ValueId,
        right: ValueId,
    },
    Phi {
        result: ValueId,
        value_type: ValueType,
        incoming: Vec<(BlockId, ValueId)>,
    },
    ClosureNew {
        result: ValueId,
        function: String,
        captures: Vec<ValueId>,
        capture_types: Vec<ValueType>,
    },
    CallDirect {
        result: ValueId,
        function: String,
        arguments: Vec<ValueId>,
        argument_types: Vec<ValueType>,
        return_type: ValueType,
    },
    CallIndirect {
        result: ValueId,
        callee: ValueId,
        arguments: Vec<ValueId>,
        argument_types: Vec<ValueType>,
        return_type: ValueType,
    },
    CallBuiltin {
        builtin: Builtin,
        arguments: Vec<ValueId>,
        display_values: Vec<Option<String>>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryNumberOperator {
    Plus,
    Minus,
    BitwiseNot,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryBoolOperator {
    Not,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryNumberOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    ShiftRight,
    ShiftRightZeroFill,
    BitwiseOr,
    BitwiseXor,
    BitwiseAnd,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareNumberOperator {
    Equal,
    NotEqual,
    StrictEqual,
    StrictNotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    ConsoleLog,
}
#[derive(Debug)]
pub enum Terminator {
    Jump(BlockId),
    Branch {
        condition: ValueId,
        then_block: BlockId,
        else_block: BlockId,
    },
    ReturnI32(i32),
    ReturnValue {
        value: ValueId,
        value_type: ValueType,
    },
    TailCallDirect {
        function: String,
        arguments: Vec<ValueId>,
        argument_types: Vec<ValueType>,
    },
    Unreachable,
}

pub fn value_types(program: &Program) -> Result<HashMap<ValueId, ValueType>> {
    let mut types = HashMap::new();
    // Definition pass first. A loop-header phi references its back-edge value,
    // which is intentionally defined in a later block.
    for function in &program.functions {
        for block in &function.blocks {
            for instruction in &block.instructions {
                if let Some((result, value_type)) = declared_result(instruction) {
                    if types.insert(result, value_type).is_some() {
                        bail!("SSA value %v{} được định nghĩa nhiều lần", result.0);
                    }
                }
            }
        }
    }
    // Use/type validation pass.
    for function in &program.functions {
        for block in &function.blocks {
            for instruction in &block.instructions {
                match instruction {
                    Instruction::Parameter {
                        result,
                        index,
                        value_type,
                    } => {
                        let parameter =
                            function.parameters.get(*index as usize).ok_or_else(|| {
                                anyhow::anyhow!("parameter index {} ngoài signature", index)
                            })?;
                        if parameter.value != *result || parameter.value_type != *value_type {
                            bail!("parameter instruction không khớp function signature")
                        }
                    }
                    Instruction::Capture {
                        result,
                        index,
                        value_type,
                    } => {
                        let capture = function.captures.get(*index as usize).ok_or_else(|| {
                            anyhow::anyhow!("capture index {} ngoài closure signature", index)
                        })?;
                        if capture.value != *result || capture.value_type != *value_type {
                            bail!("capture instruction không khớp closure signature")
                        }
                    }
                    Instruction::CellNew {
                        value, value_type, ..
                    } => require_type(&types, *value, *value_type)?,
                    Instruction::CellGet { cell, .. } => {
                        require_type(&types, *cell, ValueType::Cell)?
                    }
                    Instruction::CellSet {
                        cell,
                        value,
                        value_type,
                    } => {
                        require_type(&types, *cell, ValueType::Cell)?;
                        require_type(&types, *value, *value_type)?;
                    }
                    Instruction::PromiseResolved {
                        value, value_type, ..
                    } => require_type(&types, *value, *value_type)?,
                    Instruction::PromiseThen {
                        promise, callback, ..
                    } => {
                        require_type(&types, *promise, ValueType::Promise)?;
                        require_type(&types, *callback, ValueType::Callable)?;
                    }
                    Instruction::ObjectGet { object, .. } => {
                        require_type(&types, *object, ValueType::Object)?
                    }
                    Instruction::ObjectNewWithPrototype { prototype, .. } => {
                        if !matches!(
                            types.get(prototype),
                            Some(ValueType::Object | ValueType::Null)
                        ) {
                            bail!("prototype phải là Object hoặc Null")
                        }
                    }
                    Instruction::ObjectSetPrototype { object, prototype } => {
                        require_type(&types, *object, ValueType::Object)?;
                        if !matches!(
                            types.get(prototype),
                            Some(ValueType::Object | ValueType::Null)
                        ) {
                            bail!("prototype phải là Object hoặc Null")
                        }
                    }
                    Instruction::ObjectDefineAccessor {
                        object,
                        getter,
                        setter,
                        ..
                    } => {
                        require_type(&types, *object, ValueType::Object)?;
                        if let Some(getter) = getter {
                            require_type(&types, *getter, ValueType::Callable)?;
                        }
                        if let Some(setter) = setter {
                            require_type(&types, *setter, ValueType::Callable)?;
                        }
                    }
                    Instruction::ObjectGetPrototype { result, object } => {
                        require_type(&types, *object, ValueType::Object)?;
                        let _ = result;
                    }
                    Instruction::ObjectSet {
                        object,
                        value,
                        value_type,
                        ..
                    } => {
                        require_type(&types, *object, ValueType::Object)?;
                        require_type(&types, *value, *value_type)?;
                    }
                    Instruction::ObjectDelete { object, .. } => {
                        require_type(&types, *object, ValueType::Object)?
                    }
                    Instruction::ToBoolean { operand, .. } => {
                        if !types.contains_key(operand) {
                            bail!("unknown SSA value %v{}", operand.0)
                        }
                    }
                    Instruction::UnaryNumber { operand, .. } => {
                        require_type(&types, *operand, ValueType::Number)?
                    }
                    Instruction::UnaryBool { operand, .. } => {
                        require_type(&types, *operand, ValueType::Bool)?
                    }
                    Instruction::BinaryNumber { left, right, .. }
                    | Instruction::CompareNumber { left, right, .. } => {
                        require_type(&types, *left, ValueType::Number)?;
                        require_type(&types, *right, ValueType::Number)?;
                    }
                    Instruction::CompareString { left, right, .. } => {
                        require_type(&types, *left, ValueType::String)?;
                        require_type(&types, *right, ValueType::String)?;
                    }
                    Instruction::CompareObject { left, right, .. } => {
                        require_type(&types, *left, ValueType::Object)?;
                        require_type(&types, *right, ValueType::Object)?;
                    }
                    Instruction::Phi {
                        result,
                        value_type,
                        incoming,
                    } => {
                        if incoming.is_empty() {
                            bail!("phi %v{} không có incoming", result.0)
                        }
                        for (_, value) in incoming {
                            let actual = types.get(value).copied().ok_or_else(|| {
                                anyhow::anyhow!("unknown SSA value %v{}", value.0)
                            })?;
                            if *value_type != ValueType::Dynamic && actual != *value_type {
                                bail!(
                                    "phi %v{} nhận kiểu {:?}, cần {:?}",
                                    result.0,
                                    actual,
                                    value_type
                                )
                            }
                        }
                    }
                    Instruction::ClosureNew {
                        captures,
                        capture_types,
                        ..
                    } => {
                        if captures.len() != capture_types.len() {
                            bail!("closure capture metadata không khớp")
                        }
                        for (capture, value_type) in captures.iter().zip(capture_types) {
                            require_type(&types, *capture, *value_type)?;
                        }
                    }
                    Instruction::CallDirect {
                        function: callee,
                        arguments,
                        argument_types,
                        return_type,
                        ..
                    } => {
                        verify_call_arguments(&types, arguments, argument_types)?;
                        let target = program
                            .functions
                            .iter()
                            .find(|candidate| candidate.name == *callee)
                            .ok_or_else(|| anyhow::anyhow!("unknown direct callee `{callee}`"))?;
                        if target.parameters.len() != arguments.len() {
                            bail!("direct call `{callee}` sai arity")
                        }
                        if target.return_type != Some(*return_type) {
                            bail!("direct call `{callee}` sai return type")
                        }
                    }
                    Instruction::CallIndirect {
                        callee,
                        arguments,
                        argument_types,
                        ..
                    } => {
                        require_type(&types, *callee, ValueType::Callable)?;
                        verify_call_arguments(&types, arguments, argument_types)?;
                    }
                    Instruction::CallBuiltin {
                        arguments,
                        display_values,
                        ..
                    } => {
                        if arguments.len() != display_values.len() {
                            bail!("console.log metadata không khớp số argument")
                        }
                        for argument in arguments {
                            if !types.contains_key(argument) {
                                bail!("unknown SSA value %v{}", argument.0)
                            }
                        }
                    }
                    _ => {}
                }
            }
            match &block.terminator {
                Terminator::Jump(target) => require_block(function, *target)?,
                Terminator::Branch {
                    condition,
                    then_block,
                    else_block,
                } => {
                    require_type(&types, *condition, ValueType::Bool)?;
                    require_block(function, *then_block)?;
                    require_block(function, *else_block)?;
                }
                Terminator::ReturnI32(_) => {}
                Terminator::ReturnValue { value, value_type } => {
                    require_type(&types, *value, *value_type)?;
                    if function.return_type != Some(*value_type)
                        && function.return_type != Some(ValueType::Dynamic)
                    {
                        bail!("return type không khớp function `{}`", function.name)
                    }
                }
                Terminator::TailCallDirect {
                    function: callee,
                    arguments,
                    argument_types,
                } => {
                    verify_call_arguments(&types, arguments, argument_types)?;
                    let target = program
                        .functions
                        .iter()
                        .find(|candidate| candidate.name == *callee)
                        .ok_or_else(|| anyhow::anyhow!("unknown direct tail callee `{callee}`"))?;
                    if target.parameters.len() != arguments.len() {
                        bail!("direct tail call `{callee}` sai target arity")
                    }
                    if function.parameters.len() != arguments.len() {
                        bail!("direct tail call `{callee}` không thể tái sử dụng argv")
                    }
                    if function.return_type != Some(ValueType::Dynamic)
                        && function.return_type != target.return_type
                    {
                        bail!("direct tail call `{callee}` sai return type")
                    }
                }
                Terminator::Unreachable => {}
            }
        }
    }
    Ok(types)
}

fn declared_result(instruction: &Instruction) -> Option<(ValueId, ValueType)> {
    Some(match instruction {
        Instruction::Parameter {
            result, value_type, ..
        }
        | Instruction::Capture {
            result, value_type, ..
        } => (*result, *value_type),
        Instruction::CellNew { result, .. } => (*result, ValueType::Cell),
        Instruction::CellGet {
            result, value_type, ..
        } => (*result, *value_type),
        Instruction::ConstUndefined { result } => (*result, ValueType::Undefined),
        Instruction::ConstNull { result } => (*result, ValueType::Null),
        Instruction::ConstNumber { result, .. } => (*result, ValueType::Number),
        Instruction::ConstBool { result, .. } => (*result, ValueType::Bool),
        Instruction::ConstString { result, .. } => (*result, ValueType::String),
        Instruction::ObjectNew { result } => (*result, ValueType::Object),
        Instruction::ObjectNewWithPrototype { result, .. } => (*result, ValueType::Object),
        Instruction::ObjectGet {
            result, value_type, ..
        } => (*result, *value_type),
        Instruction::ObjectDelete { result, .. } => (*result, ValueType::Bool),
        Instruction::ObjectGetPrototype { result, .. } => (*result, ValueType::Object),
        Instruction::ObjectSetPrototype { .. } => return None,
        Instruction::ObjectDefineAccessor { .. } => return None,
        Instruction::ToBoolean { result, .. } => (*result, ValueType::Bool),
        Instruction::UnaryNumber { result, .. } => (*result, ValueType::Number),
        Instruction::UnaryBool { result, .. } => (*result, ValueType::Bool),
        Instruction::BinaryNumber { result, .. } => (*result, ValueType::Number),
        Instruction::CompareNumber { result, .. } => (*result, ValueType::Bool),
        Instruction::CompareString { result, .. } => (*result, ValueType::Bool),
        Instruction::CompareObject { result, .. } => (*result, ValueType::Bool),
        Instruction::Phi {
            result, value_type, ..
        } => (*result, *value_type),
        Instruction::ClosureNew { result, .. } => (*result, ValueType::Callable),
        Instruction::CallDirect {
            result,
            return_type,
            ..
        }
        | Instruction::CallIndirect {
            result,
            return_type,
            ..
        } => (*result, *return_type),
        Instruction::CallBuiltin { .. } => return None,
        Instruction::ObjectSet { .. } => return None,
        Instruction::CellSet { .. } => return None,
        Instruction::PromiseResolved { result, .. } => (*result, ValueType::Promise),
        Instruction::PromisePending { result } => (*result, ValueType::Promise),
        Instruction::PromiseThen { result, .. } => (*result, ValueType::Promise),
        Instruction::MicrotaskDrain => return None,
    })
}

fn verify_call_arguments(
    types: &HashMap<ValueId, ValueType>,
    arguments: &[ValueId],
    argument_types: &[ValueType],
) -> Result<()> {
    if arguments.len() != argument_types.len() {
        bail!("call argument metadata không khớp")
    }
    for (argument, value_type) in arguments.iter().zip(argument_types) {
        require_type(types, *argument, *value_type)?;
    }
    Ok(())
}

fn require_type(
    types: &HashMap<ValueId, ValueType>,
    value: ValueId,
    expected: ValueType,
) -> Result<()> {
    match types.get(&value) {
        Some(actual) if *actual == expected => Ok(()),
        Some(actual) => bail!(
            "SSA value %v{} có kiểu {:?}, cần {:?}",
            value.0,
            actual,
            expected
        ),
        None => bail!("unknown SSA value %v{}", value.0),
    }
}

fn require_block(function: &Function, block: BlockId) -> Result<()> {
    if usize::try_from(block.0)
        .ok()
        .is_some_and(|index| index < function.blocks.len())
    {
        Ok(())
    } else {
        bail!("block %b{} không tồn tại", block.0)
    }
}

pub fn verify_program(program: &Program) -> Result<()> {
    let _ = value_types(program)?;
    for function in &program.functions {
        verify_cfg(function)?;
    }
    Ok(())
}

fn verify_cfg(function: &Function) -> Result<()> {
    if function.blocks.is_empty() {
        bail!("function `{}` không có entry block", function.name)
    }
    let mut predecessors = vec![HashSet::<BlockId>::new(); function.blocks.len()];
    let mut successors = vec![Vec::<BlockId>::new(); function.blocks.len()];
    for (index, block) in function.blocks.iter().enumerate() {
        let targets = match &block.terminator {
            Terminator::Jump(target) => vec![*target],
            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => vec![*then_block, *else_block],
            Terminator::ReturnI32(_)
            | Terminator::ReturnValue { .. }
            | Terminator::TailCallDirect { .. }
            | Terminator::Unreachable => Vec::new(),
        };
        for target in targets {
            require_block(function, target)?;
            successors[index].push(target);
            predecessors[target.0 as usize].insert(BlockId(index as u32));
        }
    }

    let mut reachable = HashSet::from([BlockId(0)]);
    let mut work = VecDeque::from([BlockId(0)]);
    while let Some(block) = work.pop_front() {
        for successor in &successors[block.0 as usize] {
            if reachable.insert(*successor) {
                work.push_back(*successor);
            }
        }
    }

    for (index, block) in function.blocks.iter().enumerate() {
        let block_id = BlockId(index as u32);
        let expected = predecessors[index]
            .iter()
            .filter(|predecessor| reachable.contains(predecessor))
            .copied()
            .collect::<HashSet<_>>();
        let mut saw_non_phi = false;
        for instruction in &block.instructions {
            if let Instruction::Phi { incoming, .. } = instruction {
                if saw_non_phi {
                    bail!(
                        "phi trong block `{}` của `{}` phải đứng trước instruction thường",
                        block.name,
                        function.name
                    )
                }
                let actual = incoming
                    .iter()
                    .map(|(predecessor, _)| *predecessor)
                    .collect::<HashSet<_>>();
                if actual.len() != incoming.len() {
                    bail!("phi trong block `{}` có predecessor trùng", block.name)
                }
                if reachable.contains(&block_id) && actual != expected {
                    bail!(
                        "phi trong block `{}` có incoming {:?}, CFG cần {:?}",
                        block.name,
                        actual,
                        expected
                    )
                }
            } else {
                saw_non_phi = true;
            }
        }
    }
    Ok(())
}

pub fn dump_program(program: &Program) -> String {
    let mut output = String::new();
    for function in &program.functions {
        let parameters = function
            .parameters
            .iter()
            .map(|parameter| format!("%v{}: {:?}", parameter.value.0, parameter.value_type))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            &mut output,
            "fn {}({parameters}) -> {:?} {{",
            function.name, function.return_type
        )
        .unwrap();
        for block in &function.blocks {
            writeln!(&mut output, "{}:", block.name).unwrap();
            for instruction in &block.instructions {
                match instruction {
                    Instruction::Parameter {
                        result,
                        index,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = parameter {} {:?}",
                        result.0, index, value_type
                    )
                    .unwrap(),
                    Instruction::Capture {
                        result,
                        index,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = capture {} {:?}",
                        result.0, index, value_type
                    )
                    .unwrap(),
                    Instruction::CellNew {
                        result,
                        value,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = cell_new {:?} %v{}",
                        result.0, value_type, value.0
                    )
                    .unwrap(),
                    Instruction::CellGet {
                        result,
                        cell,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = cell_get {:?} %v{}",
                        result.0, value_type, cell.0
                    )
                    .unwrap(),
                    Instruction::CellSet {
                        cell,
                        value,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    cell_set {:?} %v{}, %v{}",
                        value_type, cell.0, value.0
                    )
                    .unwrap(),
                    Instruction::PromiseResolved {
                        result,
                        value,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = promise_resolved {:?} %v{}",
                        result.0, value_type, value.0
                    )
                    .unwrap(),
                    Instruction::PromisePending { result } => writeln!(
                        &mut output,
                        "    %v{} = promise_pending",
                        result.0
                    )
                    .unwrap(),
                    Instruction::PromiseThen {
                        result,
                        promise,
                        callback,
                    } => writeln!(
                        &mut output,
                        "    %v{} = promise_then %v{}, %v{}",
                        result.0, promise.0, callback.0
                    )
                    .unwrap(),
                    Instruction::MicrotaskDrain => {
                        writeln!(&mut output, "    microtask_drain").unwrap()
                    }
                    Instruction::ConstUndefined { result } => {
                        writeln!(&mut output, "    %v{} = const_undefined", result.0).unwrap()
                    }
                    Instruction::ConstNull { result } => {
                        writeln!(&mut output, "    %v{} = const_null", result.0).unwrap()
                    }
                    Instruction::ConstNumber { result, value } => {
                        writeln!(&mut output, "    %v{} = const_number {value}", result.0).unwrap()
                    }
                    Instruction::ConstBool { result, value } => {
                        writeln!(&mut output, "    %v{} = const_bool {value}", result.0).unwrap()
                    }
                    Instruction::ConstString { result, value } => {
                        writeln!(&mut output, "    %v{} = const_string {:?}", result.0, value)
                            .unwrap()
                    }
                    Instruction::ObjectNew { result } => {
                        writeln!(&mut output, "    %v{} = object_new", result.0).unwrap()
                    }
                    Instruction::ObjectNewWithPrototype { result, prototype } => writeln!(
                        &mut output,
                        "    %v{} = object_new_with_prototype %v{}",
                        result.0, prototype.0
                    )
                    .unwrap(),
                    Instruction::ObjectGet {
                        result,
                        object,
                        key,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = object_get {:?} %v{}, {:?}",
                        result.0, value_type, object.0, key
                    )
                    .unwrap(),
                    Instruction::ObjectSet {
                        object,
                        key,
                        value,
                        value_type,
                    } => writeln!(
                        &mut output,
                        "    object_set {:?} %v{}, {:?}, %v{}",
                        value_type, object.0, key, value.0
                    )
                    .unwrap(),
                    Instruction::ToBoolean {
                        result,
                        operand,
                        operand_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = to_boolean {:?} %v{}",
                        result.0, operand_type, operand.0
                    )
                    .unwrap(),
                    Instruction::UnaryNumber {
                        result,
                        operator,
                        operand,
                    } => writeln!(
                        &mut output,
                        "    %v{} = {:?} %v{}",
                        result.0, operator, operand.0
                    )
                    .unwrap(),
                    Instruction::UnaryBool {
                        result,
                        operator,
                        operand,
                    } => writeln!(
                        &mut output,
                        "    %v{} = {:?} %v{}",
                        result.0, operator, operand.0
                    )
                    .unwrap(),
                    Instruction::BinaryNumber {
                        result,
                        operator,
                        left,
                        right,
                    } => writeln!(
                        &mut output,
                        "    %v{} = {:?} %v{}, %v{}",
                        result.0, operator, left.0, right.0
                    )
                    .unwrap(),
                    Instruction::CompareNumber {
                        result,
                        operator,
                        left,
                        right,
                    } => writeln!(
                        &mut output,
                        "    %v{} = {:?} %v{}, %v{}",
                        result.0, operator, left.0, right.0
                    )
                    .unwrap(),
                    Instruction::CompareString {
                        result,
                        left,
                        right,
                    } => writeln!(
                        &mut output,
                        "    %v{} = string_equal %v{}, %v{}",
                        result.0, left.0, right.0
                    )
                    .unwrap(),
                    Instruction::CompareObject {
                        result,
                        operator,
                        left,
                        right,
                    } => writeln!(
                        &mut output,
                        "    %v{} = object_compare {:?} %v{}, %v{}",
                        result.0, operator, left.0, right.0
                    )
                    .unwrap(),
                    Instruction::CallBuiltin {
                        builtin: Builtin::ConsoleLog,
                        arguments,
                        display_values,
                    } => {
                        let args = arguments
                            .iter()
                            .map(|v| format!("%v{}", v.0))
                            .collect::<Vec<_>>()
                            .join(", ");
                        writeln!(
                            &mut output,
                            "    call @builtin.console_log({args}) ; {display_values:?}"
                        )
                        .unwrap();
                    }
                    Instruction::ObjectDelete {
                        result,
                        object,
                        key,
                    } => writeln!(
                        &mut output,
                        "    %v{} = object_delete %v{}, {:?}",
                        result.0, object.0, key
                    )
                    .unwrap(),
                    Instruction::ObjectSetPrototype { object, prototype } => writeln!(
                        &mut output,
                        "    object_set_prototype %v{}, %v{}",
                        object.0, prototype.0
                    )
                    .unwrap(),
                    Instruction::ObjectDefineAccessor {
                        object,
                        key,
                        getter,
                        setter,
                        enumerable,
                        configurable,
                    } => writeln!(
                        &mut output,
                        "    object_define_accessor %v{}, {:?}, {:?}, {:?}, enumerable={}, configurable={}",
                        object.0, key, getter, setter, enumerable, configurable
                    )
                    .unwrap(),
                    Instruction::ObjectGetPrototype { result, object } => writeln!(
                        &mut output,
                        "    %v{} = object_get_prototype %v{}",
                        result.0, object.0
                    )
                    .unwrap(),
                    Instruction::Phi {
                        result,
                        value_type,
                        incoming,
                    } => {
                        let args = incoming
                            .iter()
                            .map(|(block, value)| format!("[%b{}, %v{}]", block.0, value.0))
                            .collect::<Vec<_>>()
                            .join(", ");
                        writeln!(
                            &mut output,
                            "    %v{} = phi {:?} {args}",
                            result.0, value_type
                        )
                        .unwrap();
                    }
                    Instruction::ClosureNew {
                        result,
                        function,
                        captures,
                        ..
                    } => {
                        let captures = captures
                            .iter()
                            .map(|value| format!("%v{}", value.0))
                            .collect::<Vec<_>>()
                            .join(", ");
                        writeln!(
                            &mut output,
                            "    %v{} = closure_new @{} [{}]",
                            result.0, function, captures
                        )
                        .unwrap();
                    }
                    Instruction::CallDirect {
                        result,
                        function,
                        arguments,
                        return_type,
                        ..
                    } => {
                        let arguments = arguments
                            .iter()
                            .map(|value| format!("%v{}", value.0))
                            .collect::<Vec<_>>()
                            .join(", ");
                        writeln!(
                            &mut output,
                            "    %v{} = call {:?} @{}({})",
                            result.0, return_type, function, arguments
                        )
                        .unwrap();
                    }
                    Instruction::CallIndirect {
                        result,
                        callee,
                        arguments,
                        return_type,
                        ..
                    } => {
                        let arguments = arguments
                            .iter()
                            .map(|value| format!("%v{}", value.0))
                            .collect::<Vec<_>>()
                            .join(", ");
                        writeln!(
                            &mut output,
                            "    %v{} = call_indirect {:?} %v{}({})",
                            result.0, return_type, callee.0, arguments
                        )
                        .unwrap();
                    }
                }
            }
            match &block.terminator {
                Terminator::Jump(target) => {
                    writeln!(&mut output, "    jump %b{}", target.0).unwrap()
                }
                Terminator::Branch {
                    condition,
                    then_block,
                    else_block,
                } => writeln!(
                    &mut output,
                    "    branch %v{} -> %b{}, %b{}",
                    condition.0, then_block.0, else_block.0
                )
                .unwrap(),
                Terminator::ReturnI32(value) => {
                    writeln!(&mut output, "    ret i32 {value}").unwrap()
                }
                Terminator::ReturnValue { value, value_type } => {
                    writeln!(&mut output, "    ret {:?} %v{}", value_type, value.0).unwrap()
                }
                Terminator::TailCallDirect {
                    function,
                    arguments,
                    ..
                } => {
                    let arguments = arguments
                        .iter()
                        .map(|value| format!("%v{}", value.0))
                        .collect::<Vec<_>>()
                        .join(", ");
                    writeln!(&mut output, "    tail_call @{}({})", function, arguments).unwrap()
                }
                Terminator::Unreachable => writeln!(&mut output, "    unreachable").unwrap(),
            }
        }
        writeln!(&mut output, "}}\n").unwrap();
    }
    output
}
