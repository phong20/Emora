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

#[derive(Debug, Clone)]
pub struct CallArgument {
    pub value: ValueId,
    pub value_type: ValueType,
    pub spread: bool,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DynamicUnaryOperator {
    Plus = 0,
    Minus = 1,
    Not = 2,
    BitwiseNot = 3,
    TypeOf = 4,
    Void = 5,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DynamicBinaryOperator {
    Add = 0,
    Subtract = 1,
    Multiply = 2,
    Divide = 3,
    Remainder = 4,
    Exponential = 5,
    Equal = 6,
    NotEqual = 7,
    StrictEqual = 8,
    StrictNotEqual = 9,
    LessThan = 10,
    LessEqual = 11,
    GreaterThan = 12,
    GreaterEqual = 13,
    ShiftLeft = 14,
    ShiftRight = 15,
    ShiftRightZeroFill = 16,
    BitwiseOr = 17,
    BitwiseXor = 18,
    BitwiseAnd = 19,
    In = 20,
    InstanceOf = 21,
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
    /// Create a promise fulfilled through the built-in Promise resolution
    /// procedure. A Promise-typed value is adopted, not boxed as fulfillment.
    PromiseResolved {
        result: ValueId,
        value: ValueId,
        value_type: ValueType,
    },
    PromiseRejected {
        result: ValueId,
        reason: ValueId,
        reason_type: ValueType,
    },
    PromisePending {
        result: ValueId,
    },
    /// Settle an existing capability promise. Fulfillment uses the Promise
    /// resolution procedure and therefore adopts a Promise-typed value.
    PromiseSettle {
        promise: ValueId,
        value: ValueId,
        value_type: ValueType,
        rejected: bool,
    },
    PromiseThen {
        result: ValueId,
        promise: ValueId,
        on_fulfilled: Option<ValueId>,
        on_rejected: Option<ValueId>,
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
    /// ECMAScript ToNumber after analysis proves the dynamic value cannot be
    /// Object, Proxy, Callable, Promise, Cell or BigInt.
    ToNumber {
        result: ValueId,
        operand: ValueId,
        operand_type: ValueType,
    },
    /// ECMAScript `typeof` for a value whose concrete tag is only known at
    /// runtime. Statically typed operands are folded in analysis instead.
    TypeOfDynamic {
        result: ValueId,
        operand: ValueId,
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

    CurrentThis {
        result: ValueId,
    },
    CurrentCallable {
        result: ValueId,
    },
    ArgumentsObject {
        result: ValueId,
    },
    RestArray {
        result: ValueId,
        start: u32,
    },
    ArrayPush {
        array: ValueId,
        value: ValueId,
        value_type: ValueType,
    },
    ArraySpread {
        array: ValueId,
        iterable: ValueId,
        iterable_type: ValueType,
    },
    DynamicUnary {
        result: ValueId,
        operator: DynamicUnaryOperator,
        operand: ValueId,
        operand_type: ValueType,
    },
    DynamicBinary {
        result: ValueId,
        operator: DynamicBinaryOperator,
        left: ValueId,
        left_type: ValueType,
        right: ValueId,
        right_type: ValueType,
    },
    DynamicGet {
        result: ValueId,
        object: ValueId,
        object_type: ValueType,
        key: String,
    },
    DynamicSet {
        object: ValueId,
        object_type: ValueType,
        key: String,
        value: ValueId,
        value_type: ValueType,
    },
    DynamicDelete {
        result: ValueId,
        object: ValueId,
        object_type: ValueType,
        key: String,
    },
    ClosureNewGeneric {
        result: ValueId,
        function: String,
        captures: Vec<ValueId>,
        capture_types: Vec<ValueType>,
        constructable: bool,
        strict: bool,
        lexical_this: Option<ValueId>,
        lexical_this_type: Option<ValueType>,
    },
    CallValue {
        result: ValueId,
        callee: ValueId,
        callee_type: ValueType,
        receiver: Option<ValueId>,
        receiver_type: Option<ValueType>,
        arguments: Vec<CallArgument>,
    },
    ConstructValue {
        result: ValueId,
        callee: ValueId,
        callee_type: ValueType,
        arguments: Vec<CallArgument>,
    },
    BindValue {
        result: ValueId,
        target: ValueId,
        target_type: ValueType,
        this_arg: ValueId,
        this_type: ValueType,
        arguments: Vec<CallArgument>,
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
    Exponential,
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
    /// ECMAScript abrupt completion. This is deliberately distinct from a
    /// normal return: it never writes the function's normal result slot.
    ThrowValue {
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
                    Instruction::PromiseRejected {
                        reason,
                        reason_type,
                        ..
                    } => require_type(&types, *reason, *reason_type)?,
                    Instruction::PromiseSettle {
                        promise,
                        value,
                        value_type,
                        ..
                    } => {
                        require_type(&types, *promise, ValueType::Promise)?;
                        require_type(&types, *value, *value_type)?;
                    }
                    Instruction::PromiseThen {
                        promise,
                        on_fulfilled,
                        on_rejected,
                        ..
                    } => {
                        require_type(&types, *promise, ValueType::Promise)?;
                        if let Some(on_fulfilled) = on_fulfilled {
                            require_type(&types, *on_fulfilled, ValueType::Callable)?;
                        }
                        if let Some(on_rejected) = on_rejected {
                            require_type(&types, *on_rejected, ValueType::Callable)?;
                        }
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
                    Instruction::ToNumber {
                        operand,
                        operand_type,
                        ..
                    } => {
                        require_type(&types, *operand, *operand_type)?;
                        if matches!(
                            operand_type,
                            ValueType::Object
                                | ValueType::Callable
                                | ValueType::Cell
                                | ValueType::Promise
                        ) {
                            bail!("native ToNumber cannot observe object coercion")
                        }
                    }
                    Instruction::TypeOfDynamic { operand, .. } => {
                        require_type(&types, *operand, ValueType::Dynamic)?
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
                        let target =
                            verify_direct_target(program, callee, argument_types, "direct call")?;
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

                    Instruction::CurrentThis { .. } => {}
                    Instruction::CurrentCallable { .. } => {
                        if function.return_type.is_none() {
                            bail!("process entry không có current callable")
                        }
                    }
                    Instruction::ArgumentsObject { .. } | Instruction::RestArray { .. } => {
                        if function.return_type.is_none() {
                            bail!("process entry không có JavaScript argv")
                        }
                    }
                    Instruction::ArrayPush {
                        array,
                        value,
                        value_type,
                    } => {
                        require_type(&types, *array, ValueType::Object)?;
                        require_type(&types, *value, *value_type)?;
                    }
                    Instruction::ArraySpread {
                        array,
                        iterable,
                        iterable_type,
                    } => {
                        require_type(&types, *array, ValueType::Object)?;
                        require_type(&types, *iterable, *iterable_type)?;
                    }
                    Instruction::DynamicUnary {
                        operand,
                        operand_type,
                        ..
                    } => require_type(&types, *operand, *operand_type)?,
                    Instruction::DynamicBinary {
                        left,
                        left_type,
                        right,
                        right_type,
                        ..
                    } => {
                        require_type(&types, *left, *left_type)?;
                        require_type(&types, *right, *right_type)?;
                    }
                    Instruction::DynamicGet {
                        object,
                        object_type,
                        ..
                    }
                    | Instruction::DynamicDelete {
                        object,
                        object_type,
                        ..
                    } => require_type(&types, *object, *object_type)?,
                    Instruction::DynamicSet {
                        object,
                        object_type,
                        value,
                        value_type,
                        ..
                    } => {
                        require_type(&types, *object, *object_type)?;
                        require_type(&types, *value, *value_type)?;
                    }
                    Instruction::ClosureNewGeneric {
                        function: callee,
                        captures,
                        capture_types,
                        lexical_this,
                        lexical_this_type,
                        ..
                    } => {
                        if captures.len() != capture_types.len() {
                            bail!("generic closure capture metadata không khớp")
                        }
                        for (capture, value_type) in captures.iter().zip(capture_types) {
                            require_type(&types, *capture, *value_type)?;
                        }
                        match (lexical_this, lexical_this_type) {
                            (Some(value), Some(value_type)) => {
                                require_type(&types, *value, *value_type)?;
                            }
                            (None, None) => {}
                            _ => bail!("lexical this metadata không khớp"),
                        }
                        let target = program
                            .functions
                            .iter()
                            .find(|candidate| candidate.name == *callee)
                            .ok_or_else(|| {
                                anyhow::anyhow!("unknown generic closure function `{callee}`")
                            })?;
                        if target.return_type.is_none() {
                            bail!("generic closure không được trỏ tới process entry")
                        }
                        if target.captures.len() != captures.len() {
                            bail!("generic closure `{callee}` sai capture arity")
                        }
                    }
                    Instruction::CallValue {
                        callee,
                        callee_type,
                        receiver,
                        receiver_type,
                        arguments,
                        ..
                    } => {
                        require_callable_type(&types, *callee, *callee_type)?;
                        verify_receiver(&types, *receiver, *receiver_type)?;
                        verify_generic_call_arguments(&types, arguments)?;
                    }
                    Instruction::ConstructValue {
                        callee,
                        callee_type,
                        arguments,
                        ..
                    } => {
                        require_callable_type(&types, *callee, *callee_type)?;
                        verify_generic_call_arguments(&types, arguments)?;
                    }
                    Instruction::BindValue {
                        target,
                        target_type,
                        this_arg,
                        this_type,
                        arguments,
                        ..
                    } => {
                        require_callable_type(&types, *target, *target_type)?;
                        require_type(&types, *this_arg, *this_type)?;
                        verify_generic_call_arguments(&types, arguments)?;
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
                Terminator::ThrowValue { value, value_type } => {
                    // A thrown value is not a normal function result and must
                    // never participate in return-type validation.
                    require_type(&types, *value, *value_type)?;
                }
                Terminator::TailCallDirect {
                    function: callee,
                    arguments,
                    argument_types,
                } => {
                    verify_call_arguments(&types, arguments, argument_types)?;
                    let target =
                        verify_direct_target(program, callee, argument_types, "direct tail call")?;
                    if function.return_type.is_none() {
                        bail!(
                            "process entry `{}` không được tail-call JavaScript function",
                            function.name
                        )
                    }
                    // TailCallDirect owns a fresh logical call frame. LLVM
                    // codegen may implement that frame with TLS storage, but
                    // IR validity must not depend on reusing caller argv or on
                    // caller/callee arity equality.
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
        Instruction::ToNumber { result, .. } => (*result, ValueType::Number),
        Instruction::TypeOfDynamic { result, .. } => (*result, ValueType::String),
        Instruction::UnaryNumber { result, .. } => (*result, ValueType::Number),
        Instruction::UnaryBool { result, .. } => (*result, ValueType::Bool),
        Instruction::BinaryNumber { result, .. } => (*result, ValueType::Number),
        Instruction::CompareNumber { result, .. } => (*result, ValueType::Bool),
        Instruction::CompareString { result, .. } => (*result, ValueType::Bool),
        Instruction::CompareObject { result, .. } => (*result, ValueType::Bool),
        Instruction::Phi {
            result, value_type, ..
        } => (*result, *value_type),

        Instruction::CurrentThis { result } => (*result, ValueType::Dynamic),
        Instruction::CurrentCallable { result } => (*result, ValueType::Callable),
        Instruction::ArgumentsObject { result } | Instruction::RestArray { result, .. } => {
            (*result, ValueType::Object)
        }
        Instruction::DynamicUnary { result, .. }
        | Instruction::DynamicBinary { result, .. }
        | Instruction::DynamicGet { result, .. }
        | Instruction::CallValue { result, .. }
        | Instruction::ConstructValue { result, .. } => (*result, ValueType::Dynamic),
        Instruction::DynamicDelete { result, .. } => (*result, ValueType::Bool),
        Instruction::ClosureNewGeneric { result, .. } | Instruction::BindValue { result, .. } => {
            (*result, ValueType::Callable)
        }
        Instruction::ArrayPush { .. }
        | Instruction::ArraySpread { .. }
        | Instruction::DynamicSet { .. } => return None,

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
        Instruction::PromiseResolved { result, .. }
        | Instruction::PromiseRejected { result, .. } => (*result, ValueType::Promise),
        Instruction::PromisePending { result } => (*result, ValueType::Promise),
        Instruction::PromiseSettle { .. } => return None,
        Instruction::PromiseThen { result, .. } => (*result, ValueType::Promise),
        Instruction::MicrotaskDrain => return None,
    })
}

fn verify_generic_call_arguments(
    types: &HashMap<ValueId, ValueType>,
    arguments: &[CallArgument],
) -> Result<()> {
    for argument in arguments {
        require_type(types, argument.value, argument.value_type)?;
    }
    Ok(())
}

fn verify_receiver(
    types: &HashMap<ValueId, ValueType>,
    receiver: Option<ValueId>,
    receiver_type: Option<ValueType>,
) -> Result<()> {
    match (receiver, receiver_type) {
        (Some(value), Some(value_type)) => require_type(types, value, value_type),
        (None, None) => Ok(()),
        _ => bail!("receiver metadata không khớp"),
    }
}

fn require_callable_type(
    types: &HashMap<ValueId, ValueType>,
    value: ValueId,
    value_type: ValueType,
) -> Result<()> {
    require_type(types, value, value_type)?;
    if !matches!(value_type, ValueType::Callable | ValueType::Dynamic) {
        bail!(
            "callee phải là Callable hoặc Dynamic, nhận {:?}",
            value_type
        )
    }
    Ok(())
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

fn verify_direct_target<'a>(
    program: &'a Program,
    callee: &str,
    argument_types: &[ValueType],
    operation: &str,
) -> Result<&'a Function> {
    let target = program
        .functions
        .iter()
        .find(|candidate| candidate.name == callee)
        .ok_or_else(|| anyhow::anyhow!("unknown {operation} callee `{callee}`"))?;

    if target.return_type.is_none() {
        bail!("{operation} `{callee}` không được gọi process entry")
    }
    if !target.captures.is_empty() {
        bail!(
            "{operation} `{callee}` thiếu closure environment cho {} capture",
            target.captures.len()
        )
    }
    if target.parameters.len() != argument_types.len() {
        bail!(
            "{operation} `{callee}` sai arity: cần {}, nhận {}",
            target.parameters.len(),
            argument_types.len()
        )
    }
    for (index, (parameter, actual)) in target.parameters.iter().zip(argument_types).enumerate() {
        if parameter.value_type != *actual {
            bail!(
                "{operation} `{callee}` argument {index} có kiểu {:?}, target cần {:?}",
                actual,
                parameter.value_type
            )
        }
    }
    Ok(target)
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
            | Terminator::ThrowValue { .. }
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
                    Instruction::PromiseRejected {
                        result,
                        reason,
                        reason_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = promise_rejected {:?} %v{}",
                        result.0, reason_type, reason.0
                    )
                    .unwrap(),
                    Instruction::PromisePending { result } => writeln!(
                        &mut output,
                        "    %v{} = promise_pending",
                        result.0
                    )
                    .unwrap(),
                    Instruction::PromiseSettle {
                        promise,
                        value,
                        value_type,
                        rejected,
                    } => writeln!(
                        &mut output,
                        "    promise_settle %v{}, {:?} %v{}, rejected={}",
                        promise.0, value_type, value.0, rejected
                    )
                    .unwrap(),
                    Instruction::PromiseThen {
                        result,
                        promise,
                        on_fulfilled,
                        on_rejected,
                    } => writeln!(
                        &mut output,
                        "    %v{} = promise_then %v{}, {:?}, {:?}",
                        result.0, promise.0, on_fulfilled, on_rejected
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
                    Instruction::ToNumber {
                        result,
                        operand,
                        operand_type,
                    } => writeln!(
                        &mut output,
                        "    %v{} = to_number {:?} %v{}",
                        result.0, operand_type, operand.0
                    )
                    .unwrap(),
                    Instruction::TypeOfDynamic { result, operand } => writeln!(
                        &mut output,
                        "    %v{} = typeof_dynamic %v{}",
                        result.0, operand.0
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

                    other => {
                        writeln!(&mut output, "    {other:?}").unwrap();
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
                Terminator::ThrowValue { value, value_type } => {
                    writeln!(&mut output, "    throw {:?} %v{}", value_type, value.0).unwrap()
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

#[cfg(test)]
mod throw_tests {
    use super::*;

    fn function_with(terminator: Terminator, instruction: Instruction) -> Program {
        Program {
            functions: vec![Function {
                name: "js.test.0".to_owned(),
                parameters: Vec::new(),
                captures: Vec::new(),
                return_type: Some(ValueType::Number),
                blocks: vec![BasicBlock {
                    name: "entry".to_owned(),
                    instructions: vec![instruction],
                    terminator,
                }],
            }],
        }
    }

    #[test]
    fn thrown_type_does_not_have_to_match_normal_return_type() {
        let value = ValueId(0);
        let program = function_with(
            Terminator::ThrowValue {
                value,
                value_type: ValueType::String,
            },
            Instruction::ConstString {
                result: value,
                value: "boom".to_owned(),
            },
        );
        verify_program(&program).unwrap();
    }

    #[test]
    fn throw_operand_is_still_strongly_typed() {
        let value = ValueId(0);
        let program = function_with(
            Terminator::ThrowValue {
                value,
                value_type: ValueType::Number,
            },
            Instruction::ConstString {
                result: value,
                value: "boom".to_owned(),
            },
        );
        let error = verify_program(&program).unwrap_err().to_string();
        assert!(error.contains("cần Number"), "{error}");
    }
}
