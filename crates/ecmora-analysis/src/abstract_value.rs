use ecmora_hir::{
    BinaryOperator, Expression, ExpressionKind, LogicalOperator, MemberProperty, UnaryOperator,
};
use ecmora_ir::ValueType;
use ecmora_value::Value;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(super) struct AbstractValue {
    mask: u16,
    constant: Option<Value>,
}

impl AbstractValue {
    const UNDEFINED: u16 = 1 << 0;
    const NULL: u16 = 1 << 1;
    const BOOL: u16 = 1 << 2;
    const NUMBER: u16 = 1 << 3;
    const STRING: u16 = 1 << 4;
    const OBJECT: u16 = 1 << 5;
    const CALLABLE: u16 = 1 << 6;
    const PROMISE: u16 = 1 << 7;
    const ALL: u16 = (1 << 8) - 1;

    pub(super) fn dynamic() -> Self {
        Self {
            mask: Self::ALL,
            constant: None,
        }
    }

    pub(super) fn from_type(value_type: ValueType, constant: Option<Value>) -> Self {
        let mask = match value_type {
            ValueType::Undefined => Self::UNDEFINED,
            ValueType::Null => Self::NULL,
            ValueType::Bool => Self::BOOL,
            ValueType::Number => Self::NUMBER,
            ValueType::String => Self::STRING,
            ValueType::Object => Self::OBJECT,
            ValueType::Callable => Self::CALLABLE,
            ValueType::Promise => Self::PROMISE,
            ValueType::Dynamic | ValueType::Cell => Self::ALL,
        };
        Self { mask, constant }
    }

    pub(super) fn single_type(&self) -> Option<ValueType> {
        Some(match self.mask {
            Self::UNDEFINED => ValueType::Undefined,
            Self::NULL => ValueType::Null,
            Self::BOOL => ValueType::Bool,
            Self::NUMBER => ValueType::Number,
            Self::STRING => ValueType::String,
            Self::OBJECT => ValueType::Object,
            Self::CALLABLE => ValueType::Callable,
            Self::PROMISE => ValueType::Promise,
            _ => return None,
        })
    }

    fn from_value(value: Value) -> Self {
        let value_type = match &value {
            Value::Undefined => ValueType::Undefined,
            Value::Null => ValueType::Null,
            Value::Bool(_) => ValueType::Bool,
            Value::Number(_) => ValueType::Number,
            Value::String(_) => ValueType::String,
            Value::Object(_) | Value::Array(_) => ValueType::Object,
            Value::Function(_) => ValueType::Callable,
            Value::Promise(_) => ValueType::Promise,
        };
        Self::from_type(value_type, Some(value))
    }

    fn join(self, other: Self) -> Self {
        let constant = if self.constant == other.constant {
            self.constant
        } else {
            None
        };
        Self {
            mask: self.mask | other.mask,
            constant,
        }
    }

    fn truthiness(&self) -> Option<bool> {
        self.constant.as_ref().map(ecmora_value::to_boolean)
    }
}

pub(super) fn evaluate(
    expression: &Expression,
    bindings: &HashMap<String, AbstractValue>,
) -> AbstractValue {
    match &expression.kind {
        ExpressionKind::String(value) => AbstractValue::from_value(Value::String(value.clone())),
        ExpressionKind::Number(value) => AbstractValue::from_value(Value::Number(*value)),
        ExpressionKind::Bool(value) => AbstractValue::from_value(Value::Bool(*value)),
        ExpressionKind::Null => AbstractValue::from_value(Value::Null),
        ExpressionKind::Global(name) => {
            bindings
                .get(name)
                .cloned()
                .unwrap_or_else(|| match name.as_str() {
                    "undefined" => AbstractValue::from_value(Value::Undefined),
                    "NaN" => AbstractValue::from_value(Value::Number(f64::NAN)),
                    "Infinity" => AbstractValue::from_value(Value::Number(f64::INFINITY)),
                    _ => AbstractValue::dynamic(),
                })
        }
        ExpressionKind::Object(_) | ExpressionKind::Array(_) => {
            AbstractValue::from_type(ValueType::Object, None)
        }
        ExpressionKind::Function(_) => AbstractValue::from_type(ValueType::Callable, None),
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => match evaluate(test, bindings).truthiness() {
            Some(true) => evaluate(consequent, bindings),
            Some(false) => evaluate(alternate, bindings),
            None => evaluate(consequent, bindings).join(evaluate(alternate, bindings)),
        },
        ExpressionKind::Unary { operator, argument } => {
            let argument = evaluate(argument, bindings);
            if let Some(value) = argument.constant {
                let folded = match operator {
                    UnaryOperator::Plus
                    | UnaryOperator::Minus
                    | UnaryOperator::Not
                    | UnaryOperator::BitwiseNot => ecmora_value::unary(
                        match operator {
                            UnaryOperator::Plus => ecmora_value::UnaryOperator::Plus,
                            UnaryOperator::Minus => ecmora_value::UnaryOperator::Minus,
                            UnaryOperator::Not => ecmora_value::UnaryOperator::Not,
                            UnaryOperator::BitwiseNot => ecmora_value::UnaryOperator::BitwiseNot,
                            _ => unreachable!(),
                        },
                        value,
                    ),
                    UnaryOperator::Typeof => Value::String(
                        match value {
                            Value::Undefined => "undefined",
                            Value::Null => "object",
                            Value::Bool(_) => "boolean",
                            Value::Number(_) => "number",
                            Value::String(_) => "string",
                            Value::Function(_) => "function",
                            Value::Object(_) | Value::Array(_) | Value::Promise(_) => "object",
                        }
                        .to_owned(),
                    ),
                    UnaryOperator::Void => Value::Undefined,
                    UnaryOperator::Delete => Value::Bool(true),
                };
                return AbstractValue::from_value(folded);
            }
            AbstractValue::from_type(
                match operator {
                    UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitwiseNot => {
                        ValueType::Number
                    }
                    UnaryOperator::Not | UnaryOperator::Delete => ValueType::Bool,
                    UnaryOperator::Typeof => ValueType::String,
                    UnaryOperator::Void => ValueType::Undefined,
                },
                None,
            )
        }
        ExpressionKind::Binary {
            left,
            operator,
            right,
        } => {
            let left = evaluate(left, bindings);
            let right = evaluate(right, bindings);
            if let (Some(left), Some(right)) = (left.constant.clone(), right.constant.clone()) {
                if let Ok(value) = ecmora_value::binary(to_sem_binary(*operator), left, right) {
                    return AbstractValue::from_value(value);
                }
            }
            AbstractValue::from_type(
                match operator {
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
                        if left.mask == AbstractValue::STRING || right.mask == AbstractValue::STRING
                        {
                            ValueType::String
                        } else if left.mask == AbstractValue::NUMBER
                            && right.mask == AbstractValue::NUMBER
                        {
                            ValueType::Number
                        } else {
                            ValueType::Dynamic
                        }
                    }
                    _ => ValueType::Number,
                },
                None,
            )
        }
        ExpressionKind::Logical {
            left,
            operator,
            right,
        } => {
            let left = evaluate(left, bindings);
            match operator {
                LogicalOperator::Or => match left.truthiness() {
                    Some(true) => left,
                    Some(false) => evaluate(right, bindings),
                    None => left.join(evaluate(right, bindings)),
                },
                LogicalOperator::And => match left.truthiness() {
                    Some(false) => left,
                    Some(true) => evaluate(right, bindings),
                    None => left.join(evaluate(right, bindings)),
                },
                LogicalOperator::Nullish => {
                    if left.mask & (AbstractValue::NULL | AbstractValue::UNDEFINED) == 0 {
                        left
                    } else if left.mask & !(AbstractValue::NULL | AbstractValue::UNDEFINED) == 0 {
                        evaluate(right, bindings)
                    } else {
                        left.join(evaluate(right, bindings))
                    }
                }
            }
        }
        ExpressionKind::Assignment { value, .. } => evaluate(value, bindings),
        ExpressionKind::Update { .. } => AbstractValue::from_type(ValueType::Number, None),
        ExpressionKind::Call { callee, .. } => match &callee.kind {
            ExpressionKind::Global(name) => AbstractValue::from_type(
                match name.as_str() {
                    "Number" => ValueType::Number,
                    "String" => ValueType::String,
                    "Boolean" => ValueType::Bool,
                    _ => ValueType::Dynamic,
                },
                None,
            ),
            ExpressionKind::Member {
                object,
                property: MemberProperty::Static(method),
            } if matches!(&object.kind, ExpressionKind::Global(name) if name == "Promise")
                && matches!(method.as_str(), "resolve" | "reject") =>
            {
                AbstractValue::from_type(ValueType::Promise, None)
            }
            _ => AbstractValue::dynamic(),
        },
        ExpressionKind::New { callee, .. } => {
            if matches!(&callee.kind, ExpressionKind::Global(name) if name == "Promise") {
                AbstractValue::from_type(ValueType::Promise, None)
            } else {
                AbstractValue::from_type(ValueType::Object, None)
            }
        }
        ExpressionKind::Await(_) | ExpressionKind::Member { .. } | ExpressionKind::This => {
            AbstractValue::dynamic()
        }
    }
}

fn to_sem_binary(operator: BinaryOperator) -> ecmora_value::BinaryOperator {
    use ecmora_value::BinaryOperator as Sem;
    match operator {
        BinaryOperator::Add => Sem::Add,
        BinaryOperator::Subtract => Sem::Subtract,
        BinaryOperator::Multiply => Sem::Multiply,
        BinaryOperator::Divide => Sem::Divide,
        BinaryOperator::Remainder => Sem::Remainder,
        BinaryOperator::Exponential => Sem::Exponential,
        BinaryOperator::Equal => Sem::Equal,
        BinaryOperator::NotEqual => Sem::NotEqual,
        BinaryOperator::StrictEqual => Sem::StrictEqual,
        BinaryOperator::StrictNotEqual => Sem::StrictNotEqual,
        BinaryOperator::LessThan => Sem::LessThan,
        BinaryOperator::LessEqual => Sem::LessEqual,
        BinaryOperator::GreaterThan => Sem::GreaterThan,
        BinaryOperator::GreaterEqual => Sem::GreaterEqual,
        BinaryOperator::ShiftLeft => Sem::ShiftLeft,
        BinaryOperator::ShiftRight => Sem::ShiftRight,
        BinaryOperator::ShiftRightZeroFill => Sem::ShiftRightZeroFill,
        BinaryOperator::BitwiseOr => Sem::BitwiseOr,
        BinaryOperator::BitwiseXor => Sem::BitwiseXor,
        BinaryOperator::BitwiseAnd => Sem::BitwiseAnd,
        BinaryOperator::In => Sem::In,
        BinaryOperator::InstanceOf => Sem::InstanceOf,
    }
}
