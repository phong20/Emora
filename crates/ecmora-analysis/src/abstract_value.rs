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
    const BIGINT: u16 = 1 << 8;
    const ALL: u16 = (1 << 9) - 1;
    const NUMBER_COERCIBLE_PRIMITIVES: u16 =
        Self::UNDEFINED | Self::NULL | Self::BOOL | Self::NUMBER | Self::STRING;

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

    pub(super) fn from_value(value: Value) -> Self {
        let mask = match &value {
            Value::Undefined => Self::UNDEFINED,
            Value::Null => Self::NULL,
            Value::Bool(_) => Self::BOOL,
            Value::Number(_) => Self::NUMBER,
            Value::BigInt(_) => Self::BIGINT,
            Value::String(_) => Self::STRING,
            Value::Object(_) | Value::Array(_) => Self::OBJECT,
            Value::Function(_) => Self::CALLABLE,
            Value::Promise(_) => Self::PROMISE,
        };
        Self {
            mask,
            constant: Some(value),
        }
    }

    pub(super) fn join(self, other: Self) -> Self {
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
            Self::BIGINT => return None,
            _ => return None,
        })
    }

    pub(super) fn constant(&self) -> Option<&Value> {
        self.constant.as_ref()
    }

    pub(super) fn numeric_coercion_safe(&self) -> bool {
        self.mask != 0 && self.mask & !Self::NUMBER_COERCIBLE_PRIMITIVES == 0
    }

    pub(super) fn may_be_string(&self) -> bool {
        self.mask & Self::STRING != 0
    }

    pub(super) fn may_be_bigint(&self) -> bool {
        self.mask & Self::BIGINT != 0
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
        ExpressionKind::BigInt(value) => match ecmora_value::parse_bigint_literal(value) {
            Ok(value) => AbstractValue::from_value(Value::BigInt(value)),
            Err(_) => AbstractValue {
                mask: AbstractValue::BIGINT,
                constant: None,
            },
        },
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
            if let Some(value) = argument.constant.clone() {
                let folded = match operator {
                    UnaryOperator::Plus
                    | UnaryOperator::Minus
                    | UnaryOperator::Not
                    | UnaryOperator::BitwiseNot => ecmora_value::unary_checked(
                        match operator {
                            UnaryOperator::Plus => ecmora_value::UnaryOperator::Plus,
                            UnaryOperator::Minus => ecmora_value::UnaryOperator::Minus,
                            UnaryOperator::Not => ecmora_value::UnaryOperator::Not,
                            UnaryOperator::BitwiseNot => ecmora_value::UnaryOperator::BitwiseNot,
                            _ => unreachable!(),
                        },
                        value,
                    )
                    .ok(),
                    UnaryOperator::Typeof => Some(Value::String(
                        match value {
                            Value::Undefined => "undefined",
                            Value::Null => "object",
                            Value::Bool(_) => "boolean",
                            Value::Number(_) => "number",
                            Value::BigInt(_) => "bigint",
                            Value::String(_) => "string",
                            Value::Function(_) => "function",
                            Value::Object(_) | Value::Array(_) | Value::Promise(_) => "object",
                        }
                        .to_owned(),
                    )),
                    UnaryOperator::Void => Some(Value::Undefined),
                    UnaryOperator::Delete => Some(Value::Bool(true)),
                };
                if let Some(folded) = folded {
                    return AbstractValue::from_value(folded);
                }
            }
            match operator {
                UnaryOperator::Minus | UnaryOperator::BitwiseNot if argument.may_be_bigint() => {
                    AbstractValue {
                        mask: AbstractValue::NUMBER | AbstractValue::BIGINT,
                        constant: None,
                    }
                }
                UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitwiseNot => {
                    AbstractValue::from_type(ValueType::Number, None)
                }
                UnaryOperator::Not | UnaryOperator::Delete => {
                    AbstractValue::from_type(ValueType::Bool, None)
                }
                UnaryOperator::Typeof => AbstractValue::from_type(ValueType::String, None),
                UnaryOperator::Void => AbstractValue::from_type(ValueType::Undefined, None),
            }
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
            if matches!(
                operator,
                BinaryOperator::Equal
                    | BinaryOperator::NotEqual
                    | BinaryOperator::StrictEqual
                    | BinaryOperator::StrictNotEqual
                    | BinaryOperator::LessThan
                    | BinaryOperator::LessEqual
                    | BinaryOperator::GreaterThan
                    | BinaryOperator::GreaterEqual
                    | BinaryOperator::In
                    | BinaryOperator::InstanceOf
            ) {
                return AbstractValue::from_type(ValueType::Bool, None);
            }
            if *operator == BinaryOperator::Add && (left.may_be_string() || right.may_be_string()) {
                return AbstractValue {
                    mask: AbstractValue::STRING | AbstractValue::NUMBER | AbstractValue::BIGINT,
                    constant: None,
                };
            }
            if left.may_be_bigint() || right.may_be_bigint() {
                return AbstractValue {
                    mask: AbstractValue::NUMBER | AbstractValue::BIGINT,
                    constant: None,
                };
            }
            AbstractValue::from_type(ValueType::Number, None)
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
        ExpressionKind::Update { target: _, .. } => AbstractValue {
            mask: AbstractValue::NUMBER | AbstractValue::BIGINT,
            constant: None,
        },
        ExpressionKind::Call { callee, .. } => match &callee.kind {
            ExpressionKind::Global(name) => match name.as_str() {
                "Number" => AbstractValue::from_type(ValueType::Number, None),
                "String" => AbstractValue::from_type(ValueType::String, None),
                "Boolean" => AbstractValue::from_type(ValueType::Bool, None),
                "BigInt" => AbstractValue {
                    mask: AbstractValue::BIGINT,
                    constant: None,
                },
                _ => AbstractValue::dynamic(),
            },
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
