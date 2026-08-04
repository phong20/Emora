use anyhow::Result;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

mod object_model;
pub use object_model::*;

#[derive(Debug, Clone)]
pub enum Value {
    Undefined,
    Null,
    Number(f64),
    Bool(bool),
    String(String),
    Object(ObjectRef),
    Array(ArrayRef),
    Function(u64),
    Promise(u64),
}

#[derive(Debug)]
pub struct ObjectData {
    pub properties: HashMap<String, Value>,
    pub property_attributes: HashMap<String, PropertyAttributes>,
    pub accessors: HashMap<String, AccessorDescriptor>,
    pub prototype: Option<ObjectRef>,
    pub extensible: bool,
    pub internal_slots: InternalSlots,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PropertyAttributes {
    pub writable: bool,
    pub enumerable: bool,
    pub configurable: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct AccessorDescriptor {
    pub getter: Option<u64>,
    pub setter: Option<u64>,
    pub enumerable: bool,
    pub configurable: bool,
}

pub type ObjectRef = Rc<RefCell<ObjectData>>;
pub type ArrayRef = Rc<RefCell<Vec<Option<Value>>>>;

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        strict_equal(self, other)
    }
}

pub fn object() -> Value {
    object_with_prototype(None)
}

pub fn object_with_prototype(prototype: Option<ObjectRef>) -> Value {
    object_with_prototype_in_realm(prototype, RealmId::ROOT)
}

pub fn object_with_prototype_in_realm(prototype: Option<ObjectRef>, realm: RealmId) -> Value {
    Value::Object(Rc::new(RefCell::new(ObjectData {
        properties: HashMap::new(),
        property_attributes: HashMap::new(),
        accessors: HashMap::new(),
        prototype,
        extensible: true,
        internal_slots: InternalSlots::ordinary(realm),
    })))
}

pub fn set_prototype(value: &Value, prototype: Option<ObjectRef>) -> Result<()> {
    let Value::Object(object) = value else {
        anyhow::bail!("Object.setPrototypeOf target phải là object")
    };
    let mut cursor = prototype.clone();
    while let Some(candidate) = cursor {
        if Rc::ptr_eq(&candidate, object) {
            anyhow::bail!("cyclic __proto__ value")
        }
        cursor = candidate.borrow().prototype.clone();
    }
    object.borrow_mut().prototype = prototype;
    Ok(())
}

pub fn get_prototype(value: &Value) -> Option<ObjectRef> {
    match value {
        Value::Object(object) => object.borrow().prototype.clone(),
        _ => None,
    }
}

pub fn array(values: Vec<Value>) -> Value {
    array_with_holes(values.into_iter().map(Some).collect())
}

pub fn array_with_holes(values: Vec<Option<Value>>) -> Value {
    Value::Array(Rc::new(RefCell::new(values)))
}

pub fn get_property(value: &Value, key: &str) -> Value {
    match value {
        Value::Object(object) => {
            let object = object.borrow();
            object
                .properties
                .get(key)
                .cloned()
                .or_else(|| object.accessors.get(key).map(|_| Value::Undefined))
                .or_else(|| {
                    object
                        .prototype
                        .as_ref()
                        .map(|p| get_property(&Value::Object(p.clone()), key))
                })
                .unwrap_or(Value::Undefined)
        }
        Value::Array(array) => {
            if key == "length" {
                return Value::Number(array.borrow().len() as f64);
            }
            key.parse::<usize>()
                .ok()
                .and_then(|index| array.borrow().get(index).cloned().flatten())
                .unwrap_or(Value::Undefined)
        }
        Value::String(string) => {
            if key == "length" {
                return Value::Number(string.encode_utf16().count() as f64);
            }
            key.parse::<usize>()
                .ok()
                .and_then(|index| string.chars().nth(index))
                .map(|character| Value::String(character.to_string()))
                .unwrap_or(Value::Undefined)
        }
        _ => Value::Undefined,
    }
}

pub fn set_property(value: &Value, key: String, property: Value) -> Result<Value> {
    match value {
        Value::Object(object) => {
            let mut object = object.borrow_mut();
            let exists =
                object.properties.contains_key(&key) || object.accessors.contains_key(&key);
            if !exists && !object.extensible {
                anyhow::bail!("object không extensible")
            }
            if let Some(attributes) = object.property_attributes.get(&key) {
                if !attributes.writable {
                    anyhow::bail!("property `{key}` không writable")
                }
            }
            if let Some(accessor) = object.accessors.get(&key) {
                if accessor.setter.is_none() {
                    anyhow::bail!("accessor `{key}` không có setter")
                }
            }
            object.accessors.remove(&key);
            object.properties.insert(key.clone(), property.clone());
            object
                .property_attributes
                .entry(key)
                .or_insert(PropertyAttributes {
                    writable: true,
                    enumerable: true,
                    configurable: true,
                });
            Ok(property)
        }
        Value::Array(array) => {
            if key == "length" {
                let Value::Number(length) = property else {
                    anyhow::bail!("array length phải là Number")
                };
                if !length.is_finite() || length < 0.0 || length.fract() != 0.0 {
                    anyhow::bail!("array length không hợp lệ")
                }
                array.borrow_mut().resize(length as usize, None);
                return Ok(property);
            }
            let index = key
                .parse::<usize>()
                .map_err(|_| anyhow::anyhow!("array property phải là index"))?;
            let mut array = array.borrow_mut();
            while array.len() <= index {
                array.push(None);
            }
            array[index] = Some(property.clone());
            Ok(property)
        }
        _ => anyhow::bail!("không thể gán property trên giá trị không phải object"),
    }
}

pub fn define_accessor(
    value: &Value,
    key: String,
    getter: Option<u64>,
    setter: Option<u64>,
) -> Result<()> {
    define_accessor_with_attributes(value, key, getter, setter, true, true)
}

pub fn define_accessor_with_attributes(
    value: &Value,
    key: String,
    getter: Option<u64>,
    setter: Option<u64>,
    enumerable: bool,
    configurable: bool,
) -> Result<()> {
    let Value::Object(object) = value else {
        anyhow::bail!("accessor target phải là object")
    };
    let mut object = object.borrow_mut();
    let exists = object.properties.contains_key(&key) || object.accessors.contains_key(&key);
    if !exists && !object.extensible {
        anyhow::bail!("object không extensible")
    }
    if object
        .property_attributes
        .get(&key)
        .is_some_and(|attributes| !attributes.configurable)
    {
        anyhow::bail!("không thể đổi data property `{key}` non-configurable thành accessor")
    }
    if let Some(previous) = object.accessors.get(&key) {
        if !previous.configurable
            && (previous.enumerable != enumerable
                || configurable
                || getter.is_some_and(|getter| Some(getter) != previous.getter)
                || setter.is_some_and(|setter| Some(setter) != previous.setter))
        {
            anyhow::bail!("không thể redefine accessor `{key}` non-configurable")
        }
    }
    object.properties.remove(&key);
    object.property_attributes.remove(&key);
    let previous = object
        .accessors
        .get(&key)
        .copied()
        .unwrap_or(AccessorDescriptor {
            getter: None,
            setter: None,
            enumerable,
            configurable,
        });
    object.accessors.insert(
        key,
        AccessorDescriptor {
            getter: getter.or(previous.getter),
            setter: setter.or(previous.setter),
            enumerable,
            configurable,
        },
    );
    Ok(())
}

pub fn get_accessor(value: &Value, key: &str) -> Option<AccessorDescriptor> {
    match value {
        Value::Object(object) => {
            let object = object.borrow();
            object.accessors.get(key).copied().or_else(|| {
                object
                    .prototype
                    .as_ref()
                    .and_then(|prototype| get_accessor(&Value::Object(prototype.clone()), key))
            })
        }
        _ => None,
    }
}

pub fn own_property_keys(value: &Value) -> Vec<String> {
    let mut keys = match value {
        Value::Object(object) => {
            let object = object.borrow();
            object
                .properties
                .keys()
                .filter(|key| {
                    object
                        .property_attributes
                        .get(*key)
                        .is_none_or(|attributes| attributes.enumerable)
                })
                .cloned()
                .chain(
                    object
                        .accessors
                        .iter()
                        .filter(|(_, descriptor)| descriptor.enumerable)
                        .map(|(key, _)| key.clone()),
                )
                .collect()
        }
        Value::Array(array) => array
            .borrow()
            .iter()
            .enumerate()
            .filter(|(_, value)| value.is_some())
            .map(|(index, _)| index.to_string())
            .collect(),
        Value::String(string) => (0..string.chars().count())
            .map(|index| index.to_string())
            .collect(),
        _ => Vec::new(),
    };
    keys.sort();
    keys
}

pub fn delete_property(value: &Value, key: &str) -> bool {
    match value {
        Value::Object(object) => {
            let mut object = object.borrow_mut();
            if object
                .property_attributes
                .get(key)
                .is_some_and(|attributes| !attributes.configurable)
                || object
                    .accessors
                    .get(key)
                    .is_some_and(|accessor| !accessor.configurable)
            {
                return false;
            }
            object.properties.remove(key);
            object.property_attributes.remove(key);
            object.accessors.remove(key);
            true
        }
        Value::Array(array) => {
            if let Ok(index) = key.parse::<usize>() {
                if let Some(slot) = array.borrow_mut().get_mut(index) {
                    *slot = None;
                }
            }
            true
        }
        Value::String(string) => {
            key == "length"
                || key
                    .parse::<usize>()
                    .ok()
                    .is_some_and(|index| index < string.chars().count())
        }
        _ => false,
    }
}

pub fn has_property(value: &Value, key: &str) -> bool {
    match value {
        Value::Object(object) => {
            let object = object.borrow();
            object.properties.contains_key(key)
                || object.accessors.contains_key(key)
                || object
                    .prototype
                    .as_ref()
                    .is_some_and(|prototype| has_property(&Value::Object(prototype.clone()), key))
        }
        Value::Array(array) => {
            key == "length"
                || key
                    .parse::<usize>()
                    .ok()
                    .is_some_and(|index| array.borrow().get(index).is_some_and(Option::is_some))
        }
        _ => false,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    Plus,
    Minus,
    Not,
    BitwiseNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Exponential,
    Equal,
    NotEqual,
    StrictEqual,
    StrictNotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    ShiftLeft,
    ShiftRight,
    ShiftRightZeroFill,
    BitwiseOr,
    BitwiseXor,
    BitwiseAnd,
    In,
    InstanceOf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicalOperator {
    Or,
    And,
    Nullish,
}

pub fn to_boolean(value: &Value) -> bool {
    match value {
        Value::Undefined | Value::Null => false,
        Value::Bool(value) => *value,
        Value::Number(value) => *value != 0.0 && !value.is_nan(),
        Value::String(value) => !value.is_empty(),
        Value::Object(_) | Value::Array(_) | Value::Function(_) | Value::Promise(_) => true,
    }
}

pub fn to_number(value: &Value) -> f64 {
    match value {
        Value::Undefined => f64::NAN,
        Value::Null => 0.0,
        Value::Number(value) => *value,
        Value::Bool(value) => {
            if *value {
                1.0
            } else {
                0.0
            }
        }
        Value::String(value) => string_to_number(value),
        Value::Object(_) => f64::NAN,
        Value::Array(array) => string_to_number(
            &array
                .borrow()
                .iter()
                .map(|value| value.as_ref().map(to_string).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(","),
        ),
        Value::Function(_) | Value::Promise(_) => f64::NAN,
    }
}

pub fn to_string(value: &Value) -> String {
    match value {
        Value::Undefined => "undefined".to_owned(),
        Value::Null => "null".to_owned(),
        Value::Bool(value) => value.to_string(),
        Value::String(value) => value.clone(),
        Value::Number(value) => number_to_string(*value),
        Value::Object(_) => "[object Object]".to_owned(),
        Value::Array(array) => array
            .borrow()
            .iter()
            .map(|value| value.as_ref().map(to_string).unwrap_or_default())
            .collect::<Vec<_>>()
            .join(","),
        Value::Function(_) => "function () { [native code] }".to_owned(),
        Value::Promise(_) => "[object Promise]".to_owned(),
    }
}

pub fn number_to_string(value: f64) -> String {
    if value == 0.0 {
        return "0".to_owned();
    }
    if value.is_nan() {
        return "NaN".to_owned();
    }
    if value == f64::INFINITY {
        return "Infinity".to_owned();
    }
    if value == f64::NEG_INFINITY {
        return "-Infinity".to_owned();
    }
    let mut buffer = ryu_js::Buffer::new();
    buffer.format(value).to_owned()
}

pub fn unary(operator: UnaryOperator, value: Value) -> Value {
    match operator {
        UnaryOperator::Plus => Value::Number(to_number(&value)),
        UnaryOperator::Minus => Value::Number(-to_number(&value)),
        UnaryOperator::Not => Value::Bool(!to_boolean(&value)),
        UnaryOperator::BitwiseNot => Value::Number((!to_int32(to_number(&value))) as f64),
    }
}

pub fn binary(operator: BinaryOperator, left: Value, right: Value) -> Result<Value> {
    match operator {
        BinaryOperator::Add => {
            if matches!(
                left,
                Value::String(_)
                    | Value::Object(_)
                    | Value::Array(_)
                    | Value::Function(_)
                    | Value::Promise(_)
            ) || matches!(
                right,
                Value::String(_)
                    | Value::Object(_)
                    | Value::Array(_)
                    | Value::Function(_)
                    | Value::Promise(_)
            ) {
                return Ok(Value::String(format!(
                    "{}{}",
                    to_string(&left),
                    to_string(&right)
                )));
            }
            Ok(Value::Number(to_number(&left) + to_number(&right)))
        }
        BinaryOperator::Subtract => Ok(Value::Number(to_number(&left) - to_number(&right))),
        BinaryOperator::Multiply => Ok(Value::Number(to_number(&left) * to_number(&right))),
        BinaryOperator::Divide => Ok(Value::Number(to_number(&left) / to_number(&right))),
        BinaryOperator::Remainder => Ok(Value::Number(to_number(&left) % to_number(&right))),
        BinaryOperator::Exponential => Ok(Value::Number(exponentiate(
            to_number(&left),
            to_number(&right),
        ))),
        BinaryOperator::Equal => Ok(Value::Bool(loose_equal(&left, &right))),
        BinaryOperator::NotEqual => Ok(Value::Bool(!loose_equal(&left, &right))),
        BinaryOperator::StrictEqual => Ok(Value::Bool(strict_equal(&left, &right))),
        BinaryOperator::StrictNotEqual => Ok(Value::Bool(!strict_equal(&left, &right))),
        BinaryOperator::LessThan => Ok(Value::Bool(relational(&left, &right, Relational::Less))),
        BinaryOperator::LessEqual => Ok(Value::Bool(relational(
            &left,
            &right,
            Relational::LessEqual,
        ))),
        BinaryOperator::GreaterThan => {
            Ok(Value::Bool(relational(&left, &right, Relational::Greater)))
        }
        BinaryOperator::GreaterEqual => Ok(Value::Bool(relational(
            &left,
            &right,
            Relational::GreaterEqual,
        ))),
        BinaryOperator::ShiftLeft => Ok(Value::Number(
            (to_int32(to_number(&left)) << (to_uint32(to_number(&right)) & 31)) as f64,
        )),
        BinaryOperator::ShiftRight => Ok(Value::Number(
            (to_int32(to_number(&left)) >> (to_uint32(to_number(&right)) & 31)) as f64,
        )),
        BinaryOperator::ShiftRightZeroFill => Ok(Value::Number(
            (to_uint32(to_number(&left)) >> (to_uint32(to_number(&right)) & 31)) as f64,
        )),
        BinaryOperator::BitwiseOr => Ok(Value::Number(
            (to_int32(to_number(&left)) | to_int32(to_number(&right))) as f64,
        )),
        BinaryOperator::BitwiseXor => Ok(Value::Number(
            (to_int32(to_number(&left)) ^ to_int32(to_number(&right))) as f64,
        )),
        BinaryOperator::BitwiseAnd => Ok(Value::Number(
            (to_int32(to_number(&left)) & to_int32(to_number(&right))) as f64,
        )),
        BinaryOperator::In => Ok(Value::Bool(match right {
            Value::Object(_) | Value::Array(_) => has_property(&right, &to_string(&left)),
            _ => false,
        })),
        BinaryOperator::InstanceOf => anyhow::bail!("instanceof cần constructor/prototype runtime"),
    }
}

pub fn logical(
    operator: LogicalOperator,
    left: Value,
    right: impl FnOnce() -> Result<Value>,
) -> Result<Value> {
    match operator {
        LogicalOperator::Or if to_boolean(&left) => Ok(left),
        LogicalOperator::And if !to_boolean(&left) => Ok(left),
        LogicalOperator::Nullish if !matches!(left, Value::Null | Value::Undefined) => Ok(left),
        _ => right(),
    }
}

pub fn assignment(operator: LogicalOperator, left: &Value) -> bool {
    match operator {
        LogicalOperator::Or => to_boolean(left),
        LogicalOperator::And => !to_boolean(left),
        LogicalOperator::Nullish => !matches!(left, Value::Null | Value::Undefined),
    }
}

#[derive(Clone, Copy)]
enum Relational {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

fn relational(left: &Value, right: &Value, op: Relational) -> bool {
    let result = if matches!((left, right), (Value::String(_), Value::String(_))) {
        let left = left_string_units(left);
        let right = left_string_units(right);
        left.cmp(&right)
    } else {
        let left = to_number(left);
        let right = to_number(right);
        let Some(ordering) = left.partial_cmp(&right) else {
            return false;
        };
        ordering
    };
    match op {
        Relational::Less => result == std::cmp::Ordering::Less,
        Relational::LessEqual => result != std::cmp::Ordering::Greater,
        Relational::Greater => result == std::cmp::Ordering::Greater,
        Relational::GreaterEqual => result != std::cmp::Ordering::Less,
    }
}

fn left_string_units(value: &Value) -> Vec<u16> {
    match value {
        Value::String(value) => value.encode_utf16().collect(),
        _ => unreachable!(),
    }
}

fn strict_equal(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Undefined, Value::Undefined) | (Value::Null, Value::Null) => true,
        (Value::Bool(left), Value::Bool(right)) => left == right,
        (Value::String(left), Value::String(right)) => left == right,
        (Value::Number(left), Value::Number(right)) => {
            !left.is_nan() && !right.is_nan() && left == right
        }
        (Value::Object(left), Value::Object(right)) => Rc::ptr_eq(left, right),
        (Value::Array(left), Value::Array(right)) => Rc::ptr_eq(left, right),
        (Value::Function(left), Value::Function(right)) => left == right,
        (Value::Promise(left), Value::Promise(right)) => left == right,
        _ => false,
    }
}

fn loose_equal(left: &Value, right: &Value) -> bool {
    if std::mem::discriminant(left) == std::mem::discriminant(right) {
        return strict_equal(left, right);
    }
    match (left, right) {
        (Value::Null, Value::Undefined) | (Value::Undefined, Value::Null) => true,
        (Value::Number(_), Value::String(_)) | (Value::String(_), Value::Number(_)) => {
            strict_equal(
                &Value::Number(to_number(left)),
                &Value::Number(to_number(right)),
            )
        }
        (Value::Bool(_), _) => loose_equal(&Value::Number(to_number(left)), right),
        (_, Value::Bool(_)) => loose_equal(left, &Value::Number(to_number(right))),
        (
            Value::Object(_) | Value::Array(_) | Value::Function(_) | Value::Promise(_),
            Value::String(_) | Value::Number(_),
        ) => loose_equal(&Value::String(to_string(left)), right),
        (
            Value::String(_) | Value::Number(_),
            Value::Object(_) | Value::Array(_) | Value::Function(_) | Value::Promise(_),
        ) => loose_equal(left, &Value::String(to_string(right))),
        _ => false,
    }
}

fn to_int32(value: f64) -> i32 {
    if !value.is_finite() || value == 0.0 {
        return 0;
    }
    let integer = value.trunc();
    let modulo = integer.rem_euclid(4_294_967_296.0);
    if modulo >= 2_147_483_648.0 {
        (modulo - 4_294_967_296.0) as i32
    } else {
        modulo as i32
    }
}

fn to_uint32(value: f64) -> u32 {
    to_int32(value) as u32
}

fn string_to_number(value: &str) -> f64 {
    let value = value.trim_matches(is_ecma_whitespace);
    if value.is_empty() {
        return 0.0;
    }
    if value == "Infinity" || value == "+Infinity" {
        return f64::INFINITY;
    }
    if value == "-Infinity" {
        return f64::NEG_INFINITY;
    }
    let (sign, digits, had_sign) = match value.strip_prefix('+') {
        Some(v) => (1.0, v, true),
        None => match value.strip_prefix('-') {
            Some(v) => (-1.0, v, true),
            None => (1.0, value, false),
        },
    };
    if let Some(v) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        return if had_sign {
            f64::NAN
        } else {
            parse_radix(v, 16)
        };
    }
    if let Some(v) = digits
        .strip_prefix("0b")
        .or_else(|| digits.strip_prefix("0B"))
    {
        return if had_sign {
            f64::NAN
        } else {
            parse_radix(v, 2)
        };
    }
    if let Some(v) = digits
        .strip_prefix("0o")
        .or_else(|| digits.strip_prefix("0O"))
    {
        return if had_sign {
            f64::NAN
        } else {
            parse_radix(v, 8)
        };
    }
    if !digits.chars().all(|character| {
        character.is_ascii_digit() || matches!(character, '.' | 'e' | 'E' | '+' | '-')
    }) {
        return f64::NAN;
    }
    let parsed = digits.parse::<f64>().unwrap_or(f64::NAN);
    sign * parsed
}

fn is_ecma_whitespace(c: char) -> bool {
    matches!(
        c,
        '\u{0009}'
            | '\u{000A}'
            | '\u{000B}'
            | '\u{000C}'
            | '\u{000D}'
            | '\u{0020}'
            | '\u{00A0}'
            | '\u{1680}'
            | '\u{2000}'
            ..='\u{200A}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202F}'
                | '\u{205F}'
                | '\u{3000}'
                | '\u{FEFF}'
    )
}

pub fn ensure_number(value: &Value) -> Result<f64> {
    Ok(to_number(value))
}

fn parse_radix(value: &str, radix: u32) -> f64 {
    if value.is_empty() {
        return f64::NAN;
    }
    let mut result = 0.0;
    for digit in value.chars() {
        let Some(digit) = digit.to_digit(radix) else {
            return f64::NAN;
        };
        result = result * radix as f64 + digit as f64;
    }
    result
}

fn exponentiate(base: f64, exponent: f64) -> f64 {
    if exponent == 0.0 {
        return 1.0;
    }
    if exponent.is_nan() || base.is_nan() {
        return f64::NAN;
    }
    if exponent.is_infinite() && base.abs() == 1.0 {
        return f64::NAN;
    }
    base.powf(exponent)
}

#[cfg(test)]
mod tests {
    use super::{
        BinaryOperator, Value, binary, number_to_string, to_boolean, to_number, to_string,
    };

    #[test]
    fn ecma_number_edges() {
        assert_eq!(to_number(&Value::String("  0x10  ".into())), 16.0);
        assert!(to_number(&Value::String("+0x10".into())).is_nan());
        assert_eq!(to_number(&Value::String("".into())), 0.0);
        assert_eq!(number_to_string(-0.0), "0");
        assert_eq!(number_to_string(f64::INFINITY), "Infinity");
    }

    #[test]
    fn ecma_coercion_and_equality() {
        assert!(to_boolean(&Value::String("x".into())));
        assert!(!to_boolean(&Value::Number(f64::NAN)));
        assert_eq!(
            binary(
                BinaryOperator::Add,
                Value::String("x".into()),
                Value::Number(1.0)
            )
            .unwrap(),
            Value::String("x1".into())
        );
        assert_eq!(
            binary(
                BinaryOperator::Equal,
                Value::String("1".into()),
                Value::Number(1.0)
            )
            .unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            binary(
                BinaryOperator::StrictEqual,
                Value::String("1".into()),
                Value::Number(1.0)
            )
            .unwrap(),
            Value::Bool(false)
        );
        assert_eq!(to_string(&Value::Number(2.5)), "2.5");
        assert_eq!(
            binary(BinaryOperator::Equal, Value::Bool(false), Value::Null).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            binary(BinaryOperator::Equal, Value::Bool(false), Value::Undefined).unwrap(),
            Value::Bool(false)
        );
    }
}
