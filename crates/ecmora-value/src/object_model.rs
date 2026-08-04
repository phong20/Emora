use crate::{ObjectRef, Value, object_with_prototype_in_realm};
use anyhow::{Result, bail};
use std::collections::{HashSet, VecDeque};

/// Identity of an ECMAScript Realm.
///
/// The compatibility runtime currently creates one realm per execution entry,
/// but values retain the owner realm so cross-realm intrinsics can be added
/// without changing object layout again.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct RealmId(pub u32);

impl RealmId {
    pub const ROOT: Self = Self(0);
}

#[derive(Debug, Clone)]
pub struct ProxySlots {
    pub target: Value,
    pub handler: Value,
    pub revoked: bool,
}

#[derive(Debug, Clone)]
pub struct ClassConstructorSlots {
    pub name: String,
    pub parent: Option<String>,
    pub realm: RealmId,
    pub constructor: Option<u64>,
    pub prototype: ObjectRef,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncGeneratorState {
    SuspendedStart,
    SuspendedYield,
    Executing,
    AwaitingReturn,
    Completed,
}

#[derive(Debug, Clone)]
pub enum GeneratorCompletion {
    Normal(Value),
    Return(Value),
    Throw(Value),
}

#[derive(Debug, Clone)]
pub struct AsyncGeneratorRequest {
    pub completion: GeneratorCompletion,
    /// Promise capability owned by the runtime job queue.
    pub capability: u64,
}

#[derive(Debug, Clone)]
pub struct AsyncGeneratorSlots {
    pub runtime_id: u64,
    pub state: AsyncGeneratorState,
    pub queue: VecDeque<AsyncGeneratorRequest>,
}

impl AsyncGeneratorSlots {
    pub fn new(runtime_id: u64) -> Self {
        Self {
            runtime_id,
            state: AsyncGeneratorState::SuspendedStart,
            queue: VecDeque::new(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub enum ObjectKind {
    #[default]
    Ordinary,
    Proxy(ProxySlots),
    ClassConstructor(ClassConstructorSlots),
    AsyncGenerator(AsyncGeneratorSlots),
}

#[derive(Debug, Clone)]
pub struct InternalSlots {
    pub realm: RealmId,
    pub kind: ObjectKind,
}

impl InternalSlots {
    pub fn ordinary(realm: RealmId) -> Self {
        Self {
            realm,
            kind: ObjectKind::Ordinary,
        }
    }
}

impl Default for InternalSlots {
    fn default() -> Self {
        Self::ordinary(RealmId::ROOT)
    }
}

pub fn is_object_like(value: &Value) -> bool {
    matches!(
        value,
        Value::Object(_) | Value::Array(_) | Value::Function(_) | Value::Promise(_)
    )
}

pub fn proxy_object(target: Value, handler: Value, realm: RealmId) -> Result<Value> {
    if !is_object_like(&target) {
        bail!("Proxy target phải là object")
    }
    if !is_object_like(&handler) {
        bail!("Proxy handler phải là object")
    }
    let proxy = object_with_prototype_in_realm(None, realm);
    let Value::Object(object) = &proxy else {
        unreachable!("ordinary object constructor did not return an object")
    };
    object.borrow_mut().internal_slots.kind = ObjectKind::Proxy(ProxySlots {
        target,
        handler,
        revoked: false,
    });
    Ok(proxy)
}

pub fn proxy_slots(value: &Value) -> Option<ProxySlots> {
    let Value::Object(object) = value else {
        return None;
    };
    let kind = object.borrow().internal_slots.kind.clone();
    match kind {
        ObjectKind::Proxy(slots) => Some(slots),
        _ => None,
    }
}

pub fn revoke_proxy(value: &Value) -> Result<()> {
    let Value::Object(object) = value else {
        bail!("Proxy revoke target không phải object")
    };
    let mut object = object.borrow_mut();
    let ObjectKind::Proxy(slots) = &mut object.internal_slots.kind else {
        bail!("object không có [[ProxyTarget]]")
    };
    slots.revoked = true;
    slots.target = Value::Null;
    slots.handler = Value::Null;
    Ok(())
}

pub fn object_realm(value: &Value) -> RealmId {
    match value {
        Value::Object(object) => object.borrow().internal_slots.realm,
        _ => RealmId::ROOT,
    }
}

pub fn set_object_realm(value: &Value, realm: RealmId) -> Result<()> {
    let Value::Object(object) = value else {
        bail!("realm slot chỉ tồn tại trên ordinary object wrapper")
    };
    object.borrow_mut().internal_slots.realm = realm;
    Ok(())
}

pub fn object_kind(value: &Value) -> Option<ObjectKind> {
    let Value::Object(object) = value else {
        return None;
    };
    let kind = object.borrow().internal_slots.kind.clone();
    Some(kind)
}

pub fn set_object_kind(value: &Value, kind: ObjectKind) -> Result<()> {
    let Value::Object(object) = value else {
        bail!("internal slots target không phải object")
    };
    object.borrow_mut().internal_slots.kind = kind;
    Ok(())
}

pub fn is_extensible(value: &Value) -> bool {
    match value {
        Value::Object(object) => object.borrow().extensible,
        _ => false,
    }
}

pub fn prevent_extensions(value: &Value) -> Result<()> {
    let Value::Object(object) = value else {
        bail!("Object.preventExtensions target phải là object")
    };
    object.borrow_mut().extensible = false;
    Ok(())
}

pub fn own_property_keys_all(value: &Value) -> Vec<String> {
    let mut keys = match value {
        Value::Object(object) => {
            let object = object.borrow();
            object
                .properties
                .keys()
                .cloned()
                .chain(object.accessors.keys().cloned())
                .collect::<Vec<_>>()
        }
        Value::Array(array) => array
            .borrow()
            .iter()
            .enumerate()
            .filter(|(_, value)| value.is_some())
            .map(|(index, _)| index.to_string())
            .chain(std::iter::once("length".to_owned()))
            .collect(),
        Value::String(string) => (0..string.chars().count())
            .map(|index| index.to_string())
            .chain(std::iter::once("length".to_owned()))
            .collect(),
        _ => Vec::new(),
    };
    keys.sort();
    keys.dedup();
    keys
}

pub fn non_configurable_own_keys(value: &Value) -> HashSet<String> {
    match value {
        Value::Object(object) => {
            let object = object.borrow();
            object
                .property_attributes
                .iter()
                .filter(|(_, attributes)| !attributes.configurable)
                .map(|(key, _)| key.clone())
                .chain(
                    object
                        .accessors
                        .iter()
                        .filter(|(_, descriptor)| !descriptor.configurable)
                        .map(|(key, _)| key.clone()),
                )
                .collect()
        }
        Value::Array(_) | Value::String(_) => HashSet::from(["length".to_owned()]),
        _ => HashSet::new(),
    }
}

pub fn is_non_writable_non_configurable_data_property(value: &Value, key: &str) -> Option<Value> {
    let Value::Object(object) = value else {
        return None;
    };
    let object = object.borrow();
    let attributes = object.property_attributes.get(key)?;
    if attributes.configurable || attributes.writable {
        return None;
    }
    object.properties.get(key).cloned()
}

pub fn same_value(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Number(left), Value::Number(right)) => {
            (left.is_nan() && right.is_nan())
                || (left == right && left.is_sign_negative() == right.is_sign_negative())
        }
        _ => left == right,
    }
}

pub fn class_constructor_object(
    name: String,
    parent: Option<String>,
    constructor: Option<u64>,
    prototype: ObjectRef,
    realm: RealmId,
) -> Value {
    let object = object_with_prototype_in_realm(None, realm);
    set_object_kind(
        &object,
        ObjectKind::ClassConstructor(ClassConstructorSlots {
            name,
            parent,
            realm,
            constructor,
            prototype,
        }),
    )
    .expect("fresh class constructor object");
    object
}

pub fn class_constructor_slots(value: &Value) -> Option<ClassConstructorSlots> {
    match object_kind(value)? {
        ObjectKind::ClassConstructor(slots) => Some(slots),
        _ => None,
    }
}

pub fn async_generator_object(runtime_id: u64, realm: RealmId) -> Value {
    let object = object_with_prototype_in_realm(None, realm);
    set_object_kind(
        &object,
        ObjectKind::AsyncGenerator(AsyncGeneratorSlots::new(runtime_id)),
    )
    .expect("fresh async generator object");
    object
}

pub fn async_generator_slots(value: &Value) -> Option<AsyncGeneratorSlots> {
    match object_kind(value)? {
        ObjectKind::AsyncGenerator(slots) => Some(slots),
        _ => None,
    }
}

pub fn async_generator_enqueue(value: &Value, request: AsyncGeneratorRequest) -> Result<()> {
    let Value::Object(object) = value else {
        bail!("async generator request target không phải object")
    };
    let mut object = object.borrow_mut();
    let ObjectKind::AsyncGenerator(slots) = &mut object.internal_slots.kind else {
        bail!("object không có [[AsyncGeneratorState]]")
    };
    slots.queue.push_back(request);
    Ok(())
}

pub fn async_generator_dequeue(value: &Value) -> Result<Option<AsyncGeneratorRequest>> {
    let Value::Object(object) = value else {
        bail!("async generator request target không phải object")
    };
    let mut object = object.borrow_mut();
    let ObjectKind::AsyncGenerator(slots) = &mut object.internal_slots.kind else {
        bail!("object không có [[AsyncGeneratorState]]")
    };
    Ok(slots.queue.pop_front())
}

pub fn set_async_generator_state(value: &Value, state: AsyncGeneratorState) -> Result<()> {
    let Value::Object(object) = value else {
        bail!("async generator state target không phải object")
    };
    let mut object = object.borrow_mut();
    let ObjectKind::AsyncGenerator(slots) = &mut object.internal_slots.kind else {
        bail!("object không có [[AsyncGeneratorState]]")
    };
    slots.state = state;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{get_property, object, set_property};

    #[test]
    fn proxy_slots_retain_target_handler_and_realm() {
        let target = object();
        let handler = object();
        set_property(&target, "value".to_owned(), Value::Number(7.0)).unwrap();
        let proxy = proxy_object(target.clone(), handler.clone(), RealmId(4)).unwrap();

        let slots = proxy_slots(&proxy).unwrap();
        assert_eq!(object_realm(&proxy), RealmId(4));
        assert_eq!(get_property(&slots.target, "value"), Value::Number(7.0));
        assert!(matches!(slots.handler, Value::Object(_)));
    }

    #[test]
    fn revoked_proxy_clears_observable_slots() {
        let proxy = proxy_object(object(), object(), RealmId::ROOT).unwrap();
        revoke_proxy(&proxy).unwrap();
        let slots = proxy_slots(&proxy).unwrap();
        assert!(slots.revoked);
        assert_eq!(slots.target, Value::Null);
        assert_eq!(slots.handler, Value::Null);
    }

    #[test]
    fn same_value_distinguishes_signed_zero_and_accepts_nan() {
        assert!(!same_value(&Value::Number(0.0), &Value::Number(-0.0)));
        assert!(same_value(
            &Value::Number(f64::NAN),
            &Value::Number(f64::NAN)
        ));
    }
}
