use super::ClosureBinding;
use ecmora_ir::ValueType;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

pub(super) const MAX_SPECIALIZATIONS_PER_FUNCTION: usize = 64;

/// Typed identity of one native function specialization.
///
/// New dimensions such as object shapes, calling conventions, or guard sets
/// belong here instead of being appended to ad-hoc formatted strings.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct SpecializationKey {
    function: String,
    parameter_types: Vec<ValueType>,
    captures: Vec<(String, ValueType)>,
    callbacks: Vec<(String, u64)>,
    return_seed: ValueType,
}

impl SpecializationKey {
    pub(super) fn new(
        function: &str,
        parameter_types: Vec<ValueType>,
        captures: Vec<(String, ValueType)>,
        callbacks: Vec<(String, u64)>,
        return_seed: ValueType,
    ) -> Self {
        Self {
            function: function.to_owned(),
            parameter_types,
            captures,
            callbacks,
            return_seed,
        }
    }
}

/// Pick the return seed used by both specialization identity and its ABI.
///
/// A concrete body-inferred return type must win over an unrelated caller
/// context, otherwise identical callees are compiled repeatedly. A genuinely
/// Dynamic return still needs its contextual seed for callback-only recursive
/// functions such as `return thunk()` / `return self(...)`.
pub(super) fn canonical_return_seed(inferred: ValueType, expected: Option<ValueType>) -> ValueType {
    if inferred == ValueType::Dynamic {
        expected.unwrap_or(ValueType::Dynamic)
    } else {
        inferred
    }
}

pub(super) fn callback_specialization_fingerprint(callback: &ClosureBinding) -> u64 {
    let mut hasher = DefaultHasher::new();
    format!("{:?}", callback.function).hash(&mut hasher);
    for capture in &callback.captures {
        capture.name.hash(&mut hasher);
        capture.value_type.hash(&mut hasher);
    }
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn return_seed_changes_specialization_identity() {
        let number = SpecializationKey::new(
            "recursive",
            vec![ValueType::Number],
            Vec::new(),
            Vec::new(),
            ValueType::Number,
        );
        let dynamic = SpecializationKey::new(
            "recursive",
            vec![ValueType::Number],
            Vec::new(),
            Vec::new(),
            ValueType::Dynamic,
        );
        assert_ne!(number, dynamic);
    }

    #[test]
    fn concrete_inference_ignores_caller_context() {
        assert_eq!(
            canonical_return_seed(ValueType::Number, Some(ValueType::String)),
            ValueType::Number,
        );
    }

    #[test]
    fn dynamic_inference_uses_contextual_seed() {
        assert_eq!(
            canonical_return_seed(ValueType::Dynamic, Some(ValueType::Number)),
            ValueType::Number,
        );
    }
}
