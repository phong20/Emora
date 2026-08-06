//! Detached compatibility ABI stub.
//!
//! This crate intentionally contains no parser, HIR lowering, analyzer,
//! interpreter, or native compiler dependency. It remains a workspace member
//! only so old external link integrations receive a deterministic failure
//! instead of silently executing a second implementation of JavaScript.

use std::ffi::c_char;

/// Compatibility execution is intentionally unavailable.
pub const COMPATIBILITY_BACKEND_AVAILABLE: bool = false;

/// Legacy no-op retained for source compatibility with external callers.
///
/// The compiler driver does not depend on or call this function.
pub fn ensure_linked() {}

/// Legacy C ABI stub.
///
/// It never reads, parses, lowers, analyzes, or executes `path`/`source`.
/// Status 78 follows the conventional "configuration unavailable" exit code.
///
/// # Safety
/// This function deliberately does not dereference any pointer.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ecmora_execute_source(
    _path: *const c_char,
    _source: *const u8,
    _length: usize,
) -> i32 {
    eprintln!(
        "Ecmora compatibility backend is detached; compile the source through the native SSA/LLVM pipeline"
    );
    78
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compatibility_backend_is_a_non_executing_stub() {
        assert!(!COMPATIBILITY_BACKEND_AVAILABLE);

        // Null is safe specifically because the detached stub does not inspect
        // or execute input. This guards against reconnecting parser/runtime code.
        let status = unsafe { ecmora_execute_source(std::ptr::null(), std::ptr::null(), 0) };
        assert_eq!(status, 78);
    }
}
