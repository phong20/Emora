use std::{
    ffi::{CStr, c_char},
    path::Path,
    slice,
};

/// Marker used by the driver so Cargo always emits the companion static library.
pub fn ensure_linked() {}

/// Parse and execute an embedded ECMAScript source inside a native executable.
///
/// # Safety
/// `path` must be a valid NUL-terminated string. `source` must address `length`
/// readable bytes for the duration of this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ecmora_execute_source(
    path: *const c_char,
    source: *const u8,
    length: usize,
) -> i32 {
    let result = std::panic::catch_unwind(|| {
        if path.is_null() || source.is_null() {
            return Err("native host nhận null pointer".to_owned());
        }
        // SAFETY: guaranteed by the exported function contract.
        let path = unsafe { CStr::from_ptr(path) }
            .to_str()
            .map_err(|error| error.to_string())?;
        // SAFETY: guaranteed by the exported function contract.
        let source = unsafe { slice::from_raw_parts(source, length) };
        let source = std::str::from_utf8(source).map_err(|error| error.to_string())?;
        let hir = ecmora_frontend_oxc::lower_source(Path::new(path), source)
            .map_err(|error| format!("{error:#}"))?;
        ecmora_runtime::execute(&hir).map_err(|error| format!("{error:#}"))
    });

    match result {
        Ok(Ok(())) => 0,
        Ok(Err(error)) => {
            eprintln!("Ecmora runtime error: {error}");
            1
        }
        Err(_) => {
            eprintln!("Ecmora runtime panic");
            101
        }
    }
}
