use std::{
    env, fs,
    path::{Path, PathBuf},
};

fn main() {
    println!("cargo:rerun-if-env-changed=LLVM_SYS_221_PREFIX");

    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("windows") {
        panic!("the LLVM-C linking setup currently supports Windows only");
    }

    let llvm_prefix = env::var_os("LLVM_SYS_221_PREFIX")
        .map(PathBuf::from)
        .expect("LLVM_SYS_221_PREFIX must point to LLVM 22");
    let llvm_lib_dir = llvm_prefix.join("lib");
    let llvm_import_library = llvm_lib_dir.join("LLVM-C.lib");
    let llvm_dll = llvm_prefix.join("bin").join("LLVM-C.dll");

    require_file(&llvm_import_library);
    require_file(&llvm_dll);

    println!("cargo:rustc-link-search=native={}", llvm_lib_dir.display());
    println!("cargo:rustc-link-lib=dylib=LLVM-C");
    println!("cargo:rerun-if-changed={}", llvm_dll.display());

    copy_runtime_dll(&llvm_dll);
}

fn require_file(path: &Path) {
    if !path.is_file() {
        panic!("required LLVM file does not exist: {}", path.display());
    }
}

fn copy_runtime_dll(source: &Path) {
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo did not provide OUT_DIR"));
    let profile_dir = out_dir
        .ancestors()
        .nth(3)
        .expect("unexpected Cargo OUT_DIR layout");

    for destination_dir in [profile_dir.to_path_buf(), profile_dir.join("deps")] {
        fs::create_dir_all(&destination_dir).unwrap_or_else(|error| {
            panic!("could not create {}: {error}", destination_dir.display())
        });

        let destination = destination_dir.join("LLVM-C.dll");
        fs::copy(source, &destination).unwrap_or_else(|error| {
            panic!(
                "could not copy {} to {}: {error}",
                source.display(),
                destination.display()
            )
        });
    }
}
