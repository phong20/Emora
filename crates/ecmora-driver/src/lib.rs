use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use anyhow::{Context, Result, bail};

mod modules;

pub fn run_file(path: &Path) -> Result<()> {
    // `run` is deliberately not an interpreter shortcut. It exercises exactly
    // the same native-only pipeline as `build`, then executes that artifact.
    let executable = build_file(path)?;
    let status = Command::new(&executable)
        .status()
        .with_context(|| format!("không thể chạy native executable {}", executable.display()))?;

    if !status.success() {
        bail!(
            "native executable {} kết thúc với status {}",
            executable.display(),
            status
        )
    }

    Ok(())
}

pub fn check_file(path: &Path) -> Result<()> {
    let _ssa = lower_ssa_from_file(path)?;

    println!("OK: {}", path.display());

    Ok(())
}

pub fn dump_ast_file(path: &Path) -> Result<PathBuf> {
    let source = read_source(path)?;

    let ast = ecmora_frontend_oxc::dump_ast(path, &source)?;

    let output = artifact_path(path, "ast.txt")?;

    fs::write(&output, ast).with_context(|| format!("không thể ghi {}", output.display()))?;

    Ok(output)
}

pub fn dump_hir_file(path: &Path) -> Result<PathBuf> {
    let hir = lower_hir_from_file(path)?;
    let output = artifact_path(path, "hir.txt")?;

    fs::write(&output, format!("{hir:#?}"))
        .with_context(|| format!("không thể ghi {}", output.display()))?;

    Ok(output)
}

pub fn dump_ssa_file(path: &Path) -> Result<PathBuf> {
    let ssa = lower_ssa_from_file(path)?;
    let output = artifact_path(path, "ssa.txt")?;

    let dump = ecmora_ir::dump_program(&ssa);

    fs::write(&output, dump).with_context(|| format!("không thể ghi {}", output.display()))?;

    Ok(output)
}

pub fn dump_llvm_file(path: &Path) -> Result<PathBuf> {
    let ssa = lower_ssa_from_file(path)?;
    let output_path = artifact_path(path, "ll")?;

    ecmora_codegen_llvm::write_llvm_ir(&ssa, &output_path)?;

    Ok(output_path)
}
/// Build JavaScript thành executable native.
///
/// Pipeline:
///
/// source → AST → HIR → SSA → LLVM IR → object → native runtime → executable
///
/// There is intentionally no compatibility fallback here. A native analysis,
/// verification, codegen, or linker failure is returned to the caller.
pub fn build_file(path: &Path) -> Result<PathBuf> {
    let ssa = lower_ssa_from_file(path)
        .with_context(|| format!("native analysis/lowering thất bại cho {}", path.display()))?;

    build_ssa_file(path, &ssa)
        .with_context(|| format!("native LLVM codegen/link thất bại cho {}", path.display()))
}

fn build_ssa_file(path: &Path, ssa: &ecmora_ir::Program) -> Result<PathBuf> {
    let object_suffix = if cfg!(windows) { "obj" } else { "o" };

    let object_path = artifact_path(path, object_suffix)?;

    ecmora_codegen_llvm::write_object_file(ssa, &object_path)?;

    let executable_path = executable_artifact_path(path)?;

    // Inkwell đã làm:
    //
    // SSA → LLVM IR → native object file
    //
    // Clang chỉ còn link object file với C runtime
    // để resolve `puts`.
    let clang = find_clang()?;

    let output = Command::new(&clang)
        .arg(&object_path)
        .arg(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("ecmora-runtime")
                .join("native")
                .join("object_runtime.c"),
        )
        .arg("-o")
        .arg(&executable_path)
        .output()
        .with_context(|| format!("không thể chạy linker {:?}", clang))?;

    if !output.status.success() {
        bail!(
            "link executable thất bại\n\
             status: {}\n\
             stdout:\n{}\n\
             stderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    Ok(executable_path)
}

fn lower_hir_from_file(path: &Path) -> Result<ecmora_hir::Program> {
    modules::load_program(path)
}

fn lower_ssa_from_file(path: &Path) -> Result<ecmora_ir::Program> {
    let hir = lower_hir_from_file(path)?;
    let mut ir = ecmora_analysis::analyze(&hir)?;
    ecmora_opt::optimize(&mut ir)?;
    Ok(ir)
}

fn read_source(path: &Path) -> Result<String> {
    fs::read_to_string(path).with_context(|| format!("không đọc được {}", path.display()))
}

fn artifact_path(source_path: &Path, suffix: &str) -> Result<PathBuf> {
    let stem = source_path
        .file_stem()
        .context("source file không có tên")?
        .to_string_lossy();

    let directory = PathBuf::from("target").join("ecmora");

    fs::create_dir_all(&directory)
        .with_context(|| format!("không thể tạo {}", directory.display()))?;

    Ok(directory.join(format!("{stem}.{suffix}")))
}

fn executable_artifact_path(source_path: &Path) -> Result<PathBuf> {
    let stem = source_path
        .file_stem()
        .context("source file không có tên")?
        .to_string_lossy();

    let directory = PathBuf::from("target").join("ecmora");

    fs::create_dir_all(&directory)?;

    let filename = if cfg!(windows) {
        format!("{stem}.exe")
    } else {
        stem.into_owned()
    };

    Ok(directory.join(filename))
}

/// Thứ tự tìm clang:
///
/// 1. ECMORA_CLANG
/// 2. clang trong PATH
/// 3. LLVM_SYS_221_PREFIX
/// 4. C:\tools\LLVM\bin\clang.exe
/// 5. C:\Program Files\LLVM\bin\clang.exe
fn find_clang() -> Result<OsString> {
    let mut candidates = Vec::<OsString>::new();

    if let Some(configured) = env::var_os("ECMORA_CLANG") {
        candidates.push(configured);
    }

    candidates.push(OsString::from("clang"));

    if cfg!(windows) {
        if let Some(prefix) = env::var_os("LLVM_SYS_221_PREFIX") {
            candidates.push(
                PathBuf::from(prefix)
                    .join("bin")
                    .join("clang.exe")
                    .into_os_string(),
            );
        }

        candidates.push(OsString::from(r"C:\tools\LLVM\bin\clang.exe"));

        candidates.push(OsString::from(r"C:\Program Files\LLVM\bin\clang.exe"));
    }

    for candidate in candidates {
        let result = Command::new(&candidate)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();

        if let Ok(status) = result {
            if status.success() {
                return Ok(candidate);
            }
        }
    }

    bail!(
        "không tìm thấy clang; thêm LLVM bin vào PATH \
         hoặc đặt biến ECMORA_CLANG, ví dụ:\n\
         $env:ECMORA_CLANG = \
         'C:\\Program Files\\LLVM\\bin\\clang.exe'"
    );
}
