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
    let hir = lower_hir_from_file(path)?;

    ecmora_runtime::execute(&hir)
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
/// source → AST → HIR → SSA → LLVM IR → clang → exe
pub fn build_file(path: &Path) -> Result<PathBuf> {
    ecmora_native_host::ensure_linked();
    match lower_ssa_from_file(path) {
        Ok(ssa) => match build_ssa_file(path, &ssa) {
            Ok(executable) => Ok(executable),
            Err(reason) => {
                eprintln!(
                    "LLVM native backend chưa phủ SSA này; dùng compatibility executable: {reason:#}"
                );
                build_compatibility_file(path)
            }
        },
        Err(reason) => {
            eprintln!(
                "native SSA chưa phủ chương trình này; dùng compatibility executable: {reason:#}"
            );
            build_compatibility_file(path)
        }
    }
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

fn build_compatibility_file(path: &Path) -> Result<PathBuf> {
    let source = read_source(path)?;
    let wrapper_path = artifact_path(path, "compat.c")?;
    let embedded_name = format!(
        "embedded.{}",
        path.extension()
            .and_then(|extension| extension.to_str())
            .unwrap_or("js")
    );
    let embedded_name = embedded_name.replace('\\', "\\\\").replace('"', "\\\"");
    let source_bytes = source
        .as_bytes()
        .iter()
        .map(|byte| format!("0x{byte:02x}"))
        .collect::<Vec<_>>()
        .join(",");
    let wrapper = format!(
        "#include <stddef.h>\n\
         extern int ecmora_execute_source(const char *, const unsigned char *, size_t);\n\
         static const unsigned char source[] = {{{source_bytes}}};\n\
         int main(void) {{ return ecmora_execute_source(\"{embedded_name}\", source, sizeof(source)); }}\n"
    );
    fs::write(&wrapper_path, wrapper)
        .with_context(|| format!("không thể ghi {}", wrapper_path.display()))?;

    let executable_path = executable_artifact_path(path)?;
    let clang = find_clang()?;
    let executable = env::current_exe().context("không tìm được executable ecmora hiện tại")?;
    let target_directory = executable
        .parent()
        .context("executable ecmora không có parent directory")?;
    let workspace_manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("Cargo.toml");
    let mut cargo = Command::new("cargo");
    cargo.args([
        "build",
        "-p",
        "ecmora-native-host",
        "--offline",
        "--manifest-path",
    ]);
    cargo.arg(&workspace_manifest);
    if target_directory
        .file_name()
        .is_some_and(|name| name == "release")
    {
        cargo.arg("--release");
    }
    let status = cargo
        .status()
        .context("không thể cập nhật compatibility static library")?;
    if !status.success() {
        bail!("cargo build ecmora-native-host thất bại")
    }
    let static_library = target_directory.join(if cfg!(windows) {
        "ecmora_native_host.lib"
    } else {
        "libecmora_native_host.a"
    });
    if !static_library.exists() {
        bail!(
            "thiếu compatibility static library {}; chạy `cargo build -p ecmora-native-host`",
            static_library.display()
        )
    }

    let mut command = Command::new(&clang);
    command.arg(&wrapper_path).arg(&static_library);
    if cfg!(windows) {
        command.args([
            "-ladvapi32",
            "-lbcrypt",
            "-lkernel32",
            "-lntdll",
            "-lole32",
            "-lshell32",
            "-luserenv",
            "-lws2_32",
        ]);
    }
    let output = command
        .arg("-o")
        .arg(&executable_path)
        .output()
        .with_context(|| format!("không thể link compatibility executable bằng {:?}", clang))?;
    if !output.status.success() {
        bail!(
            "link compatibility executable thất bại\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        )
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
