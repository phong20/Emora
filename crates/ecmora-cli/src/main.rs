use std::{env, path::PathBuf};

use anyhow::{Result, bail};

fn main() -> Result<()> {
    let arguments = env::args_os().skip(1).collect::<Vec<_>>();

    match arguments.as_slice() {
        [command, source] if command.as_os_str() == "run" => {
            ecmora_driver::run_file(&PathBuf::from(source))
        }

        [command, source] if command.as_os_str() == "check" => {
            ecmora_driver::check_file(&PathBuf::from(source))
        }

        [command, source] if command.as_os_str() == "dump-ast" => {
            let output = ecmora_driver::dump_ast_file(&PathBuf::from(source))?;

            println!("AST written: {}", output.display());

            Ok(())
        }

        [command, source] if command.as_os_str() == "dump-hir" => {
            let output = ecmora_driver::dump_hir_file(&PathBuf::from(source))?;

            println!("HIR written: {}", output.display());

            Ok(())
        }

        [command, source] if command.as_os_str() == "dump-ssa" => {
            let output = ecmora_driver::dump_ssa_file(&PathBuf::from(source))?;

            println!("SSA written: {}", output.display());

            Ok(())
        }

        [command, source] if command.as_os_str() == "dump-llvm" => {
            let output = ecmora_driver::dump_llvm_file(&PathBuf::from(source))?;

            println!("LLVM IR written: {}", output.display());

            Ok(())
        }

        [command, source] if command.as_os_str() == "build" => {
            let output = ecmora_driver::build_file(&PathBuf::from(source))?;

            println!("Executable written: {}", output.display());

            Ok(())
        }

        _ => bail!(
            "cách dùng:\n\
             \tecmora run <file.js>\n\
             \tecmora check <file.js>\n\
             \tecmora dump-ast <file.js>\n\
             \tecmora dump-hir <file.js>\n\
             \tecmora dump-ssa <file.js>\n\
             \tecmora dump-llvm <file.js>\n\
             \tecmora build <file.js>"
        ),
    }
}
