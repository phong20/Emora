use anyhow::Result;

/// Minimal optimization entry point. Passes are intentionally a no-op until
/// the IR has more than one useful instruction class.
pub fn optimize(program: &mut ecmora_ir::Program) -> Result<()> {
    // Keep optimizer boundaries canonical even after future passes start
    // rewriting CFG. Verification remains strict after canonicalization.
    ecmora_ir::canonicalize_cfg(program)?;
    ecmora_ir::verify_program(program)
}
