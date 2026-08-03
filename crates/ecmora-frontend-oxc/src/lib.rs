use std::path::Path;
mod lower;
use anyhow::{Context, Result, bail};
use ecmora_hir::Program as HirProgram;
use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_span::SourceType;

pub fn lower_source(path: &Path, source_text: &str) -> Result<HirProgram> {
    let source_type = SourceType::from_path(path)
        .with_context(|| format!("không xác định được loại source: {}", path.display()))?;

    let allocator = Allocator::default();

    let result = Parser::new(&allocator, source_text, source_type).parse();

    if result.panicked {
        bail!("Oxc parser không thể parse {}", path.display());
    }

    if !result.diagnostics.is_empty() {
        let diagnostics = result
            .diagnostics
            .iter()
            .map(|diagnostic| format!("{diagnostic:#?}"))
            .collect::<Vec<_>>()
            .join("\n");

        bail!("parse {} thất bại:\n{}", path.display(), diagnostics);
    }

    let hir = lower::lower_program(&result.program)?;

    Ok(hir)
}

pub fn dump_ast(path: &Path, source_text: &str) -> Result<String> {
    let allocator = Allocator::default();

    let source_type = SourceType::from_path(path)
        .with_context(|| format!("không xác định được loại source: {}", path.display()))?;

    let result = Parser::new(&allocator, source_text, source_type).parse();

    if result.panicked {
        bail!("Oxc parser panicked khi parse {}", path.display());
    }

    if !result.diagnostics.is_empty() {
        let diagnostics = result
            .diagnostics
            .into_iter()
            .map(|diagnostic| {
                let diagnostic = diagnostic.with_source_code(source_text.to_owned());

                format!("{diagnostic:?}")
            })
            .collect::<Vec<_>>()
            .join("\n");

        bail!("không thể parse {}:\n{}", path.display(), diagnostics);
    }

    Ok(format!("{:#?}", result.program))
}
