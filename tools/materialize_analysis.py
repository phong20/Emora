#!/usr/bin/env python3
"""Replace ecmora-analysis build-time source patching with normal Rust modules.

The current recursion branch already produces the final analysis source under
Cargo's OUT_DIR. This one-shot migration takes that verified generated source,
checks it into `src/lib.rs`, extracts stable support/specialization modules,
removes the analysis build script/base file, and leaves the IR/codegen patches
untouched.

Run from the repository root on Windows:

    py -3 tools/materialize_analysis.py --dry-run
    py -3 tools/materialize_analysis.py

The migration snapshots every changed file. If formatting or `cargo check`
fails, all original files are restored.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
ANALYSIS = ROOT / "crates" / "ecmora-analysis"
SRC = ANALYSIS / "src"
LIB = SRC / "lib.rs"
BASE = SRC / "lib_base.rs"
BUILD_RS = ANALYSIS / "build.rs"
SUPPORT = SRC / "support.rs"
SPECIALIZATION = SRC / "specialization.rs"
PATCHSPEC = ROOT / "tools" / "recursive_specialization.patchspec"

SUPPORT_MARKER = "#[derive(Debug, Default)]\nstruct FreeVariableCollector"
CALLBACK_START = "fn callback_specialization_fingerprint("
CALLBACK_END = "fn sanitize_function_name("
IR_PATCH_MARKER = 'ir = "crates/ecmora-ir/src/lib.rs"'

REQUIRED_GENERATED_MARKERS = (
    "specialization_counts: HashMap",
    "fn resolve_callback_argument(",
    "Terminator::TailCallDirect",
    "function_return_hint: Option<ValueType>",
)

SUPPORT_API = (
    "infer_function_return_type",
    "infer_expression_type_hint",
    "type_of",
    "to_sem_unary",
    "to_sem_binary",
    "number_operator",
    "number_operator_for_sem",
    "compare_operator",
    "assignment_binary",
    "sanitize_function_name",
    "collect_used_names",
    "is_pure_expression_known",
)


@dataclass
class Snapshot:
    path: Path
    existed: bool
    content: bytes | None


def run(command: list[str]) -> None:
    print("+", " ".join(command))
    subprocess.run(command, cwd=ROOT, check=True)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise ValueError(
            f"{label}: expected exactly one match, found {count}\n"
            f"--- expected ---\n{old[:700]}"
        )
    return text.replace(old, new, 1)


def newest_generated_source() -> Path | None:
    candidates = list(
        (ROOT / "target").glob("**/out/ecmora_analysis_generated.rs")
    )
    return max(candidates, key=lambda path: path.stat().st_mtime_ns) if candidates else None


def ensure_generated_source() -> Path:
    generated = newest_generated_source()
    if generated is not None:
        return generated

    print("No generated analysis source found; building it once first.")
    run(["cargo", "check", "-p", "ecmora-analysis"])
    generated = newest_generated_source()
    if generated is None:
        raise RuntimeError("Cargo did not produce ecmora_analysis_generated.rs")
    return generated


def extract_callback_fingerprint(support: str) -> tuple[str, str]:
    start = support.find(CALLBACK_START)
    end = support.find(CALLBACK_END, start + 1)
    if start < 0 or end < 0:
        raise ValueError("callback fingerprint boundaries were not found")

    callback = support[start:end].strip()
    remaining = support[:start].rstrip() + "\n\n" + support[end:].lstrip()
    return remaining, callback


def build_support_module(source: str) -> str:
    source = "use super::*;\n\n" + source.lstrip()
    source = replace_once(
        source,
        SUPPORT_MARKER,
        "pub(super) fn collect_free_variables(function: &HirFunction) -> HashSet<String> {\n"
        "    FreeVariableCollector::collect(function)\n"
        "}\n\n"
        + SUPPORT_MARKER,
        "free-variable facade",
    )
    for function in SUPPORT_API:
        source = replace_once(
            source,
            f"fn {function}(",
            f"pub(super) fn {function}(",
            f"support visibility for {function}",
        )
    return source.rstrip() + "\n"


def build_specialization_module(callback: str) -> str:
    callback = replace_once(
        callback,
        CALLBACK_START,
        "pub(super) fn callback_specialization_fingerprint(",
        "callback fingerprint visibility",
    )
    return f'''use super::ClosureBinding;
use ecmora_ir::ValueType;
use std::{{
    collections::hash_map::DefaultHasher,
    hash::{{Hash, Hasher}},
}};

pub(super) const MAX_SPECIALIZATIONS_PER_FUNCTION: usize = 64;

/// Typed identity of one native function specialization.
///
/// New dimensions such as object shapes, calling conventions, or guard sets
/// belong here instead of being appended to ad-hoc formatted strings.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct SpecializationKey {{
    function: String,
    parameter_types: Vec<ValueType>,
    captures: Vec<(String, ValueType)>,
    callbacks: Vec<(String, u64)>,
    return_seed: ValueType,
}}

impl SpecializationKey {{
    pub(super) fn new(
        function: &str,
        parameter_types: Vec<ValueType>,
        captures: Vec<(String, ValueType)>,
        callbacks: Vec<(String, u64)>,
        return_seed: ValueType,
    ) -> Self {{
        Self {{
            function: function.to_owned(),
            parameter_types,
            captures,
            callbacks,
            return_seed,
        }}
    }}
}}

{callback}

#[cfg(test)]
mod tests {{
    use super::*;

    #[test]
    fn return_seed_changes_specialization_identity() {{
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
    }}
}}
'''


def build_core_module(source: str) -> str:
    source = replace_once(
        source,
        """use std::{
    collections::{HashMap, HashSet, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
};""",
        """use std::collections::{HashMap, HashSet};

mod specialization;
mod support;

use specialization::*;
use support::*;""",
        "analysis module imports",
    )
    source = replace_once(
        source,
        "    specializations: HashMap<String, (String, ValueType)>,",
        "    specializations: HashMap<SpecializationKey, (String, ValueType)>,",
        "completed specialization table",
    )
    source = replace_once(
        source,
        "    active_specializations: HashMap<String, ActiveSpecialization>,",
        "    active_specializations: HashMap<SpecializationKey, ActiveSpecialization>,",
        "active specialization table",
    )
    source = replace_once(
        source,
        "let free_names = FreeVariableCollector::collect(function);",
        "let free_names = collect_free_variables(function);",
        "free-variable facade call",
    )
    source = replace_once(
        source,
        """        let capture_signature = captures
            .iter()
            .map(|capture| {
                (
                    capture.name.as_str(),
                    capture.value_type,
                )
            })
            .collect::<Vec<_>>();""",
        """        let capture_signature = captures
            .iter()
            .map(|capture| (capture.name.clone(), capture.value_type))
            .collect::<Vec<_>>();""",
        "owned capture signature",
    )
    source = replace_once(
        source,
        """                (
                    parameter.as_str(),
                    callback_specialization_fingerprint(&callbacks[parameter]),
                )""",
        """                (
                    parameter.clone(),
                    callback_specialization_fingerprint(&callbacks[parameter]),
                )""",
        "owned callback signature",
    )
    source = replace_once(
        source,
        """        let specialization_key = format!(
            "{}::{:?}::{capture_signature:?}::{callback_signature:?}::{return_seed:?}",
            name,
            parameters
                .iter()
                .map(|(_, value_type)| *value_type)
                .collect::<Vec<_>>(),
        );""",
        """        let specialization_key = SpecializationKey::new(
            name,
            parameters
                .iter()
                .map(|(_, value_type)| *value_type)
                .collect(),
            capture_signature,
            callback_signature,
            return_seed,
        );""",
        "typed specialization key",
    )
    source = replace_once(
        source,
        "        const MAX_SPECIALIZATIONS_PER_FUNCTION: usize = 64;\n",
        "",
        "central specialization budget",
    )
    return source.rstrip() + "\n"


def materialize(generated: str) -> tuple[str, str, str]:
    generated = generated.replace("\r\n", "\n")
    missing = [marker for marker in REQUIRED_GENERATED_MARKERS if marker not in generated]
    if missing:
        raise ValueError(
            "generated source is missing completed recursion features: "
            + ", ".join(missing)
        )

    split = generated.find(SUPPORT_MARKER)
    if split < 0:
        raise ValueError("analysis support-section marker was not found")

    core = generated[:split].rstrip() + "\n"
    support = generated[split:]
    support, callback = extract_callback_fingerprint(support)

    return (
        build_core_module(core),
        build_support_module(support),
        build_specialization_module(callback),
    )


def trim_analysis_patches(text: str) -> str:
    text = text.replace("\r\n", "\n")
    start = text.find(IR_PATCH_MARKER)
    if start < 0:
        raise ValueError("IR patch marker was not found in patchspec")
    return (
        "# Build-time source patches retained only for IR/codegen migration.\n"
        "# ecmora-analysis now uses checked-in Rust modules.\n\n"
        + text[start:].lstrip().rstrip()
        + "\n"
    )


def snapshots(paths: Iterable[Path]) -> list[Snapshot]:
    return [
        Snapshot(path, path.exists(), path.read_bytes() if path.exists() else None)
        for path in paths
    ]


def restore(items: Iterable[Snapshot]) -> None:
    for item in items:
        if item.existed:
            item.path.parent.mkdir(parents=True, exist_ok=True)
            assert item.content is not None
            item.path.write_bytes(item.content)
        elif item.path.exists():
            item.path.unlink()


def write_files(core: str, support: str, specialization: str, patchspec: str) -> None:
    LIB.write_text(core, encoding="utf-8", newline="\n")
    SUPPORT.write_text(support, encoding="utf-8", newline="\n")
    SPECIALIZATION.write_text(specialization, encoding="utf-8", newline="\n")
    PATCHSPEC.write_text(patchspec, encoding="utf-8", newline="\n")
    BUILD_RS.unlink(missing_ok=True)
    BASE.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--no-check", action="store_true")
    args = parser.parse_args()

    if not ANALYSIS.exists() or not PATCHSPEC.exists():
        raise SystemExit("run from an Ecmora repository checkout")

    already_done = (
        not BUILD_RS.exists()
        and not BASE.exists()
        and SUPPORT.exists()
        and SPECIALIZATION.exists()
        and "mod specialization;" in LIB.read_text(encoding="utf-8")
    )
    if already_done:
        print("ecmora-analysis is already materialized.")
        return 0

    generated_path = ensure_generated_source()
    print(f"Using: {generated_path.relative_to(ROOT)}")
    core, support, specialization = materialize(
        generated_path.read_text(encoding="utf-8")
    )
    patchspec = trim_analysis_patches(PATCHSPEC.read_text(encoding="utf-8"))

    affected = [LIB, SUPPORT, SPECIALIZATION, PATCHSPEC, BUILD_RS, BASE]
    if args.dry_run:
        print("Validation passed. Planned changes:")
        for path in affected:
            action = "delete" if path in (BUILD_RS, BASE) else "write"
            print(f"  {action:6} {path.relative_to(ROOT)}")
        return 0

    saved = snapshots(affected)
    try:
        write_files(core, support, specialization, patchspec)
        if not args.no_check:
            run(["cargo", "fmt", "-p", "ecmora-analysis"])
            run(["cargo", "check", "-p", "ecmora-analysis"])
            run(["cargo", "test", "-p", "ecmora-analysis"])
    except Exception:
        print("Migration failed; restoring original files.", file=sys.stderr)
        restore(saved)
        raise

    print("\nAnalysis source is now checked in and modular:")
    print("  crates/ecmora-analysis/src/lib.rs")
    print("  crates/ecmora-analysis/src/support.rs")
    print("  crates/ecmora-analysis/src/specialization.rs")
    print("\nRemoved:")
    print("  crates/ecmora-analysis/build.rs")
    print("  crates/ecmora-analysis/src/lib_base.rs")
    print("\nNext:")
    print("  git status --short")
    print("  git diff --stat")
    print("  git add crates/ecmora-analysis tools/recursive_specialization.patchspec")
    print('  git commit -m "refactor: modularize analysis lowering"')
    print("  git push")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
