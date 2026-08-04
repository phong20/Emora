#!/usr/bin/env python3
"""Materialize and modularize the ecmora-analysis source tree.

The recursion work was initially shipped as build-time textual patches because
GitHub-only editing could not safely replace a multi-thousand-line Rust file.
This tool consumes Cargo's already generated source once, turns it into normal
checked-in Rust modules, removes the analysis build script/base source, and
removes analysis-only replacements from the shared patch specification.

Run from the repository root:

    py -3 tools/refactor_analysis.py

The operation is transactional with respect to the files it changes: if
`cargo fmt` or `cargo check -p ecmora-analysis` fails, the original files are
restored.
"""

from __future__ import annotations

import argparse
import re
import shutil
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
IR_PATCH_MARKER = 'ir = "crates/ecmora-ir/src/lib.rs"'

REQUIRED_GENERATED_MARKERS = (
    "specialization_counts: HashMap",
    "fn resolve_callback_argument(",
    "Terminator::TailCallDirect",
    "function_return_hint: Option<ValueType>",
)

PUBLIC_SUPPORT_FUNCTIONS = (
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


def run(command: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(command))
    return subprocess.run(
        command,
        cwd=ROOT,
        check=check,
        text=True,
    )


def latest_generated_source() -> Path | None:
    candidates = list(
        (ROOT / "target").glob(
            "**/out/ecmora_analysis_generated.rs"
        )
    )
    if not candidates:
        return None
    return max(candidates, key=lambda path: path.stat().st_mtime_ns)


def ensure_generated_source() -> Path:
    generated = latest_generated_source()
    if generated is not None:
        return generated

    print("No generated analysis source found; building it once first.")
    run(["cargo", "check", "-p", "ecmora-analysis"])
    generated = latest_generated_source()
    if generated is None:
        raise SystemExit(
            "cargo completed but ecmora_analysis_generated.rs was not found"
        )
    return generated


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise ValueError(
            f"{label}: expected exactly one match, found {count}\n"
            f"--- expected ---\n{old[:800]}"
        )
    return text.replace(old, new, 1)


def extract_function(text: str, name: str) -> tuple[str, str]:
    """Remove one top-level Rust function and return (remaining, function)."""
    match = re.search(rf"(?m)^fn {re.escape(name)}\s*\(", text)
    if match is None:
        raise ValueError(f"top-level function `{name}` not found")

    start = match.start()
    # Preserve immediately preceding doc/comments and attributes belonging to
    # the function, but stop at a blank line after a prior item.
    line_start = start
    while line_start > 0:
        previous_end = line_start - 1
        previous_start = text.rfind("\n", 0, previous_end) + 1
        previous = text[previous_start:previous_end].strip()
        if previous.startswith(("///", "//", "#[")):
            line_start = previous_start
            continue
        break
    start = line_start

    brace = text.find("{", match.end())
    if brace < 0:
        raise ValueError(f"function `{name}` has no body")

    end = scan_balanced_braces(text, brace)
    while end < len(text) and text[end] in " \t":
        end += 1
    if end < len(text) and text[end] == "\n":
        end += 1
    if end < len(text) and text[end] == "\n":
        end += 1

    function = text[start:end].rstrip() + "\n"
    remaining = text[:start].rstrip() + "\n\n" + text[end:].lstrip()
    return remaining, function


def scan_balanced_braces(text: str, opening: int) -> int:
    depth = 0
    index = opening
    state = "code"
    raw_hashes = 0

    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""

        if state == "code":
            if char == "/" and next_char == "/":
                state = "line_comment"
                index += 2
                continue
            if char == "/" and next_char == "*":
                state = "block_comment"
                depth_comment = 1
                index += 2
                while index < len(text) and depth_comment:
                    pair = text[index : index + 2]
                    if pair == "/*":
                        depth_comment += 1
                        index += 2
                    elif pair == "*/":
                        depth_comment -= 1
                        index += 2
                    else:
                        index += 1
                continue
            if char == "\"":
                state = "string"
                index += 1
                continue
            if char == "'":
                # Rust lifetimes are common. Treat as a char only when a closing
                # quote appears within the next few bytes.
                closing = text.find("'", index + 1, min(len(text), index + 8))
                if closing != -1:
                    state = "char"
                    index += 1
                    continue
            if char == "r":
                raw = re.match(r'r(#+)?"', text[index:])
                if raw:
                    raw_hashes = len(raw.group(1) or "")
                    state = "raw_string"
                    index += raw.end()
                    continue
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    return index + 1
            index += 1
            continue

        if state == "line_comment":
            if char == "\n":
                state = "code"
            index += 1
            continue

        if state == "string":
            if char == "\\":
                index += 2
            elif char == "\"":
                state = "code"
                index += 1
            else:
                index += 1
            continue

        if state == "char":
            if char == "\\":
                index += 2
            elif char == "'":
                state = "code"
                index += 1
            else:
                index += 1
            continue

        if state == "raw_string":
            closing = '"' + ("#" * raw_hashes)
            if text.startswith(closing, index):
                index += len(closing)
                state = "code"
            else:
                index += 1
            continue

    raise ValueError("unterminated Rust item while scanning braces")


def make_support_module(support: str) -> str:
    support = "use super::*;\n\n" + support.lstrip()

    support = replace_once(
        support,
        SUPPORT_MARKER,
        "pub(super) fn collect_free_variables(function: &HirFunction) -> HashSet<String> {\n"
        "    FreeVariableCollector::collect(function)\n"
        "}\n\n"
        + SUPPORT_MARKER,
        "free-variable facade",
    )

    for name in PUBLIC_SUPPORT_FUNCTIONS:
        support = replace_once(
            support,
            f"fn {name}(",
            f"pub(super) fn {name}(",
            f"support visibility for {name}",
        )

    return support.rstrip() + "\n"


def make_specialization_module(callback_function: str) -> str:
    callback_function = callback_function.replace(
        "fn callback_specialization_fingerprint(",
        "pub(super) fn callback_specialization_fingerprint(",
        1,
    )
    return f'''use super::ClosureBinding;
use ecmora_ir::ValueType;
use std::hash::{{Hash, Hasher}};

pub(super) const MAX_SPECIALIZATIONS_PER_FUNCTION: usize = 64;

/// Stable, typed identity for a native function specialization.
///
/// Keeping this as a struct avoids accidental key collisions and makes it
/// straightforward to add object shapes, calling conventions, or guard sets
/// without rewriting string formatting at every call site.
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

{callback_function.rstrip()}

#[cfg(test)]
mod tests {{
    use super::*;

    #[test]
    fn return_seed_is_part_of_specialization_identity() {{
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


def materialize(source: str) -> tuple[str, str, str]:
    source = source.replace("\r\n", "\n")
    missing = [marker for marker in REQUIRED_GENERATED_MARKERS if marker not in source]
    if missing:
        raise ValueError(
            "generated source does not contain the completed recursion work: "
            + ", ".join(missing)
        )

    marker_index = source.find(SUPPORT_MARKER)
    if marker_index < 0:
        raise ValueError("support-section marker was not found")

    core = source[:marker_index].rstrip() + "\n"
    support = source[marker_index:]

    support, callback_function = extract_function(
        support, "callback_specialization_fingerprint"
    )
    support = make_support_module(support)
    specialization = make_specialization_module(callback_function)

    core = replace_once(
        core,
        """use std::{
    collections::{HashMap, HashSet, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
};""",
        """use std::collections::{HashMap, HashSet};

mod specialization;
mod support;

use specialization::*;
use support::*;""",
        "module declarations/import cleanup",
    )

    core = replace_once(
        core,
        "    specializations: HashMap<String, (String, ValueType)>,",
        "    specializations: HashMap<SpecializationKey, (String, ValueType)>,",
        "completed specialization map type",
    )
    core = replace_once(
        core,
        "    active_specializations: HashMap<String, ActiveSpecialization>,",
        "    active_specializations: HashMap<SpecializationKey, ActiveSpecialization>,",
        "active specialization map type",
    )

    core = replace_once(
        core,
        "let free_names = FreeVariableCollector::collect(function);",
        "let free_names = collect_free_variables(function);",
        "free-variable facade use",
    )

    core = replace_once(
        core,
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

    core = replace_once(
        core,
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

    core = replace_once(
        core,
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

    core = replace_once(
        core,
        "        const MAX_SPECIALIZATIONS_PER_FUNCTION: usize = 64;\n",
        "",
        "centralized specialization budget",
    )

    return core.rstrip() + "\n", support, specialization


def slim_patchspec(text: str) -> str:
    text = text.replace("\r\n", "\n")
    index = text.find(IR_PATCH_MARKER)
    if index < 0:
        raise ValueError("IR patch marker not found in patch specification")
    remaining = text[index:].lstrip()
    return (
        "# Build-time source patches retained only for IR/codegen migration.\n"
        "# ecmora-analysis now uses normal checked-in Rust modules.\n\n"
        + remaining.rstrip()
        + "\n"
    )


def snapshot(paths: Iterable[Path]) -> list[Snapshot]:
    result = []
    for path in paths:
        result.append(
            Snapshot(
                path=path,
                existed=path.exists(),
                content=path.read_bytes() if path.exists() else None,
            )
        )
    return result


def restore(snapshots: Iterable[Snapshot]) -> None:
    for item in snapshots:
        if item.existed:
            item.path.parent.mkdir(parents=True, exist_ok=True)
            assert item.content is not None
            item.path.write_bytes(item.content)
        elif item.path.exists():
            item.path.unlink()


def write_refactor(
    core: str,
    support: str,
    specialization: str,
    patchspec: str,
) -> None:
    SRC.mkdir(parents=True, exist_ok=True)
    LIB.write_text(core, encoding="utf-8", newline="\n")
    SUPPORT.write_text(support, encoding="utf-8", newline="\n")
    SPECIALIZATION.write_text(specialization, encoding="utf-8", newline="\n")
    PATCHSPEC.write_text(patchspec, encoding="utf-8", newline="\n")
    if BUILD_RS.exists():
        BUILD_RS.unlink()
    if BASE.exists():
        BASE.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="validate and show the planned files without changing them",
    )
    parser.add_argument(
        "--no-check",
        action="store_true",
        help="skip cargo fmt/check after materialization",
    )
    args = parser.parse_args()

    if not ANALYSIS.exists() or not PATCHSPEC.exists():
        raise SystemExit("run this tool from an Ecmora repository checkout")

    already_materialized = (
        not BUILD_RS.exists()
        and not BASE.exists()
        and SUPPORT.exists()
        and SPECIALIZATION.exists()
        and "mod specialization;" in LIB.read_text(encoding="utf-8")
    )
    if already_materialized:
        print("ecmora-analysis is already materialized and modularized.")
        return 0

    generated = ensure_generated_source()
    print(f"Using generated source: {generated.relative_to(ROOT)}")
    generated_source = generated.read_text(encoding="utf-8")
    core, support, specialization = materialize(generated_source)
    patchspec = slim_patchspec(PATCHSPEC.read_text(encoding="utf-8"))

    changed_paths = [
        LIB,
        SUPPORT,
        SPECIALIZATION,
        PATCHSPEC,
        BUILD_RS,
        BASE,
    ]

    if args.dry_run:
        print("Validated successfully. Planned changes:")
        for path in changed_paths:
            action = "delete" if path in (BUILD_RS, BASE) else "write"
            print(f"  {action:6} {path.relative_to(ROOT)}")
        return 0

    snapshots = snapshot(changed_paths)
    try:
        write_refactor(core, support, specialization, patchspec)
        if not args.no_check:
            run(["cargo", "fmt", "-p", "ecmora-analysis"])
            run(["cargo", "check", "-p", "ecmora-analysis"])
    except Exception:
        print("Refactor validation failed; restoring original files.", file=sys.stderr)
        restore(snapshots)
        raise

    print("\necmora-analysis now uses normal checked-in modules:")
    print("  crates/ecmora-analysis/src/lib.rs")
    print("  crates/ecmora-analysis/src/support.rs")
    print("  crates/ecmora-analysis/src/specialization.rs")
    print("\nRemoved analysis-only build indirection:")
    print("  crates/ecmora-analysis/build.rs")
    print("  crates/ecmora-analysis/src/lib_base.rs")
    print("\nReview and commit with:")
    print("  git status --short")
    print("  git diff --stat")
    print("  git add crates/ecmora-analysis tools/recursive_specialization.patchspec")
    print('  git commit -m "refactor: modularize analysis lowering"')
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
