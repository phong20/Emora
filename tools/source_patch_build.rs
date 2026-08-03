use std::{
    collections::HashMap,
    env, fs,
    path::{Path, PathBuf},
};

fn main() {
    let package = env::var("CARGO_PKG_NAME").expect("CARGO_PKG_NAME missing");
    let (target_path, output_name) = match package.as_str() {
        "ecmora-analysis" => (
            "crates/ecmora-analysis/src/lib.rs",
            "ecmora_analysis_generated.rs",
        ),
        "ecmora-ir" => ("crates/ecmora-ir/src/lib.rs", "ecmora_ir_generated.rs"),
        "ecmora-codegen-llvm" => (
            "crates/ecmora-codegen-llvm/src/lib.rs",
            "ecmora_codegen_llvm_generated.rs",
        ),
        other => panic!("unsupported generated-source package: {other}"),
    };

    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR missing"));
    let workspace = manifest_dir
        .parent()
        .and_then(Path::parent)
        .expect("crate must be inside workspace/crates");
    let spec_path = workspace.join("tools/recursive_specialization.patchspec");
    let base_path = manifest_dir.join("src/lib_base.rs");

    println!("cargo:rerun-if-changed={}", spec_path.display());
    println!("cargo:rerun-if-changed={}", base_path.display());

    let spec = fs::read_to_string(&spec_path).expect("cannot read recursive patch specification");
    let variables = parse_assignments(&spec);
    let mut replacements = parse_replace_calls(&spec, &variables, target_path);

    // The original connector bootstrap swapped this one call-site pair while
    // preparing the branch. Ignore that malformed pair and insert the intended
    // source transformation deterministically.
    if target_path == "crates/ecmora-analysis/src/lib.rs" {
        replacements.retain(|(old, _)| {
            !old.contains("recursive function `{name}` với devirtualized callback")
        });
        replacements.push((
            r#"        if let Some(active) = self
            .active_specializations
            .get(&specialization_key)
            .cloned()
        {
            if !callbacks.is_empty() {
                bail!(
                    "recursive function `{name}` với devirtualized callback \
                    chưa được hỗ trợ"
                )
            }

            return Ok(self.emit_specialization_call(
                &active.function_name,
                active.return_type,
                &call_arguments,
                captures,
            ));
        }"#
                .to_owned(),
            r#"        if let Some(active) = self
            .active_specializations
            .get(&specialization_key)
            .cloned()
        {
            return Ok(self.emit_specialization_call(
                &active.function_name,
                active.return_type,
                &call_arguments,
                &specialization_captures,
            ));
        }"#
                .to_owned(),
        ));
    }

    let mut source = fs::read_to_string(&base_path).expect("cannot read generated-source base");
    for (old, new) in replacements {
        let count = source.match_indices(&old).count();
        assert_eq!(
            count,
            1,
            "source patch expected exactly one match, found {count}: {}",
            old.lines().next().unwrap_or("<empty>")
        );
        source = source.replacen(&old, &new, 1);
    }

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR missing"));
    fs::write(out_dir.join(output_name), source).expect("cannot write generated Rust source");
}

fn parse_assignments(source: &str) -> HashMap<String, String> {
    let bytes = source.as_bytes();
    let mut variables = HashMap::new();
    let mut offset = 0;

    while offset < bytes.len() {
        let line_start = offset;
        let line_end = source[offset..]
            .find('\n')
            .map(|relative| offset + relative)
            .unwrap_or(bytes.len());
        let line = &source[line_start..line_end];

        if !line
            .as_bytes()
            .first()
            .is_some_and(|byte| byte.is_ascii_whitespace())
        {
            let mut cursor = line_start;
            if let Some(name) = parse_identifier(source, &mut cursor) {
                skip_space(source, &mut cursor);
                if source.as_bytes().get(cursor) == Some(&b'=') {
                    cursor += 1;
                    skip_space(source, &mut cursor);
                    if source.as_bytes().get(cursor) == Some(&b'"') {
                        let value = parse_python_string(source, &mut cursor);
                        variables.insert(name, value);
                        offset = cursor;
                        while offset < bytes.len() && bytes[offset] != b'\n' {
                            offset += 1;
                        }
                        if offset < bytes.len() {
                            offset += 1;
                        }
                        continue;
                    }
                }
            }
        }

        offset = if line_end < bytes.len() {
            line_end + 1
        } else {
            bytes.len()
        };
    }

    variables
}

fn parse_replace_calls(
    source: &str,
    variables: &HashMap<String, String>,
    target_path: &str,
) -> Vec<(String, String)> {
    let bytes = source.as_bytes();
    let marker = "replace_once(";
    let mut replacements = Vec::new();
    let mut offset = 0;

    while offset < bytes.len() {
        let is_line_start = offset == 0 || bytes[offset - 1] == b'\n';
        if is_line_start && source[offset..].starts_with(marker) {
            let mut cursor = offset + marker.len();
            let path = parse_expression(source, &mut cursor, variables);
            expect_comma(source, &mut cursor);
            let old = parse_expression(source, &mut cursor, variables);
            expect_comma(source, &mut cursor);
            let new = parse_expression(source, &mut cursor, variables);
            if path == target_path {
                replacements.push((old, new));
            }
            offset = cursor;
        } else {
            offset += 1;
        }
    }

    replacements
}

fn parse_expression(
    source: &str,
    cursor: &mut usize,
    variables: &HashMap<String, String>,
) -> String {
    skip_space(source, cursor);
    match source.as_bytes().get(*cursor) {
        Some(b'"') => parse_python_string(source, cursor),
        Some(_) => {
            let name = parse_identifier(source, cursor).expect("expected patch expression");
            variables
                .get(&name)
                .unwrap_or_else(|| panic!("unknown patch variable: {name}"))
                .clone()
        }
        None => panic!("unexpected end of patch specification"),
    }
}

fn expect_comma(source: &str, cursor: &mut usize) {
    skip_space(source, cursor);
    assert_eq!(
        source.as_bytes().get(*cursor),
        Some(&b','),
        "expected comma in patch call"
    );
    *cursor += 1;
}

fn parse_identifier(source: &str, cursor: &mut usize) -> Option<String> {
    let bytes = source.as_bytes();
    let start = *cursor;
    let first = *bytes.get(start)?;
    if !(first == b'_' || first.is_ascii_alphabetic()) {
        return None;
    }
    *cursor += 1;
    while let Some(byte) = bytes.get(*cursor) {
        if *byte == b'_' || byte.is_ascii_alphanumeric() {
            *cursor += 1;
        } else {
            break;
        }
    }
    Some(source[start..*cursor].to_owned())
}

fn skip_space(source: &str, cursor: &mut usize) {
    while source
        .as_bytes()
        .get(*cursor)
        .is_some_and(|byte| byte.is_ascii_whitespace())
    {
        *cursor += 1;
    }
}

fn parse_python_string(source: &str, cursor: &mut usize) -> String {
    let bytes = source.as_bytes();
    assert_eq!(bytes.get(*cursor), Some(&b'"'));
    let triple = source
        .get(*cursor..)
        .is_some_and(|rest| rest.starts_with("\"\"\""));
    *cursor += if triple { 3 } else { 1 };

    let mut output = String::new();
    loop {
        if triple {
            if source
                .get(*cursor..)
                .is_some_and(|rest| rest.starts_with("\"\"\""))
            {
                *cursor += 3;
                break;
            }
        } else if bytes.get(*cursor) == Some(&b'"') {
            *cursor += 1;
            break;
        }

        let byte = *bytes
            .get(*cursor)
            .expect("unterminated Python string in patch specification");
        *cursor += 1;
        if byte != b'\\' {
            let ch = source[*cursor - 1..]
                .chars()
                .next()
                .expect("invalid UTF-8 boundary");
            output.push(ch);
            *cursor += ch.len_utf8() - 1;
            continue;
        }

        let escaped = *bytes
            .get(*cursor)
            .expect("dangling escape in patch specification");
        *cursor += 1;
        match escaped {
            b'\\' => output.push('\\'),
            b'"' => output.push('"'),
            b'n' => output.push('\n'),
            b'r' => output.push('\r'),
            b't' => output.push('\t'),
            b'\n' => {}
            other => output.push(other as char),
        }
    }

    output
}
