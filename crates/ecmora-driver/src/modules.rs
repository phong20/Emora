use std::{
    collections::{HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result, bail};
use ecmora_hir::{
    ArrayElement, AssignmentTarget, ExportBinding, Expression, ExpressionKind, ForInit,
    ImportSpecifier, MemberProperty, ObjectEntry, ObjectProperty, Program, Statement, StatementKind,
};

pub(super) fn load_program(entry: &Path) -> Result<Program> {
    let mut loader = ModuleLoader::default();
    let entry_path = canonical_source(entry)?;
    let entry_source = fs::read_to_string(&entry_path)
        .with_context(|| format!("không đọc được {}", entry_path.display()))?;
    let entry_hir = ecmora_frontend_oxc::lower_source(&entry_path, &entry_source)?;
    let strict = entry_hir.strict;
    loader.load_parsed(&entry_path, entry_hir)?;
    Ok(Program {
        statements: loader.statements,
        strict,
        imports: Vec::new(),
        exports: Vec::new(),
        export_all: Vec::new(),
    })
}

#[derive(Default)]
struct ModuleLoader {
    next_id: usize,
    loaded: HashMap<PathBuf, HashMap<String, String>>,
    predeclared: HashMap<PathBuf, HashMap<String, String>>,
    pending: HashMap<PathBuf, PendingModule>,
    statements: Vec<Statement>,
}

struct PendingModule {
    hir: Program,
    rename: HashMap<String, String>,
}

impl ModuleLoader {
    fn load(&mut self, path: &Path) -> Result<HashMap<String, String>> {
        let path = canonical_source(path)?;
        if let Some(exports) = self.loaded.get(&path) {
            return Ok(exports.clone());
        }
        if let Some(exports) = self.predeclared.get(&path) {
            return Ok(exports.clone());
        }
        let source = fs::read_to_string(&path)
            .with_context(|| format!("không đọc được module {}", path.display()))?;
        let hir = ecmora_frontend_oxc::lower_source(&path, &source)?;
        self.load_parsed(&path, hir)
    }

    fn load_parsed(&mut self, path: &Path, hir: Program) -> Result<HashMap<String, String>> {
        if let Some(exports) = self.loaded.get(path) {
            return Ok(exports.clone());
        }
        if let Some(exports) = self.predeclared.get(path) {
            // This is the back-edge of a cycle. The export table is already
            // stable; the emitter for the outer load will finish this module.
            return Ok(exports.clone());
        }

        let id = self.next_id;
        self.next_id += 1;
        let mut rename = HashMap::new();
        for name in top_level_names(&hir.statements) {
            rename.insert(name.clone(), format!("__m{id}_{}", sanitize(&name)));
        }
        let mut provisional_exports = HashMap::new();
        for binding in &hir.exports {
            if binding.source.is_none() {
                if let Some(target) = rename.get(&binding.local) {
                    provisional_exports.insert(binding.exported.clone(), target.clone());
                }
            }
        }
        self.predeclared
            .insert(path.to_owned(), provisional_exports.clone());
        self.pending.insert(
            path.to_owned(),
            PendingModule { hir, rename },
        );
        let (imports, export_all) = {
            let pending = self.pending.get(path).unwrap();
            (pending.hir.imports.clone(), pending.hir.export_all.clone())
        };
        let mut dependencies = HashMap::<String, HashMap<String, String>>::new();
        for import in &imports {
            if dependencies.contains_key(&import.source) {
                continue;
            }
            let dependency_path = resolve_specifier(path, &import.source)?;
            dependencies.insert(import.source.clone(), self.load(&dependency_path)?);
        }

        let mut rename = self.pending.get(path).unwrap().rename.clone();
        let mut namespaces = HashMap::<String, HashMap<String, String>>::new();
        for import in &imports {
            let dependency = dependencies
                .get(&import.source)
                .expect("dependency was loaded");
            for specifier in &import.specifiers {
                match specifier {
                    ImportSpecifier::Named { imported, local } => {
                        let target = dependency.get(imported).ok_or_else(|| {
                            anyhow::anyhow!(
                                "module `{}` không export `{imported}`",
                                import.source
                            )
                        })?;
                        rename.insert(local.clone(), target.clone());
                    }
                    ImportSpecifier::Default { local } => {
                        let target = dependency.get("default").ok_or_else(|| {
                            anyhow::anyhow!("module `{}` không có default export", import.source)
                        })?;
                        rename.insert(local.clone(), target.clone());
                    }
                    ImportSpecifier::Namespace { local } => {
                        namespaces.insert(local.clone(), dependency.clone());
                    }
                }
            }
        }

        let mut hir = self.pending.remove(path).unwrap().hir;
        rename_scope(
            &mut hir.statements,
            &rename,
            &namespaces,
            true,
            &HashSet::new(),
        );
        self.statements.extend(hir.statements);

        let mut exports = HashMap::new();
        for ExportBinding {
            local,
            exported,
            source,
        } in hir.exports
        {
            let target = if let Some(source) = source {
                dependencies
                    .get(&source)
                    .and_then(|dependency| dependency.get(&local))
                    .cloned()
                    .ok_or_else(|| {
                        anyhow::anyhow!("module `{source}` không export `{local}` để re-export")
                    })?
            } else {
                rename.get(&local).cloned().unwrap_or(local)
            };
            exports.insert(exported, target);
        }
        for source in export_all {
            let dependency = dependencies
                .get(&source)
                .ok_or_else(|| anyhow::anyhow!("thiếu dependency `{source}`"))?;
            for (name, target) in dependency {
                if name != "default" {
                    exports.entry(name.clone()).or_insert_with(|| target.clone());
                }
            }
        }

        self.loaded.insert(path.to_owned(), exports.clone());
        self.predeclared.insert(path.to_owned(), exports.clone());
        Ok(exports)
    }
}

fn canonical_source(path: &Path) -> Result<PathBuf> {
    path.canonicalize()
        .with_context(|| format!("không resolve được {}", path.display()))
}

fn resolve_specifier(importer: &Path, specifier: &str) -> Result<PathBuf> {
    if !(specifier.starts_with("./") || specifier.starts_with("../")) {
        let mut directory = importer.parent();
        while let Some(parent) = directory {
            let package = parent.join("node_modules").join(specifier);
            if let Some(path) = resolve_package_entry(&package) {
                return Ok(path);
            }
            directory = parent.parent();
        }
        bail!("không resolve được package import `{specifier}`")
    }
    let base = importer.parent().context("module không có thư mục cha")?;
    let raw = base.join(specifier);
    let candidates = if raw.extension().is_some() {
        vec![raw]
    } else {
        vec![
            raw.clone(),
            raw.with_extension("js"),
            raw.with_extension("mjs"),
            raw.with_extension("cjs"),
            raw.join("index.js"),
        ]
    };
    candidates
        .into_iter()
        .find(|candidate| candidate.is_file())
        .ok_or_else(|| anyhow::anyhow!("không resolve được `{specifier}` từ {}", importer.display()))
}

fn resolve_package_entry(package: &Path) -> Option<PathBuf> {
    if package.is_file() {
        return Some(package.to_owned());
    }
    if !package.is_dir() {
        return None;
    }
    let package_json = package.join("package.json");
    if let Ok(manifest) = std::fs::read_to_string(package_json) {
        for field in ["exports", "module", "main"] {
            if let Some(value) = json_string_field(&manifest, field) {
                let candidate = package.join(value);
                if let Some(path) = resolve_package_entry(&candidate) {
                    return Some(path);
                }
            }
        }
    }
    ["index.js", "index.mjs", "index.cjs"]
        .iter()
        .map(|name| package.join(name))
        .find(|candidate| candidate.is_file())
}

fn json_string_field(manifest: &str, field: &str) -> Option<String> {
    let needle = format!("\"{field}\"");
    let start = manifest.find(&needle)? + needle.len();
    let colon = manifest[start..].find(':')? + start + 1;
    let rest = manifest[colon..].trim_start();
    let rest = rest.strip_prefix('"')?;
    let end = rest.find('"')?;
    Some(rest[..end].to_owned())
}

fn top_level_names(statements: &[Statement]) -> HashSet<String> {
    let mut names = HashSet::new();
    for statement in statements {
        match &statement.kind {
            StatementKind::VariableDeclaration { declarations, .. } => {
                names.extend(declarations.iter().map(|declaration| declaration.name.clone()));
            }
            StatementKind::FunctionDeclaration(function) => {
                if let Some(name) = &function.name {
                    names.insert(name.clone());
                }
            }
            _ => {}
        }
    }
    names
}

fn rename_scope(
    statements: &mut [Statement],
    rename: &HashMap<String, String>,
    namespaces: &HashMap<String, HashMap<String, String>>,
    top_level: bool,
    inherited_shadowed: &HashSet<String>,
) {
    let mut shadowed = inherited_shadowed.clone();
    if !top_level {
        shadowed.extend(top_level_names(statements));
    }
    for statement in statements {
        rename_statement(statement, rename, namespaces, top_level, &shadowed);
    }
}

fn rename_statement(
    statement: &mut Statement,
    rename: &HashMap<String, String>,
    namespaces: &HashMap<String, HashMap<String, String>>,
    top_level: bool,
    shadowed: &HashSet<String>,
) {
    match &mut statement.kind {
        StatementKind::Expression(value) | StatementKind::Throw(value) => {
            rename_expression(value, rename, namespaces, shadowed)
        }
        StatementKind::VariableDeclaration { declarations, .. } => {
            for declaration in declarations {
                if let Some(init) = &mut declaration.init {
                    rename_expression(init, rename, namespaces, shadowed);
                }
                if top_level {
                    if let Some(name) = rename.get(&declaration.name) {
                        declaration.name = name.clone();
                    }
                }
            }
        }
        StatementKind::Block(body) => rename_scope(body, rename, namespaces, false, shadowed),
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            rename_expression(test, rename, namespaces, shadowed);
            rename_statement(consequent, rename, namespaces, false, shadowed);
            if let Some(alternate) = alternate {
                rename_statement(alternate, rename, namespaces, false, shadowed);
            }
        }
        StatementKind::While { test, body } | StatementKind::DoWhile { body, test } => {
            rename_expression(test, rename, namespaces, shadowed);
            rename_statement(body, rename, namespaces, false, shadowed);
        }
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            if let Some(init) = init {
                match init {
                    ForInit::VariableDeclaration { declarations, .. } => {
                        for declaration in declarations {
                            if let Some(init) = &mut declaration.init {
                                rename_expression(init, rename, namespaces, shadowed);
                            }
                        }
                    }
                    ForInit::Expression(value) => rename_expression(value, rename, namespaces, shadowed),
                }
            }
            if let Some(test) = test {
                rename_expression(test, rename, namespaces, shadowed);
            }
            if let Some(update) = update {
                rename_expression(update, rename, namespaces, shadowed);
            }
            rename_statement(body, rename, namespaces, false, shadowed);
        }
        StatementKind::ForIn { right, body, .. }
        | StatementKind::ForOf { right, body, .. } => {
            rename_expression(right, rename, namespaces, shadowed);
            rename_statement(body, rename, namespaces, false, shadowed);
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            rename_expression(discriminant, rename, namespaces, shadowed);
            for case in cases {
                rename_scope(&mut case.consequent, rename, namespaces, false, shadowed);
                if let Some(test) = &mut case.test {
                    rename_expression(test, rename, namespaces, shadowed);
                }
            }
        }
        StatementKind::FunctionDeclaration(function) => {
            if top_level {
                if let Some(name) = &mut function.name {
                    if let Some(new_name) = rename.get(name) {
                        *name = new_name.clone();
                    }
                }
            }
            let mut function_shadowed = shadowed.clone();
            function_shadowed.extend(function.parameters.iter().cloned());
            rename_scope(&mut function.body, rename, namespaces, false, &function_shadowed);
        }
        StatementKind::Return(value) => {
            if let Some(value) = value {
                rename_expression(value, rename, namespaces, shadowed);
            }
        }
        StatementKind::Break | StatementKind::Continue => {}
    }
}

fn rename_expression(
    expression: &mut Expression,
    rename: &HashMap<String, String>,
    namespaces: &HashMap<String, HashMap<String, String>>,
    shadowed: &HashSet<String>,
) {
    match &mut expression.kind {
        ExpressionKind::Global(name) => {
            if let Some(exports) = namespaces.get(name) {
                expression.kind = ExpressionKind::Object(
                    exports
                        .iter()
                        .map(|(key, target)| ObjectEntry::Property(ObjectProperty {
                            key: MemberProperty::Static(key.clone()),
                            value: Expression {
                                kind: ExpressionKind::Global(target.clone()),
                                span: expression.span,
                            },
                        }))
                        .collect(),
                );
                return;
            }
            if !shadowed.contains(name) {
                if let Some(new_name) = rename.get(name) {
                    *name = new_name.clone();
                }
            }
        }
        ExpressionKind::Member { object, property } => {
            if let (ExpressionKind::Global(namespace), MemberProperty::Static(property)) =
                (&object.kind, &*property)
            {
                if let Some(target) = namespaces
                    .get(namespace)
                    .and_then(|exports| exports.get(property))
                {
                    expression.kind = ExpressionKind::Global(target.clone());
                    return;
                }
            }
            rename_expression(object, rename, namespaces, shadowed);
            if let MemberProperty::Computed(value) = property {
                rename_expression(value, rename, namespaces, shadowed);
            }
        }
        ExpressionKind::Object(entries) => {
            for entry in entries {
                match entry {
                    ObjectEntry::Property(property) => {
                        if let MemberProperty::Computed(key) = &mut property.key {
                            rename_expression(key, rename, namespaces, shadowed);
                        }
                        rename_expression(&mut property.value, rename, namespaces, shadowed);
                    }
                    ObjectEntry::Spread(value) => rename_expression(value, rename, namespaces, shadowed),
                    ObjectEntry::Accessor { get, set, .. } => {
                        if let Some(get) = get {
                            rename_expression(get, rename, namespaces, shadowed);
                        }
                        if let Some(set) = set {
                            rename_expression(set, rename, namespaces, shadowed);
                        }
                    }
                }
            }
        }
        ExpressionKind::Array(elements) => {
            for element in elements {
                match element {
                    ArrayElement::Expression(value) | ArrayElement::Spread(value) => {
                        rename_expression(value, rename, namespaces, shadowed)
                    }
                    ArrayElement::Hole => {}
                }
            }
        }
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            rename_expression(test, rename, namespaces, shadowed);
            rename_expression(consequent, rename, namespaces, shadowed);
            rename_expression(alternate, rename, namespaces, shadowed);
        }
        ExpressionKind::Unary { argument, .. } | ExpressionKind::Await(argument) => {
            rename_expression(argument, rename, namespaces, shadowed)
        }
        ExpressionKind::Binary { left, right, .. }
        | ExpressionKind::Logical { left, right, .. } => {
            rename_expression(left, rename, namespaces, shadowed);
            rename_expression(right, rename, namespaces, shadowed);
        }
        ExpressionKind::Assignment { target, value, .. } => {
            rename_target(target, rename, namespaces, shadowed);
            rename_expression(value, rename, namespaces, shadowed);
        }
        ExpressionKind::Update { target, .. } => rename_target(target, rename, namespaces, shadowed),
        ExpressionKind::Call { callee, arguments }
        | ExpressionKind::New { callee, arguments } => {
            rename_expression(callee, rename, namespaces, shadowed);
            for argument in arguments {
                rename_expression(argument, rename, namespaces, shadowed);
            }
        }
        ExpressionKind::Function(function) => {
            let mut function_shadowed = shadowed.clone();
            function_shadowed.extend(function.parameters.iter().cloned());
            rename_scope(&mut function.body, rename, namespaces, false, &function_shadowed);
        }
        ExpressionKind::String(_)
        | ExpressionKind::Number(_)
        | ExpressionKind::Bool(_)
        | ExpressionKind::Null => {}
    }
}

fn rename_target(
    target: &mut AssignmentTarget,
    rename: &HashMap<String, String>,
    namespaces: &HashMap<String, HashMap<String, String>>,
    shadowed: &HashSet<String>,
) {
    match target {
        AssignmentTarget::Identifier(name) => {
            if !shadowed.contains(name) {
                if let Some(new_name) = rename.get(name) {
                    *name = new_name.clone();
                }
            }
        }
        AssignmentTarget::Member { object, property } => {
            rename_expression(object, rename, namespaces, shadowed);
            if let MemberProperty::Computed(value) = property {
                rename_expression(value, rename, namespaces, shadowed);
            }
        }
    }
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect()
}
