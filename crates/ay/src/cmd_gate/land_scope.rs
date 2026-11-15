// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rust token changes and the CLI's declared module ownership.

use super::process::Runner;
use anyhow::Result;
use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

#[derive(Default)]
pub(super) struct RustScope {
    pub(super) retired_tooling: BTreeSet<PathBuf>,
    pub(super) unchanged: BTreeSet<PathBuf>,
    pub(super) narrowed_package_recipe: bool,
    pub(super) base_workspace_manifest: Option<String>,
    pub(super) base_paths: Option<BTreeSet<PathBuf>>,
    pub(super) cli_modules: BTreeMap<PathBuf, String>,
    pub(super) production_modules: BTreeSet<String>,
    pub(super) module_lists: BTreeSet<PathBuf>,
    pub(super) module_changes: BTreeMap<PathBuf, BTreeSet<String>>,
}

impl RustScope {
    pub(super) fn read(runner: &mut Runner, base: &str, paths: &[PathBuf]) -> Result<Self> {
        let mut scope = Self::default();
        if paths.iter().any(|path| path == Path::new("Cargo.toml")) {
            let old = runner.git(&["show", &format!("{base}:Cargo.toml")])?;
            let new = std::fs::read_to_string(runner.root.join("Cargo.toml"))?;
            scope.narrowed_package_recipe = only_narrows_package_bins(&old, &new);
            scope.base_workspace_manifest = Some(old);
            let paths = runner.git_bytes(&["ls-tree", "-r", "--name-only", "-z", base])?;
            scope.base_paths = Some(
                paths
                    .split(|byte| *byte == 0)
                    .filter(|path| !path.is_empty())
                    .map(|path| std::str::from_utf8(path).map(PathBuf::from))
                    .collect::<std::result::Result<_, _>>()?,
            );
        }
        let modified = runner.git_bytes(&[
            "diff",
            "--diff-filter=M",
            "--name-only",
            "-z",
            base,
            "HEAD",
            "--",
            "*.rs",
        ])?;
        let modified: BTreeSet<_> = modified.split(|b| *b == 0).collect();
        for path in paths {
            let Some(name) = path.to_str() else { continue };
            if !modified.contains(name.as_bytes()) {
                continue;
            }
            let old = runner.git(&["show", &format!("{base}:{name}")])?;
            let new = std::fs::read_to_string(runner.root.join(path))?;
            if module_list_only(&old) && module_list_only(&new) {
                let absolute = runner.root.join(path);
                scope.module_lists.insert(absolute.clone());
                scope
                    .module_changes
                    .insert(absolute, changed_modules(&old, &new));
            }
            if same_tokens(&old, &new) {
                scope.unchanged.insert(path.clone());
            }
        }
        let main = runner.root.join("crates/ay/src/main.rs");
        if let Ok(source) = std::fs::read_to_string(main) {
            if let Some(modules) = declared_modules(&source) {
                for (name, path, test_only) in modules {
                    scope
                        .cli_modules
                        .insert(Path::new("src").join(path), name.clone());
                    if !test_only {
                        scope.production_modules.insert(name);
                    }
                }
            }
        }
        Ok(scope)
    }

    pub(super) fn cli_module(&self, relative: &Path) -> Option<&str> {
        self.cli_modules.iter().find_map(|(path, name)| {
            (relative == path || relative.starts_with(path.with_extension("")))
                .then_some(name.as_str())
        })
    }
}

/// A package recipe can narrow Cargo's default binary roots without changing
/// workspace compilation inputs. Keep the existing CLI build for the changed
/// workspace provenance stamp; this does not qualify a new package artifact.
pub(super) fn only_narrows_package_bins(old: &str, new: &str) -> bool {
    fn recipe(manifest: &mut toml::Value) -> Option<(Vec<String>, BTreeSet<String>)> {
        let atpkg = manifest
            .get_mut("workspace")?
            .get_mut("metadata")?
            .get_mut("atpkg")?
            .as_table_mut()?;
        let mut declared = BTreeSet::new();
        for key in ["expose", "bundle"] {
            if let Some(values) = atpkg.get(key) {
                for value in values.as_array()? {
                    declared.insert(value.as_str()?.to_string());
                }
            }
        }
        let args = atpkg
            .remove("build-args")?
            .as_array()?
            .iter()
            .map(|value| value.as_str().map(str::to_owned))
            .collect::<Option<Vec<_>>>()?;
        Some((args, declared))
    }
    fn split(args: &[String]) -> Option<(Vec<&str>, BTreeSet<&str>)> {
        let mut rest = Vec::new();
        let mut bins = BTreeSet::new();
        let mut args = args.iter();
        while let Some(arg) = args.next() {
            let bin = if arg == "--bin" {
                Some(args.next()?.as_str())
            } else {
                arg.strip_prefix("--bin=")
            };
            if let Some(bin) = bin {
                if bin.is_empty() || bin.starts_with('-') {
                    return None;
                }
                bins.insert(bin);
            } else {
                if matches!(
                    arg.as_str(),
                    "--" | "--bins"
                        | "--lib"
                        | "--all-targets"
                        | "--tests"
                        | "--test"
                        | "--examples"
                        | "--example"
                        | "--benches"
                        | "--bench"
                ) || ["--test=", "--example=", "--bench="]
                    .iter()
                    .any(|prefix| arg.starts_with(*prefix))
                {
                    return None;
                }
                rest.push(arg.as_str());
            }
        }
        Some((rest, bins))
    }
    let parsed = || -> Option<bool> {
        let mut old: toml::Value = old.parse().ok()?;
        let mut new: toml::Value = new.parse().ok()?;
        let (old_args, _) = recipe(&mut old)?;
        let (new_args, declared) = recipe(&mut new)?;
        let (old_rest, old_bins) = split(&old_args)?;
        let (new_rest, new_bins) = split(&new_args)?;
        let declared: BTreeSet<_> = declared.iter().map(String::as_str).collect();
        Some(
            old == new
                && old_rest == new_rest
                && !declared.is_empty()
                && new_bins == declared
                && (old_bins.is_empty() || old_bins.is_superset(&new_bins)),
        )
    };
    parsed() == Some(true)
}

fn same_tokens(old: &str, new: &str) -> bool {
    match (old.parse::<TokenStream>(), new.parse::<TokenStream>()) {
        (Ok(old), Ok(new)) => {
            without_docs(&old).to_string() == without_docs(&new).to_string()
                && !span_sensitive(&old)
                && !span_sensitive(&new)
        }
        _ => false,
    }
}

fn without_docs(stream: &TokenStream) -> TokenStream {
    let tokens: Vec<_> = stream.clone().into_iter().collect();
    let mut result = TokenStream::new();
    let mut index = 0;
    while index < tokens.len() {
        if matches!(&tokens[index], TokenTree::Punct(p) if p.as_char() == '#') {
            let attribute = index
                + 1
                + usize::from(
                    matches!(tokens.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '!'),
                );
            if matches!(tokens.get(attribute), Some(TokenTree::Group(g))
                if g.delimiter() == Delimiter::Bracket && matches!(g.stream().into_iter().next(), Some(TokenTree::Ident(i)) if i == "doc"))
            {
                index = attribute + 1;
                continue;
            }
        }
        result.extend([match &tokens[index] {
            TokenTree::Group(g) => {
                TokenTree::Group(Group::new(g.delimiter(), without_docs(&g.stream())))
            }
            token => token.clone(),
        }]);
        index += 1;
    }
    result
}

fn span_sensitive(stream: &TokenStream) -> bool {
    let tokens: Vec<_> = stream.clone().into_iter().collect();
    for (index, token) in tokens.iter().enumerate() {
        if matches!(token, TokenTree::Ident(name) if matches!(name.to_string().as_str(),
            "line" | "column" | "file"))
            && matches!(tokens.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '!')
        {
            return true;
        }
        if let TokenTree::Group(group) = token {
            if group.delimiter() == Delimiter::Bracket
                && index > 0
                && matches!(tokens.get(index - 1), Some(TokenTree::Punct(p)) if p.as_char() == '#')
                && !builtin_attribute(&group.stream())
            {
                return true;
            }
            if span_sensitive(&group.stream()) {
                return true;
            }
        }
    }
    false
}

fn builtin_attribute(stream: &TokenStream) -> bool {
    let mut tokens = stream.clone().into_iter();
    let Some(TokenTree::Ident(name)) = tokens.next() else {
        return false;
    };
    if name == "derive" {
        let Some(TokenTree::Group(group)) = tokens.next() else {
            return false;
        };
        return group.stream().into_iter().all(|t| !matches!(t, TokenTree::Ident(i)
            if !matches!(i.to_string().as_str(), "Clone" | "Copy" | "Debug" | "Default" | "Eq" | "PartialEq" | "Ord" | "PartialOrd" | "Hash")));
    }
    matches!(
        name.to_string().as_str(),
        "cfg"
            | "allow"
            | "warn"
            | "deny"
            | "forbid"
            | "doc"
            | "path"
            | "test"
            | "ignore"
            | "repr"
            | "inline"
            | "cold"
            | "must_use"
            | "deprecated"
            | "non_exhaustive"
    )
}

fn declared_modules(source: &str) -> Option<Vec<(String, PathBuf, bool)>> {
    let tokens: Vec<_> = source.parse::<TokenStream>().ok()?.into_iter().collect();
    let mut modules = Vec::new();
    let mut path = None;
    let mut test_only = false;
    let mut index = 0;
    while index < tokens.len() {
        if matches!(&tokens[index], TokenTree::Punct(p) if p.as_char() == '#') {
            if let Some(TokenTree::Group(group)) = tokens.get(index + 1) {
                if group.delimiter() == Delimiter::Bracket {
                    let attribute: Vec<_> = group.stream().into_iter().collect();
                    test_only |= matches!(attribute.first(), Some(TokenTree::Ident(i)) if i == "cfg")
                        && mentions_test(&group.stream());
                    if matches!(attribute.first(), Some(TokenTree::Ident(i)) if i == "path") {
                        let TokenTree::Literal(literal) = attribute.get(2)? else {
                            return None;
                        };
                        path = Some(PathBuf::from(
                            serde_json::from_str::<String>(&literal.to_string()).ok()?,
                        ));
                    }
                    index += 2;
                    continue;
                }
            }
        }
        if matches!(&tokens[index], TokenTree::Ident(i) if i == "mod") {
            if let (Some(TokenTree::Ident(name)), Some(TokenTree::Punct(end))) =
                (tokens.get(index + 1), tokens.get(index + 2))
            {
                if end.as_char() == ';' {
                    let name = name.to_string();
                    modules.push((
                        name.clone(),
                        path.take()
                            .unwrap_or_else(|| PathBuf::from(format!("{name}.rs"))),
                        test_only,
                    ));
                }
            }
        }
        if matches!(&tokens[index], TokenTree::Group(g) if g.delimiter() == Delimiter::Brace)
            || matches!(&tokens[index], TokenTree::Punct(p) if p.as_char() == ';')
        {
            path = None;
            test_only = false;
        }
        index += 1;
    }
    Some(modules)
}

pub(super) fn source_modules(source: &Path) -> Option<BTreeMap<PathBuf, String>> {
    let parent = source.parent()?;
    Some(
        declared_modules(&std::fs::read_to_string(source).ok()?)?
            .into_iter()
            .map(|(name, path, _)| (parent.join(path), name))
            .collect(),
    )
}

fn module_list_only(source: &str) -> bool {
    let Ok(stream) = source.parse::<TokenStream>() else {
        return false;
    };
    let tokens: Vec<_> = stream.into_iter().collect();
    let mut index = 0;
    while index < tokens.len() {
        if matches!(&tokens[index], TokenTree::Punct(p) if p.as_char() == '#') {
            index += 1;
            if matches!(tokens.get(index), Some(TokenTree::Punct(p)) if p.as_char() == '!') {
                index += 1;
            }
            if !matches!(tokens.get(index), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Bracket)
            {
                return false;
            }
            index += 1;
            continue;
        }
        if matches!(tokens.get(index), Some(TokenTree::Ident(i)) if i == "pub") {
            index += 1;
            if matches!(tokens.get(index), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis)
            {
                index += 1;
            }
        }
        if !matches!(tokens.get(index), Some(TokenTree::Ident(i)) if i == "mod")
            || !matches!(tokens.get(index + 1), Some(TokenTree::Ident(_)))
            || !matches!(tokens.get(index + 2), Some(TokenTree::Punct(p)) if p.as_char() == ';')
        {
            return false;
        }
        index += 3;
    }
    true
}

fn changed_modules(old: &str, new: &str) -> BTreeSet<String> {
    let (old_attributes, old_modules) = module_signatures(old);
    let (new_attributes, new_modules) = module_signatures(new);
    new_modules
        .into_iter()
        .filter_map(|(name, signature)| {
            (old_attributes != new_attributes || old_modules.get(&name) != Some(&signature))
                .then_some(name)
        })
        .collect()
}

fn module_signatures(source: &str) -> (String, BTreeMap<String, String>) {
    let Ok(stream) = source.parse::<TokenStream>() else {
        return (String::new(), BTreeMap::new());
    };
    let tokens: Vec<_> = without_docs(&stream).into_iter().collect();
    let mut attributes = TokenStream::new();
    let mut item = Vec::new();
    let mut modules = BTreeMap::new();
    let mut index = 0;
    while index < tokens.len() {
        if matches!(&tokens[index], TokenTree::Punct(p) if p.as_char() == '#')
            && matches!(tokens.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '!')
            && matches!(tokens.get(index + 2), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Bracket)
        {
            attributes.extend(tokens[index..index + 3].iter().cloned());
            index += 3;
            continue;
        }
        item.push(tokens[index].clone());
        if matches!(&tokens[index], TokenTree::Punct(p) if p.as_char() == ';') {
            if let Some(TokenTree::Ident(name)) = item.get(item.len().saturating_sub(2)) {
                modules.insert(
                    name.to_string(),
                    item.drain(..).collect::<TokenStream>().to_string(),
                );
            }
            item.clear();
        }
        index += 1;
    }
    (attributes.to_string(), modules)
}

fn mentions_test(stream: &TokenStream) -> bool {
    stream.clone().into_iter().any(|t| match t {
        TokenTree::Ident(i) => i == "test",
        TokenTree::Group(g) => mentions_test(&g.stream()),
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_comments_do_not_select_runtime_tests_but_literals_do() {
        assert!(same_tokens("fn f() { 1; } // old", "/* new */ fn f(){1;}"));
        assert!(!same_tokens("fn f(){\"// old\";}", "fn f(){\"// new\";}"));
        assert!(same_tokens("/// old\nfn f() {}", "/// new\nfn f() {}"));
        assert!(!same_tokens("fn f( {", "fn f( {"));
        assert!(!same_tokens(
            "fn f(){line!();}",
            "// shift\nfn f(){line!();}"
        ));
        assert!(!same_tokens(
            "#[derive(Custom)] struct A;",
            "// shift\n#[derive(Custom)] struct A;"
        ));
    }

    #[test]
    fn cli_ownership_uses_declared_paths_and_does_not_read_function_bodies() {
        assert!(module_list_only(
            "//! modules\n#[path=\"a.rs\"] pub(crate) mod a;"
        ));
        assert!(!module_list_only("mod a; fn helper() {}"));
        assert_eq!(
            changed_modules("mod old; mod kept;", "mod kept; mod added;"),
            BTreeSet::from(["added".into()])
        );
        assert_eq!(
            changed_modules("#[cfg(unix)] mod a;", "#[cfg(windows)] mod a;"),
            BTreeSet::from(["a".into()])
        );
        assert_eq!(
            changed_modules("mod a; mod b;", "#![cfg(unix)] mod a; mod b;"),
            BTreeSet::from(["a".into(), "b".into()])
        );
        let modules = declared_modules(
            "mod cmd_gate; #[cfg(all(test, unix))] #[path = \"main_tests.rs\"] pub(crate) mod tests; fn f(){mod hidden;}",
        )
        .unwrap();
        assert_eq!(
            modules,
            vec![
                ("cmd_gate".into(), "cmd_gate.rs".into(), false),
                ("tests".into(), "main_tests.rs".into(), true),
            ]
        );
    }
}
