// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External coverage for every Alethe rule name AY can emit.
//!
//! Two checkers read AY's documents (`ay_proof::AletheDialect`). Every name
//! AY can emit is probed against pinned Carcara 9a352ee, the one AY's own
//! gates replay with, and must be implemented there, except the Clean-only
//! names (`ay_core::CLEAN_DIALECT_ALETHE_RULES`, today `dt_project`): those
//! are printed only in the Clean dialect, pinned Carcara must still answer
//! `unknown rule` for them (so they stay out of the pinned table), and Clean's
//! vendored Carcara (`CLEAN_BIN`) must accept a minimal certificate that uses
//! each of them and refuse its holey and wrong twins.

#![allow(clippy::print_stderr)]

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[path = "wire_rule_coverage/placeholder_inventory.rs"]
mod placeholder_inventory;
#[path = "wire_rule_coverage/respelled_operand_rules.rs"]
mod respelled_operand_rules;

static PROBE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

const PROBE_PROBLEM: &str = "(set-logic QF_UF)\n\
                             (set-info :status unsat)\n\
                             (declare-const p Bool)\n\
                             (assert p)\n\
                             (assert (not p))\n\
                             (check-sat)\n";
const UNKNOWN_RULE_DIAGNOSTIC: &str = "unknown rule";

#[derive(Debug)]
struct RuleInventory {
    sources: BTreeMap<String, BTreeSet<String>>,
    pass_throughs: usize,
    alias_targets: usize,
    printer_literals: usize,
    printer_dynamic_candidates: usize,
    rule_bounded_names: usize,
}

impl RuleInventory {
    fn add(&mut self, rule: &str, source: String) {
        assert!(
            !rule.is_empty()
                && rule
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'),
            "wire rule name is not a plain Alethe symbol: {rule:?}"
        );
        self.sources
            .entry(rule.to_string())
            .or_default()
            .insert(source);
    }
}

fn workspace_crates_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("ay-proof must live directly under the workspace crates directory")
        .to_path_buf()
}

fn source_file(path: &Path) -> String {
    std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
}

/// Pull the target spelling out of each `(internal, wire)` alias pair.
///
/// The alias table is deliberately private production state. Reading its
/// declaration here keeps the test independent of a second hand-maintained
/// export and makes a newly added alias enter the external probe immediately.
fn wire_rule_alias_targets(alethe_source: &str) -> Vec<String> {
    const DECLARATION: &str = "const WIRE_RULE_ALIASES:";
    let start = alethe_source
        .find(DECLARATION)
        .expect("WIRE_RULE_ALIASES declaration must exist");
    assert_eq!(
        alethe_source.matches(DECLARATION).count(),
        1,
        "WIRE_RULE_ALIASES declaration must be unique"
    );
    let declaration = &alethe_source[start..];
    let initializer = declaration
        .find('=')
        .map(|equals| &declaration[equals + 1..])
        .expect("WIRE_RULE_ALIASES declaration must have an initializer");
    let end = initializer
        .find(';')
        .expect("WIRE_RULE_ALIASES declaration must end with a semicolon");
    let strings = ordinary_rust_string_literals(&initializer[..=end]);
    let mut pairs = strings.chunks_exact(2);
    let targets = pairs
        .by_ref()
        .map(|pair| pair[1].clone())
        .collect::<Vec<_>>();
    assert!(
        pairs.remainder().is_empty(),
        "WIRE_RULE_ALIASES must contain (internal, wire) string pairs"
    );
    targets
}

#[derive(Debug)]
struct RustStringLiteral {
    value: String,
    line: usize,
}

fn char_literal_end(source: &str, quote: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut index = quote + 1;
    match *bytes.get(index)? {
        b'\\' => {
            index += 1;
            match *bytes.get(index)? {
                b'x' => index += 3,
                b'u' if bytes.get(index + 1) == Some(&b'{') => {
                    index += 2;
                    while *bytes.get(index)? != b'}' {
                        index += 1;
                    }
                    index += 1;
                }
                _ => index += 1,
            }
        }
        b'\n' | b'\r' | b'\'' => return None,
        _ => {
            let character = source[index..].chars().next()?;
            index += character.len_utf8();
        }
    }
    (bytes.get(index) == Some(&b'\'')).then_some(index + 1)
}

fn raw_string_open(bytes: &[u8], start: usize) -> Option<(usize, usize)> {
    let mut index = start;
    if bytes.get(index) == Some(&b'b') {
        index += 1;
    }
    if bytes.get(index) != Some(&b'r') {
        return None;
    }
    index += 1;
    let hashes_start = index;
    while bytes.get(index) == Some(&b'#') {
        index += 1;
    }
    (bytes.get(index) == Some(&b'"')).then_some((index + 1, index - hashes_start))
}

/// Locate an explicitly test-only inline module. Unknown cfg expressions are
/// kept in the conservative inventory; only `cfg(test)` licenses exclusion.
fn inline_test_module_open(source: &str, start: usize) -> Option<usize> {
    let mut tail = &source[start..];
    for token in ["#", "[", "cfg", "(", "test", ")", "]"] {
        tail = tail.trim_start().strip_prefix(token)?;
    }
    tail = strip_visibility(tail.trim_start());
    tail = tail.strip_prefix("mod")?;
    if !tail.starts_with(char::is_whitespace) {
        return None;
    }
    tail = tail.trim_start();
    let length = tail
        .char_indices()
        .take_while(|(_, ch)| ch.is_alphanumeric() || *ch == '_')
        .map(|(at, ch)| at + ch.len_utf8())
        .last()?;
    tail = tail[length..].trim_start();
    tail.starts_with('{').then_some(source.len() - tail.len())
}

/// Lex string literals from Rust source, ignoring comments and character
/// literals. Both ordinary and raw strings are included because either may be
/// used as a printer format string.
fn rust_string_literals(source: &str) -> Vec<RustStringLiteral> {
    let bytes = source.as_bytes();
    let mut strings = Vec::new();
    let mut index = 0;
    let mut line = 1;
    let mut brace_depth = 0usize;
    let mut test_module_depth = None;
    while index < bytes.len() {
        if bytes[index] == b'/' && bytes.get(index + 1) == Some(&b'/') {
            index += 2;
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
            continue;
        }
        if bytes[index] == b'/' && bytes.get(index + 1) == Some(&b'*') {
            index += 2;
            let mut depth = 1usize;
            while index < bytes.len() && depth != 0 {
                match (bytes[index], bytes.get(index + 1)) {
                    (b'/', Some(b'*')) => {
                        depth += 1;
                        index += 2;
                    }
                    (b'*', Some(b'/')) => {
                        depth -= 1;
                        index += 2;
                    }
                    (b'\n', _) => {
                        line += 1;
                        index += 1;
                    }
                    _ => index += 1,
                }
            }
            assert_eq!(depth, 0, "unterminated Rust block comment");
            continue;
        }
        if bytes[index] == b'\'' {
            if let Some(end) = char_literal_end(source, index) {
                index = end;
                continue;
            }
        }
        if let Some((content_start, hashes)) = raw_string_open(bytes, index) {
            let literal_line = line;
            let mut end = content_start;
            loop {
                let quote = source[end..]
                    .find('"')
                    .map(|offset| end + offset)
                    .expect("unterminated Rust raw string literal");
                let terminator_end = quote + 1 + hashes;
                if terminator_end <= bytes.len()
                    && bytes[quote + 1..terminator_end]
                        .iter()
                        .all(|byte| *byte == b'#')
                {
                    let value = source[content_start..quote].to_string();
                    line += value.bytes().filter(|byte| *byte == b'\n').count();
                    if test_module_depth.is_none() {
                        strings.push(RustStringLiteral {
                            value,
                            line: literal_line,
                        });
                    }
                    index = terminator_end;
                    break;
                }
                end = quote + 1;
            }
            continue;
        }
        if bytes[index] != b'"' {
            if test_module_depth.is_none() && bytes[index] == b'#' {
                if let Some(open) = inline_test_module_open(source, index) {
                    line += bytes[index..=open].iter().filter(|&&b| b == b'\n').count();
                    brace_depth += 1;
                    test_module_depth = Some(brace_depth);
                    index = open + 1;
                    continue;
                }
            }
            match bytes[index] {
                b'{' => brace_depth += 1,
                b'}' => {
                    if test_module_depth == Some(brace_depth) {
                        test_module_depth = None;
                    }
                    // This lexer also reads fragments supplied by selectors.
                    brace_depth = brace_depth.saturating_sub(1);
                }
                _ => {}
            }
            if bytes[index] == b'\n' {
                line += 1;
            }
            index += 1;
            continue;
        }
        let literal_line = line;
        index += 1;
        let mut value = String::new();
        let mut terminated = false;
        while index < bytes.len() {
            match bytes[index] {
                b'"' => {
                    index += 1;
                    terminated = true;
                    break;
                }
                b'\\' => {
                    let escaped = *bytes
                        .get(index + 1)
                        .expect("unterminated escape in Rust string literal");
                    if escaped == b'\n' {
                        line += 1;
                        index += 2;
                        while matches!(bytes.get(index), Some(b' ' | b'\t' | b'\r' | b'\n')) {
                            if bytes[index] == b'\n' {
                                line += 1;
                            }
                            index += 1;
                        }
                    } else {
                        value.push(match escaped {
                            b'n' => '\n',
                            b'r' => '\r',
                            b't' => '\t',
                            other => char::from(other),
                        });
                        index += 2;
                    }
                }
                byte => {
                    value.push(char::from(byte));
                    if byte == b'\n' {
                        line += 1;
                    }
                    index += 1;
                }
            }
        }
        assert!(terminated, "unterminated Rust string literal");
        if test_module_depth.is_none() {
            strings.push(RustStringLiteral {
                value,
                line: literal_line,
            });
        }
    }
    strings
}

#[test]
fn production_inventory_excludes_inline_test_data_and_keeps_later_emitters() {
    let source = r##"
        fn before() { emit(":rule and"); }
        #[ cfg ( test ) ]
        mod tests {
            // Neither quoted nor commented braces end this module.
            fn negative() { assert!(!document.contains(":rule trust"));
                let braces = r#"} {"#; /* } */ let close = '}'; }
        }
        fn after() { emit(":rule or"); }
        #[cfg(not(test))]
        mod production { fn retained() { emit(":rule resolution"); } }
    "##;
    let names: BTreeSet<_> = rust_string_literals(source)
        .iter()
        .flat_map(fixed_rules_in_literal)
        .map(|(name, _)| name)
        .collect();
    assert_eq!(
        names,
        BTreeSet::from(["and".into(), "or".into(), "resolution".into()])
    );
}

fn ordinary_rust_string_literals(source: &str) -> Vec<String> {
    rust_string_literals(source)
        .into_iter()
        .map(|literal| literal.value)
        .collect()
}

fn fixed_rules_in_literal(literal: &RustStringLiteral) -> Vec<(String, usize)> {
    let mut rules = Vec::new();
    let mut offset = 0;
    while let Some(relative) = literal.value[offset..].find(":rule ") {
        let marker = offset + relative;
        let name_start = marker + ":rule ".len();
        let name = literal.value[name_start..]
            .bytes()
            .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            .map(char::from)
            .collect::<String>();
        let name_len = name.len();
        if !name.is_empty() {
            let line = literal.line
                + literal.value[..marker]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count();
            // A fixed prefix immediately followed by `{` is a rule name
            // SPLICED from a fragment (`:rule bitblast_{conn}`). Reading it as
            // a literal puts a name the checker cannot resolve into the
            // inventory while hiding the real names from the scan entirely, so
            // refuse the spelling instead of probing the prefix.
            assert_ne!(
                literal.value.as_bytes().get(name_start + name_len),
                Some(&b'{'),
                "spliced :rule name at line {line}: `{name}` is a fragment, not a \
                 wire rule. Spell the complete rule name in the substituted value \
                 so the wire-rule inventory can read it."
            );
            rules.push((name, line));
        }
        offset = name_start + name_len;
    }
    rules
}

fn dynamic_rule_placeholders(literal: &RustStringLiteral) -> Vec<String> {
    let mut placeholders = Vec::new();
    let mut offset = 0;
    while let Some(relative) = literal.value[offset..].find(":rule {") {
        let name_start = offset + relative + ":rule {".len();
        let tail = &literal.value[name_start..];
        let end = tail
            .find('}')
            .expect("dynamic :rule placeholder must close");
        let name = &tail[..end];
        assert!(
            name.bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'),
            "dynamic :rule placeholder is not a simple identifier: {name:?}"
        );
        placeholders.push(name.to_string());
        offset = name_start + end + 1;
    }
    placeholders
}

fn first_string_before_semicolon_after(source: &str, marker: &str) -> Vec<RustStringLiteral> {
    let mut found = Vec::new();
    let mut offset = 0;
    while let Some(relative) = source[offset..].find(marker) {
        let start = offset + relative + marker.len();
        let tail = &source[start..];
        let end = tail
            .find(';')
            .expect("dynamic rule producer statement must end with a semicolon");
        if let Some(mut literal) = rust_string_literals(&tail[..end]).into_iter().next() {
            literal.line += source[..start]
                .bytes()
                .filter(|byte| *byte == b'\n')
                .count();
            found.push(literal);
        }
        offset = start;
    }
    found
}

fn add_dynamic_candidate(
    candidates: &mut BTreeMap<String, BTreeSet<String>>,
    literal: &RustStringLiteral,
    provenance: &str,
) {
    assert!(
        !literal.value.is_empty()
            && literal
                .value
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'),
        "dynamic printer rule is not a plain Alethe symbol: {:?}",
        literal.value
    );
    candidates
        .entry(literal.value.clone())
        .or_default()
        .insert(format!("{provenance}:{}", literal.line));
}

/// Every rule a local `let <name> = <selector>;` binding can take: the string
/// literals from `anchor` to the selector's first `;`, with their source lines.
/// `expected` pins how many the selector spells, so a rewrite that stops
/// spelling a rule as a literal fails here instead of silently dropping it
/// from the external probe.
fn local_rule_selector(
    source: &str,
    anchor: &str,
    expected: usize,
    what: &str,
) -> Vec<RustStringLiteral> {
    let start = source
        .find(anchor)
        .unwrap_or_else(|| panic!("{what} rule selector must exist"));
    let selector = &source[start..];
    let end = selector
        .find(';')
        .unwrap_or_else(|| panic!("{what} rule selector must end with a semicolon"));
    let selector_line = source[..start]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count();
    let mut rules = rust_string_literals(&selector[..end]);
    assert_eq!(
        rules.len(),
        expected,
        "{what} selector spells {expected} rules"
    );
    for literal in &mut rules {
        literal.line += selector_line;
    }
    rules
}

/// Enumerate the values feeding each dynamic `:rule {placeholder}` site.
///
/// Placeholder roles are deliberately fail-closed. Adding a new dynamic site
/// or role makes the test fail until its producer is mechanically connected to
/// this inventory; a fixed `:rule name` needs no such routing.
fn dynamic_printer_rule_candidates(
    main_source: &str,
    symm_source: &str,
    shift_source: &str,
    respelled_source: &str,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut candidates = BTreeMap::<String, BTreeSet<String>>::new();

    // `rule_name` comes from either `template("name", ...)` or the first
    // string field of `positional.push((..., "name", ...))`.
    for literal in first_string_before_semicolon_after(main_source, "template(") {
        add_dynamic_candidate(&mut candidates, &literal, "printer template rule");
    }
    for literal in first_string_before_semicolon_after(main_source, "positional.push((") {
        add_dynamic_candidate(&mut candidates, &literal, "printer positional rule");
    }

    // The idempotent BV decoder returns
    // `(operator, blast_rule, connective, simplify_rule, operand)`. Read tuple
    // fields 1 and 3 from every arm, independently of CHECKABLE_ALETHE_RULES.
    let decoder = function_body(
        main_source,
        "fn decode_idempotent_bv_gate(\n        terms: &TermStore,",
    );
    let mut decoder_arms = 0usize;
    for line in decoder.lines().filter(|line| line.contains("=> Some((")) {
        let tuple = line
            .split_once("=> Some((")
            .map(|(_, tuple)| tuple)
            .expect("filtered decoder arm contains its tuple");
        let strings = rust_string_literals(tuple);
        assert_eq!(
            strings.len(),
            4,
            "idempotent BV decoder arm must spell four string tuple fields: {line}"
        );
        add_dynamic_candidate(&mut candidates, &strings[1], "printer BV blast rule");
        add_dynamic_candidate(&mut candidates, &strings[3], "printer BV simplify rule");
        decoder_arms += 1;
    }
    assert!(decoder_arms > 0, "idempotent BV decoder has no rule arms");

    // `wire_rule` is selected by this local conditional in surface_symm.
    for literal in local_rule_selector(symm_source, "let wire_rule =", 2, "surface symmetry") {
        add_dynamic_candidate(&mut candidates, &literal, "surface symmetry rule");
    }

    // `respelled_atom.rs` (d22d4f03f) bridges each respelled operand pair with
    // `refl` or `poly_simp`; any other pair returns `None` before a step is
    // written. Those names are a closed production table,
    // `respelled_operand_rule`, and the sibling module reads that WHOLE body
    // -- brace-balanced, so the reading does not depend on how the arms are
    // spelled -- and says what the reading proves.
    for literal in respelled_operand_rules::table(respelled_source) {
        add_dynamic_candidate(&mut candidates, &literal, "printer respelled operand rule");
    }

    // The bounded E5 shift lowering prints one Alethe step per Tseitin clause
    // of its Boolean circuit and takes the rule from `CnfStep::rule`, a
    // `&'static str`. That name set is closed and readable from production:
    // every `CnfStep` is built by the single private constructor
    // `BoolCircuit::add_clause`, so reading the rule argument of each
    // `self.add_clause(...)` call enumerates it exactly, the same way the
    // idempotent BV decoder table above is read field-by-field. The rule is
    // the first string literal of the call; a call that spells it any other
    // way yields no literal and fails the count assertion below rather than
    // silently dropping a name out of the external probe.
    let add_clause_calls = shift_source.matches("self.add_clause(").count();
    assert!(
        add_clause_calls > 0,
        "bounded shift lowering has no CNF clause rules"
    );
    let shift_rules = first_string_before_semicolon_after(shift_source, "self.add_clause(");
    assert_eq!(
        shift_rules.len(),
        add_clause_calls,
        "every bounded-shift CNF clause must spell its Alethe rule as a literal"
    );
    for literal in shift_rules {
        add_dynamic_candidate(&mut candidates, &literal, "printer shift CNF rule");
    }

    candidates
}

fn add_rust_files(directory: &Path, paths: &mut BTreeSet<PathBuf>) {
    let entries = std::fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", directory.display()));
    for entry in entries {
        let path = entry.expect("read Rust source directory entry").path();
        if path.is_dir() {
            add_rust_files(&path, paths);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            paths.insert(path);
        }
    }
}

/// One `mod name;` declaration, with the attributes that precede it.
struct ModuleDeclaration {
    cfg_test: bool,
    path_attribute: Option<String>,
    name: String,
}

/// Drop a leading `pub`, `pub(crate)`, `pub(super)`, ... from a statement.
fn strip_visibility(line: &str) -> &str {
    let Some(rest) = line.strip_prefix("pub") else {
        return line;
    };
    let rest = match rest.strip_prefix('(') {
        Some(restricted) => match restricted.split_once(')') {
            Some((_, after)) => after,
            None => return line,
        },
        None => rest,
    };
    if rest.starts_with(char::is_whitespace) {
        rest.trim_start()
    } else {
        line
    }
}

/// Read the file-backed `mod` declarations of one source file.
///
/// Line oriented on purpose: this crate spells every declaration as its own
/// statement, and the alternative (a second Rust parser) is the kind of
/// machinery that goes stale silently. Inline `mod name { .. }` blocks are
/// deliberately skipped -- they back no file, so they cannot be scanned as
/// production by mistake.
fn module_declarations(source: &str) -> Vec<ModuleDeclaration> {
    let mut declarations = Vec::new();
    let mut cfg_test = false;
    let mut path_attribute = None;
    for line in source.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        if line.starts_with("#[") || line.starts_with("#![") {
            if line.contains("cfg(test)") {
                cfg_test = true;
            }
            if let Some(rest) = line.split_once("path").and_then(|(_, rest)| {
                let rest = rest.trim_start();
                rest.strip_prefix('=')
            }) {
                let rest = rest.trim_start();
                if let Some(value) = rest.strip_prefix('"').and_then(|v| v.split('"').next()) {
                    path_attribute = Some(value.to_string());
                }
            }
            continue;
        }
        let declaration = strip_visibility(line);
        if let Some(rest) = declaration.strip_prefix("mod ") {
            if let Some(name) = rest.strip_suffix(';') {
                let name = name.trim();
                if !name.is_empty()
                    && name
                        .bytes()
                        .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
                {
                    declarations.push(ModuleDeclaration {
                        cfg_test,
                        path_attribute: path_attribute.clone(),
                        name: name.to_string(),
                    });
                }
            }
        }
        cfg_test = false;
        path_attribute = None;
    }
    declarations
}

/// Resolve one `mod` declaration of `declaring` to the file that backs it.
fn module_file(declaring: &Path, declaration: &ModuleDeclaration) -> Option<PathBuf> {
    let directory = declaring.parent()?;
    if let Some(attribute) = &declaration.path_attribute {
        // `#[path]` on a file-backed module resolves against the directory the
        // declaring file lives in.
        let resolved = directory.join(attribute);
        return resolved.is_file().then_some(resolved);
    }
    let stem = declaring.file_stem()?.to_string_lossy().to_string();
    let nested = if stem == "mod" || stem == "lib" {
        directory.to_path_buf()
    } else {
        directory.join(stem)
    };
    let flat = nested.join(format!("{}.rs", declaration.name));
    if flat.is_file() {
        return Some(flat);
    }
    let folded = nested.join(&declaration.name).join("mod.rs");
    folded.is_file().then_some(folded)
}

/// Every printer source file that is TEST code, read from the declarations
/// rather than guessed from the file name.
///
/// A `*_tests.rs` suffix is this crate's convention, not a guarantee: the
/// idiomatic `#[cfg(test)] mod tests;` spelling puts a plain `tests.rs` (or a
/// `corpus.rs`) beside the production module, and eleven such files were being
/// scanned here as production. That is not cosmetic -- `707ac89b43` already
/// showed what it costs, when an inline test module contributed a literal
/// `:rule trust` taken from a NEGATIVE assertion, a name AY refuses to emit
/// and the installed carcara answers `unknown rule` for. Exclusion is
/// transitive: whatever a test module declares is test code too.
fn test_only_sources(candidates: &BTreeSet<PathBuf>) -> BTreeSet<PathBuf> {
    let mut excluded: BTreeSet<PathBuf> = candidates
        .iter()
        .filter(|path| {
            path.file_stem()
                .is_some_and(|stem| stem.to_string_lossy().ends_with("_tests"))
        })
        .cloned()
        .collect();
    let mut frontier: Vec<PathBuf> = Vec::new();
    for path in candidates {
        for declaration in module_declarations(&source_file(path)) {
            if !declaration.cfg_test {
                continue;
            }
            let backing = module_file(path, &declaration).unwrap_or_else(|| {
                panic!(
                    "`#[cfg(test)] mod {}` in {} resolves to no file; the scan cannot \
                     tell whether it is production",
                    declaration.name,
                    path.display()
                )
            });
            if excluded.insert(backing.clone()) {
                frontier.push(backing);
            }
        }
    }
    while let Some(path) = frontier.pop() {
        for declaration in module_declarations(&source_file(&path)) {
            if let Some(backing) = module_file(&path, &declaration) {
                if excluded.insert(backing.clone()) {
                    frontier.push(backing);
                }
            }
        }
    }
    excluded
}

fn printer_source_paths() -> Vec<PathBuf> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source_dir = manifest.join("src");
    let mut paths = BTreeSet::new();
    let entries = std::fs::read_dir(&source_dir)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", source_dir.display()));
    for entry in entries {
        let path = entry.expect("read printer module directory entry").path();
        let is_printer_file = path.is_file()
            && path.extension().is_some_and(|extension| extension == "rs")
            && path.file_stem().is_some_and(|stem| {
                let stem = stem.to_string_lossy();
                stem == "alethe_printer" || stem.starts_with("alethe_printer_")
            });
        if is_printer_file {
            paths.insert(path);
        }
    }
    add_rust_files(&source_dir.join("alethe_printer"), &mut paths);
    let test_only = test_only_sources(&paths);
    let production: Vec<PathBuf> = paths.difference(&test_only).cloned().collect();
    assert!(
        !production.is_empty(),
        "printer production scan excluded every source file"
    );
    production
}

fn function_body<'a>(source: &'a str, signature: &str) -> &'a str {
    assert_eq!(
        source.matches(signature).count(),
        1,
        "function signature must be unique: {signature}"
    );
    let start = source.find(signature).expect("function signature exists");
    let open = source[start..]
        .find('{')
        .map(|offset| start + offset)
        .expect("function body opens");
    let mut depth = 0usize;
    for (offset, character) in source[open..].char_indices() {
        match character {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return &source[open + 1..open + offset];
                }
            }
            _ => {}
        }
    }
    panic!("unterminated function body: {signature}");
}

fn add_production_pass_throughs(
    inventory: &mut RuleInventory,
    checkable: &BTreeSet<&str>,
    source: &str,
    signature: &str,
    provenance: &str,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for literal in rust_string_literals(function_body(source, signature)) {
        if checkable.contains(literal.value.as_str()) {
            names.insert(literal.value);
        }
    }
    for name in &names {
        inventory.add(name, provenance.to_string());
    }
    names
}

fn rule_inventory() -> RuleInventory {
    let checkable = ay_proof::checkable_rule_names()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut inventory = RuleInventory {
        sources: BTreeMap::new(),
        pass_throughs: 0,
        alias_targets: 0,
        printer_literals: 0,
        printer_dynamic_candidates: 0,
        rule_bounded_names: 0,
    };

    let core_alethe = workspace_crates_dir().join("ay-core/src/alethe.rs");
    let core_source = source_file(&core_alethe);
    let theory_kind = workspace_crates_dir().join("ay-core/src/proof/theory_lemma_kind.rs");
    let theory_source = source_file(&theory_kind);
    let mut pass_throughs = add_production_pass_throughs(
        &mut inventory,
        &checkable,
        &core_source,
        "pub fn name(&self) -> &str {",
        "CHECKABLE pass-through from AletheRule::name",
    );
    pass_throughs.extend(add_production_pass_throughs(
        &mut inventory,
        &checkable,
        &theory_source,
        "pub fn alethe_rule(&self) -> &'static str {",
        "CHECKABLE pass-through from TheoryLemmaKind::alethe_rule",
    ));
    inventory.pass_throughs = pass_throughs.len();

    // `AletheRule::Custom` has no production constructor in this workspace;
    // arbitrary downstream extension values are therefore not pass-throughs
    // "actually used" by AY. The two exhaustive built-in spelling functions
    // above are the dynamic production inputs to `wire_rule_name`.
    let alias_targets = wire_rule_alias_targets(&core_source);
    inventory.alias_targets = alias_targets.len();
    for target in alias_targets {
        inventory.add(&target, "WIRE_RULE_ALIASES target".to_string());
    }

    let mut fixed_literals = BTreeSet::new();
    let mut dynamic_placeholders = BTreeMap::<String, BTreeSet<String>>::new();
    let mut main_printer_source = None;
    let mut surface_symm_source = None;
    let mut shift_monotonicity_source = None;
    let mut respelled_atom_source = None;
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    for path in printer_source_paths() {
        let relative = path.strip_prefix(manifest).unwrap_or(&path);
        let source = source_file(&path);
        match relative.to_string_lossy().as_ref() {
            "src/alethe_printer.rs" => main_printer_source = Some(source.clone()),
            "src/alethe_printer/surface_symm.rs" => surface_symm_source = Some(source.clone()),
            "src/alethe_printer/respelled_atom.rs" => respelled_atom_source = Some(source.clone()),
            "src/alethe_printer/bv_mul_zero/shift_monotonicity.rs" => {
                shift_monotonicity_source = Some(source.clone());
            }
            _ => {}
        }
        for literal in rust_string_literals(&source) {
            for (rule, line) in fixed_rules_in_literal(&literal) {
                fixed_literals.insert(rule.clone());
                inventory.add(
                    &rule,
                    format!("printer literal {}:{line}", relative.display()),
                );
            }
            for placeholder in dynamic_rule_placeholders(&literal) {
                dynamic_placeholders
                    .entry(placeholder)
                    .or_default()
                    .insert(format!("{}:{}", relative.display(), literal.line));
            }
        }
    }
    assert!(
        !fixed_literals.is_empty(),
        "printer source scan found no literal :rule names"
    );
    inventory.printer_literals = fixed_literals.len();
    placeholder_inventory::assert_expected(&dynamic_placeholders);
    let printer_candidates = dynamic_printer_rule_candidates(
        main_printer_source
            .as_deref()
            .expect("main Alethe printer source was scanned"),
        surface_symm_source
            .as_deref()
            .expect("surface symmetry printer source was scanned"),
        shift_monotonicity_source
            .as_deref()
            .expect("bounded shift-monotonicity printer source was scanned"),
        respelled_atom_source
            .as_deref()
            .expect("respelled-atom printer source was scanned"),
    );
    for (candidate, sources) in printer_candidates {
        if !inventory.sources.contains_key(&candidate) {
            inventory.printer_dynamic_candidates += 1;
            for source in sources {
                inventory.add(&candidate, source);
            }
        }
    }

    assert_emitters_are_rule_bounded(manifest);
    for name in ay_core::CHECKABLE_ALETHE_RULES {
        if !inventory.sources.contains_key(name) {
            inventory.rule_bounded_names += 1;
        }
        inventory.add(name, "CHECKABLE_ALETHE_RULES emitter bound".to_string());
    }
    inventory
}

/// The step emitters whose wire rule is a `&str` argument, each with the
/// function that prints it.
///
/// Four lowerings added since `5d837561c` -- the packed-selector proofs
/// (`bv_packed`, ~40 files), the complete bit-blast refutation and its
/// transport, the shadowed-store array derivation and the bounded ground
/// substitution -- print `:rule {rule}` from a parameter that is spelled at
/// call sites all over their subtree, several of them SPLICED
/// (`bitblast_{gate}`, `pbblast_{op}`, `{op}_simplify`). A static scan cannot
/// read those back, and guessing at them is exactly how `cd2dff691` put a
/// name the checker cannot resolve into this inventory.
///
/// So the bound is enforced where the bytes are written instead: each of
/// these functions refuses any name outside
/// [`ay_core::CHECKABLE_ALETHE_RULES`] and leaves the honest hole, and this
/// test probes every member of that array against the installed checker. The
/// assertion below is what keeps the two halves attached: delete a guard and
/// the coverage argument fails here rather than shipping an unknown rule.
///
/// Two later writers are bounded the same way: the u128/i128
/// multiplication-overflow certificate (`mul_overflow_cert/proof.rs`,
/// `write_step`, whose names are literals spread across that subtree), and
/// the constant Skolem bridge (`constant_skolem_bridge.rs`), which writes
/// every one of its commands, the closing `sko_forall` / `sko_ex` included,
/// through `bridge_command`.
const RULE_BOUNDED_EMITTERS: &[(&str, &str)] = &[
    ("src/alethe_printer/bv_packed.rs", "fn named_step("),
    ("src/alethe_printer/shadowed_stores.rs", "fn step(&mut self"),
    (
        "src/alethe_printer/ground_substitution/derivation.rs",
        "pub fn step(&mut self",
    ),
    ("src/alethe_printer/closed_guard/emit.rs", "fn command("),
    ("src/alethe_printer/complete_blast.rs", "fn new_word("),
    ("src/alethe_printer/complete_blast.rs", "fn theory_atom("),
    (
        "src/alethe_printer/complete_blast.rs",
        "fn plan(&mut self, lits: Vec<SRef>, emit: ClauseEmit)",
    ),
    (
        "src/alethe_printer/mul_overflow_cert/proof.rs",
        "fn write_step(",
    ),
    (
        "src/alethe_printer/constant_skolem_bridge.rs",
        "fn bridge_command(",
    ),
];

const RULE_BOUND_CALL: &str = "ay_core::is_checkable_alethe_rule(";

fn assert_emitters_are_rule_bounded(manifest: &Path) {
    for (relative, signature) in RULE_BOUNDED_EMITTERS {
        let path = manifest.join(relative);
        let source = source_file(&path);
        let body = function_body(&source, signature);
        assert!(
            body.contains(RULE_BOUND_CALL),
            "{relative}: `{signature}` prints a `:rule {{rule}}` taken from a \
             parameter but no longer bounds it with `{RULE_BOUND_CALL}`. Either \
             restore the bound or connect this producer's complete rule-name set \
             to the inventory above."
        );
    }
}

fn find_carcara() -> Option<PathBuf> {
    if let Some(configured) = std::env::var_os("CARCARA_PATH") {
        let path = PathBuf::from(configured);
        if path.is_file() {
            return Some(path);
        }
        eprintln!(
            "wire-rule coverage: CARCARA_PATH={} is not a file; trying installed locations",
            path.display()
        );
    }

    if let Some(home) = std::env::var_os("HOME") {
        let installed = PathBuf::from(home).join(".cargo/bin/carcara");
        if installed.is_file() {
            return Some(installed);
        }
    }

    std::env::var_os("PATH").and_then(|path| {
        std::env::split_paths(&path)
            .map(|directory| directory.join("carcara"))
            .find(|candidate| candidate.is_file())
    })
}

fn combined_output(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn run_with_timeout(command: &mut Command, description: &str) -> Output {
    const TIMEOUT: Duration = Duration::from_secs(10);
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| panic!("failed to run {description}: {error}"));
    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_)) => {
                return child
                    .wait_with_output()
                    .unwrap_or_else(|error| panic!("failed to collect {description}: {error}"));
            }
            Ok(None) if start.elapsed() < TIMEOUT => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Ok(None) => {
                let _ = child.kill();
                let output = child.wait_with_output().unwrap_or_else(|error| {
                    panic!("failed to collect timed-out {description}: {error}")
                });
                panic!(
                    "{description} exceeded {TIMEOUT:?}: {}",
                    combined_output(&output)
                );
            }
            Err(error) => panic!("failed while waiting for {description}: {error}"),
        }
    }
}

fn carcara_version(carcara: &Path) -> String {
    let output = run_with_timeout(
        Command::new(carcara).arg("--version"),
        &format!("{} --version", carcara.display()),
    );
    assert!(
        output.status.success(),
        "{} --version failed: {}",
        carcara.display(),
        combined_output(&output)
    );
    combined_output(&output).trim().to_string()
}

struct ProbeFiles {
    directory: PathBuf,
    problem: PathBuf,
    proof: PathBuf,
}

impl ProbeFiles {
    fn create() -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock must be after the Unix epoch")
            .as_nanos();
        let sequence = PROBE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "ay-wire-rule-coverage-{}-{timestamp}-{sequence}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).unwrap_or_else(|error| {
            panic!(
                "failed to create probe directory {}: {error}",
                directory.display()
            )
        });
        let problem = directory.join("problem.smt2");
        let proof = directory.join("proof.alethe");
        std::fs::write(&problem, PROBE_PROBLEM).unwrap_or_else(|error| {
            panic!(
                "failed to write probe problem {}: {error}",
                problem.display()
            )
        });
        Self {
            directory,
            problem,
            proof,
        }
    }
}

impl Drop for ProbeFiles {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.proof);
        let _ = std::fs::remove_file(&self.problem);
        let _ = std::fs::remove_dir(&self.directory);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuleSupport {
    Implemented,
    Unknown,
}

fn probe_rule(carcara: &Path, files: &ProbeFiles, rule: &str) -> (RuleSupport, String) {
    std::fs::write(&files.proof, format!("(step t0 (cl) :rule {rule})\n")).unwrap_or_else(
        |error| {
            panic!(
                "failed to write rule probe {}: {error}",
                files.proof.display()
            )
        },
    );
    let output = run_with_timeout(
        Command::new(carcara)
            .arg("--no-color")
            .arg("check")
            .arg("--")
            .arg(&files.proof)
            .arg(&files.problem),
        &format!("{} rule probe for {rule}", carcara.display()),
    );
    let diagnostic = combined_output(&output);
    // Some implemented rules index their expected arguments before reporting
    // a structured checker error and can even panic on this deliberately bare
    // probe. That is still evidence that dispatch found the implementation.
    // Per the empirical contract under test, ONLY `unknown rule` means the
    // spelling was not resolved.
    let support = if diagnostic.contains(UNKNOWN_RULE_DIAGNOSTIC) {
        RuleSupport::Unknown
    } else {
        RuleSupport::Implemented
    };
    (support, diagnostic)
}

/// The Clean-only names the inventory found. Vocabulary disjointness is
/// checked here; actual printer dialect behavior is tested on produced proofs,
/// rather than inferred from source-file locations.
fn clean_only_names(inventory: &RuleInventory) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    for name in ay_core::CLEAN_DIALECT_ALETHE_RULES {
        assert!(
            !ay_proof::checkable_rule_names().contains(&name),
            "`{name}` is Clean-only and must stay out of the pinned table"
        );
        let Some(sources) = inventory.sources.get(name) else {
            continue;
        };
        for source in sources {
            assert!(
                source.starts_with("printer literal "),
                "Clean-only `{name}` reaches an unconditional rule source: {source}"
            );
        }
        found.insert(name.to_string());
    }
    found
}

// Actual dialect fencing is exercised by the printer/checker semantic tests
// (including bv_reconstruct and bv_offset_spines). A source-file location
// cannot establish whether a literal is guarded by the requested dialect.

/// A minimal refutation that uses one Clean-only rule, its problem, and the
/// two twins Clean must refuse: the rule replaced by `hole` (holey, never
/// `PASSED`) and a wrong conclusion over a satisfiable problem.
struct CleanOnlyFixture {
    rule: &'static str,
    problem: &'static str,
    proof: &'static str,
    wrong_problem: &'static str,
    wrong_proof: &'static str,
}

const CLEAN_ONLY_FIXTURES: [CleanOnlyFixture; 3] = [CleanOnlyFixture {
    rule: "dt_project",
    problem: "(set-logic ALL)\n\
              (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)) (other (oth Int)))))\n\
              (declare-const a Int)\n(declare-const b Int)\n\
              (assert (not (= (snd (mk a b)) b)))\n(check-sat)\n",
    proof: "(assume a0 (not (= (snd (mk a b)) b)))\n\
            (step t1 (cl (= (snd (mk a b)) b)) :rule dt_project)\n\
            (step t2 (cl) :rule resolution :premises (a0 t1))\n",
    wrong_problem: "(set-logic ALL)\n\
                    (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)) (other (oth Int)))))\n\
                    (declare-const a Int)\n(declare-const b Int)\n\
                    (assert (not (= (snd (mk a b)) a)))\n(check-sat)\n",
    wrong_proof: "(assume a0 (not (= (snd (mk a b)) a)))\n\
                  (step t1 (cl (= (snd (mk a b)) a)) :rule dt_project)\n\
                  (step t2 (cl) :rule resolution :premises (a0 t1))\n",
}, CleanOnlyFixture {
    rule: "bv_reconstruct_v1",
    problem: "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n(assert (not (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) #x04)) x)))\n(check-sat)\n",
    proof: "(assume a0 (not (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) #x04)) x)))\n(step t1 (cl (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) #x04)) x)) :rule bv_reconstruct_v1)\n(step t2 (cl) :rule resolution :premises (a0 t1))\n",
    wrong_problem: "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n(assert (not (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) #x04)) y)))\n(check-sat)\n",
    wrong_proof: "(assume a0 (not (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) #x04)) y)))\n(step t1 (cl (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) #x04)) y)) :rule bv_reconstruct_v1)\n(step t2 (cl) :rule resolution :premises (a0 t1))\n",
}, CleanOnlyFixture {
    rule: "eq_simplify_bv_offset_spines",
    problem: "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (not (= (= (bvadd (bvadd x #xff) #x01) x) true)))\n(check-sat)\n",
    proof: "(assume a0 (not (= (= (bvadd (bvadd x #xff) #x01) x) true)))\n(step t1 (cl (= (= (bvadd (bvadd x #xff) #x01) x) true)) :rule eq_simplify_bv_offset_spines)\n(step t2 (cl) :rule resolution :premises (a0 t1))\n",
    wrong_problem: "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (not (= (= (bvadd (bvadd x #xff) #x01) x) false)))\n(check-sat)\n",
    wrong_proof: "(assume a0 (not (= (= (bvadd (bvadd x #xff) #x01) x) false)))\n(step t1 (cl (= (= (bvadd (bvadd x #xff) #x01) x) false)) :rule eq_simplify_bv_offset_spines)\n(step t2 (cl) :rule resolution :premises (a0 t1))\n",
}];

#[test]
fn clean_only_fixture_problems_distinguish_valid_from_wrong_conclusions() {
    let Some(oracle) = ay_test_support::z3::optional_z3("ay-proof Clean wire fixtures") else {
        return;
    };
    let files = ProbeFiles::create();
    for fixture in &CLEAN_ONLY_FIXTURES {
        for (problem, expected) in [(fixture.problem, "unsat"), (fixture.wrong_problem, "sat")] {
            std::fs::write(&files.problem, problem).expect("write exact fixture problem");
            let output = run_with_timeout(
                oracle.command().arg("-smt2").arg(&files.problem),
                &format!(
                    "{} fixture truth for {}",
                    oracle.path().display(),
                    fixture.rule
                ),
            );
            let diagnostic = combined_output(&output);
            assert!(output.status.success(), "{diagnostic}");
            assert_eq!(
                String::from_utf8_lossy(&output.stdout).trim(),
                expected,
                "{} must have a real discriminating model/proof premise: {diagnostic}",
                fixture.rule
            );
        }
    }
}

fn clean_bin() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var_os("CLEAN_BIN")?);
    assert!(
        path.is_file(),
        "CLEAN_BIN is set but names no file: {}",
        path.display()
    );
    Some(path)
}

/// `clean cert verify-external` on one certificate: `PASSED` or not, and the
/// output. Clean prints no rule-dispatch detail ("term details omitted"), so
/// a Clean rule is probed by a certificate that must pass, not by a bare step.
fn clean_verdict(clean: &Path, files: &ProbeFiles, problem: &str, proof: &str) -> (bool, String) {
    let certificate = files.directory.join("certificate.json");
    let json = format!(
        "{{\"type\":\"alethe_certificate\",\"version\":\"1.0\",\"problem\":{},\"proof\":{}}}",
        json_string(problem),
        json_string(proof)
    );
    std::fs::write(&certificate, json).expect("write the certificate");
    let output = run_with_timeout(
        Command::new(clean)
            .args(["cert", "verify-external"])
            .arg(&certificate),
        &format!("{} cert verify-external", clean.display()),
    );
    let _ = std::fs::remove_file(&certificate);
    let diagnostic = combined_output(&output);
    (
        output.status.success() && diagnostic.contains("External certificate verification: PASSED"),
        diagnostic,
    )
}

fn json_string(text: &str) -> String {
    let mut quoted = String::from("\"");
    for character in text.chars() {
        match character {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            other => quoted.push(other),
        }
    }
    quoted.push('"');
    quoted
}

/// Clean's vendored Carcara implements every Clean-only name AY writes.
#[test]
fn clean_carcara_implements_every_clean_only_rule() {
    let inventory = rule_inventory();
    let found = clean_only_names(&inventory);
    for name in &found {
        assert!(
            CLEAN_ONLY_FIXTURES
                .iter()
                .any(|fixture| fixture.rule == name),
            "Clean-only `{name}` has no fixture certificate"
        );
    }
    let Some(clean) = clean_bin() else {
        // libtest captures eprintln on successful tests. Keep unavailable
        // external coverage visible instead of looking like a reader pass.
        let _ = writeln!(
            std::io::stderr().lock(),
            "AY-TEST-SKIP wire-rule coverage: Clean replay not run — CLEAN_BIN is not set"
        );
        return;
    };
    let files = ProbeFiles::create();
    for fixture in &CLEAN_ONLY_FIXTURES {
        let rule = fixture.rule;
        let (passed, diagnostic) = clean_verdict(&clean, &files, fixture.problem, fixture.proof);
        assert!(passed, "Clean refused its own `{rule}`:\n{diagnostic}");
        let holey = fixture
            .proof
            .replace(&format!(":rule {rule})"), ":rule hole)");
        let (passed, diagnostic) = clean_verdict(&clean, &files, fixture.problem, &holey);
        assert!(
            !passed,
            "the control is vacuous: Clean passed `hole` in place of `{rule}`:\n{diagnostic}"
        );
        let (passed, diagnostic) =
            clean_verdict(&clean, &files, fixture.wrong_problem, fixture.wrong_proof);
        assert!(
            !passed && diagnostic.contains(&format!("with rule '{rule}'")),
            "Clean must refuse a wrong `{rule}` at that step:\n{diagnostic}"
        );
        eprintln!("wire-rule coverage: Clean implements `{rule}` (fixture PASSED, twins refused)");
    }
}

#[test]
fn installed_carcara_implements_every_ay_wire_rule() {
    let Some(carcara) = find_carcara() else {
        eprintln!(
            "wire-rule coverage: SKIPPED — carcara not found via CARCARA_PATH, \
             $HOME/.cargo/bin/carcara, or PATH"
        );
        return;
    };

    let version = carcara_version(&carcara);
    let inventory = rule_inventory();
    let files = ProbeFiles::create();

    // Control the discriminator without double-probing any real inventory
    // name. If this invented name does not answer `unknown rule`, a green
    // coverage result would be vacuous.
    let (control, control_diagnostic) =
        probe_rule(&carcara, &files, "ay_wire_coverage_control_unknown_rule");
    assert_eq!(
        control,
        RuleSupport::Unknown,
        "carcara probe cannot distinguish an invented rule: {control_diagnostic}"
    );

    eprintln!("wire-rule coverage: checker = {version}");
    eprintln!(
        "wire-rule coverage: inventory = {} CHECKABLE pass-throughs + {} alias targets + \
         {} fixed printer literals + {} dynamic printer candidates + {} further \
         CHECKABLE_ALETHE_RULES members reachable through a bounded emitter = {} \
         distinct names",
        inventory.pass_throughs,
        inventory.alias_targets,
        inventory.printer_literals,
        inventory.printer_dynamic_candidates,
        inventory.rule_bounded_names,
        inventory.sources.len()
    );

    // A Clean-only name is printed only in the Clean dialect. The pinned
    // checker must still NOT implement it: if it ever does, the name belongs
    // in the pinned table instead, and this says so.
    let clean_only = clean_only_names(&inventory);
    for rule in &clean_only {
        let (support, diagnostic) = probe_rule(&carcara, &files, rule);
        assert_eq!(
            support,
            RuleSupport::Unknown,
            "the pinned checker now implements Clean-only `{rule}`; move it to \
             CHECKABLE_ALETHE_RULES after measuring its acceptance: {diagnostic}"
        );
    }
    eprintln!(
        "wire-rule coverage: {} Clean-only name(s) answer `unknown rule` in the pinned checker: {clean_only:?}",
        clean_only.len()
    );

    let mut unknown = Vec::new();
    for (rule, sources) in &inventory.sources {
        if clean_only.contains(rule) {
            continue;
        }
        let (support, diagnostic) = probe_rule(&carcara, &files, rule);
        if support == RuleSupport::Unknown {
            unknown.push((rule, sources, diagnostic));
        }
    }

    if unknown.is_empty() {
        eprintln!(
            "wire-rule coverage: PASS — probed {} distinct names once each; unknown rules = 0",
            inventory.sources.len()
        );
        return;
    }

    let mut failure = format!(
        "installed checker {version} answered `unknown rule` for {} AY wire name(s):\n",
        unknown.len()
    );
    for (rule, sources, diagnostic) in unknown {
        let source_list = sources.iter().cloned().collect::<Vec<_>>().join(", ");
        failure.push_str(&format!(
            "  {rule} [{source_list}]\n    {}\n",
            diagnostic.trim().replace('\n', "\n    ")
        ));
    }
    failure.push_str(
        "An unknown rule makes the whole Alethe document invalid. Remove the unsupported \
         pass-through/alias/literal so AY emits the checker-implemented `hole` instead.",
    );
    panic!("{failure}");
}
