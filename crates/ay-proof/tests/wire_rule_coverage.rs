// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External coverage for every Alethe rule name AY can emit.

#![allow(clippy::print_stderr)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[path = "wire_rule_coverage/placeholder_inventory.rs"]
mod placeholder_inventory;

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

/// Lex string literals from Rust source, ignoring comments and character
/// literals. Both ordinary and raw strings are included because either may be
/// used as a printer format string.
fn rust_string_literals(source: &str) -> Vec<RustStringLiteral> {
    let bytes = source.as_bytes();
    let mut strings = Vec::new();
    let mut index = 0;
    let mut line = 1;
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
                    strings.push(RustStringLiteral {
                        value,
                        line: literal_line,
                    });
                    index = terminator_end;
                    break;
                }
                end = quote + 1;
            }
            continue;
        }
        if bytes[index] != b'"' {
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
        strings.push(RustStringLiteral {
            value,
            line: literal_line,
        });
    }
    strings
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

/// Enumerate the values feeding each dynamic `:rule {placeholder}` site.
///
/// Placeholder roles are deliberately fail-closed. Adding a new dynamic site
/// or role makes the test fail until its producer is mechanically connected to
/// this inventory; a fixed `:rule name` needs no such routing.
fn dynamic_printer_rule_candidates(
    main_source: &str,
    symm_source: &str,
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
    let start = symm_source
        .find("let wire_rule =")
        .expect("surface symmetry wire-rule selector must exist");
    let selector = &symm_source[start..];
    let end = selector
        .find(';')
        .expect("surface symmetry wire-rule selector must end with a semicolon");
    let selector_line = symm_source[..start]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count();
    let selector_rules = rust_string_literals(&selector[..end]);
    assert_eq!(selector_rules.len(), 2, "surface symmetry has two rules");
    for mut literal in selector_rules {
        literal.line += selector_line;
        add_dynamic_candidate(&mut candidates, &literal, "surface symmetry rule");
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
        } else if path.extension().is_some_and(|extension| extension == "rs")
            && !path
                .file_stem()
                .is_some_and(|stem| stem.to_string_lossy().ends_with("_tests"))
        {
            paths.insert(path);
        }
    }
}

fn printer_source_paths() -> Vec<PathBuf> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source_dir = manifest.join("src");
    let mut paths = BTreeSet::new();
    let entries = std::fs::read_dir(&source_dir)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", source_dir.display()));
    for entry in entries {
        let path = entry.expect("read printer module directory entry").path();
        let is_production_printer_file = path.is_file()
            && path.extension().is_some_and(|extension| extension == "rs")
            && path.file_stem().is_some_and(|stem| {
                let stem = stem.to_string_lossy();
                (stem == "alethe_printer" || stem.starts_with("alethe_printer_"))
                    && !stem.ends_with("_tests")
            });
        if is_production_printer_file {
            paths.insert(path);
        }
    }
    add_rust_files(&source_dir.join("alethe_printer"), &mut paths);
    paths.into_iter().collect()
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
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    for path in printer_source_paths() {
        let relative = path.strip_prefix(manifest).unwrap_or(&path);
        let source = source_file(&path);
        match relative.to_string_lossy().as_ref() {
            "src/alethe_printer.rs" => main_printer_source = Some(source.clone()),
            "src/alethe_printer/surface_symm.rs" => surface_symm_source = Some(source.clone()),
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
    );
    for (candidate, sources) in printer_candidates {
        if !inventory.sources.contains_key(&candidate) {
            inventory.printer_dynamic_candidates += 1;
            for source in sources {
                inventory.add(&candidate, source);
            }
        }
    }
    inventory
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
         {} fixed printer literals + {} dynamic printer candidates = {} distinct names",
        inventory.pass_throughs,
        inventory.alias_targets,
        inventory.printer_literals,
        inventory.printer_dynamic_candidates,
        inventory.sources.len()
    );

    let mut unknown = Vec::new();
    for (rule, sources) in &inventory.sources {
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
