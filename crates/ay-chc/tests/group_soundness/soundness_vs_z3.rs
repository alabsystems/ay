// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_chc::{testing, ChcParser, PdrConfig, PortfolioConfig, PortfolioResult};
use ntest::timeout;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

#[derive(Debug, Clone, PartialEq, Eq)]
enum RawResult {
    Sat,
    Unsat,
    Unknown,
    Error(String),
}

impl RawResult {
    fn from_token(s: &str) -> Self {
        match s.trim().to_ascii_lowercase().as_str() {
            "sat" => Self::Sat,
            "unsat" => Self::Unsat,
            "unknown" => Self::Unknown,
            other => {
                if other.contains("error") {
                    Self::Error(other.to_string())
                } else {
                    Self::Unknown
                }
            }
        }
    }

    fn from_z3_output(stdout: &str, stderr: &str) -> Self {
        for line in stdout.lines() {
            let token = line.trim();
            if token.is_empty() {
                continue;
            }
            let parsed = Self::from_token(token);
            if parsed != Self::Unknown {
                return parsed;
            }
        }

        if !stderr.trim().is_empty() {
            return Self::Error(stderr.trim().to_string());
        }

        Self::Unknown
    }
}

/// Quote an SMT-LIB symbol if it contains special characters.
/// SMT-LIB symbols can contain: letters, digits, ~!@$%^&*_+-=<>.?/
/// Symbols with other characters (like ' or space) need |...| quoting.
fn quote_symbol(s: &str) -> String {
    let needs_quoting = s.chars().any(|c| {
        !matches!(c,
            'a'..='z' | 'A'..='Z' | '0'..='9' |
            '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' |
            '=' | '<' | '>' | '.' | '?' | '/'
        )
    });
    if needs_quoting {
        format!("|{s}|")
    } else {
        s.to_string()
    }
}

/// Escape all symbols in an SMT2 expression that contain special characters.
/// Replaces unquoted symbols like `x'` with `|x'|`.
fn escape_symbols_in_expr(expr: &str, symbols: &[(String, String)]) -> String {
    let mut result = expr.to_string();
    for (sym, _) in symbols {
        let quoted = quote_symbol(sym);
        if quoted != *sym {
            // Replace all occurrences of the unquoted symbol with quoted version
            // Be careful to only replace whole symbols, not parts of other symbols
            // Simple approach: replace with space boundaries
            result = result.replace(&format!("({sym} "), &format!("({quoted} "));
            result = result.replace(&format!(" {sym})"), &format!(" {quoted})"));
            result = result.replace(&format!(" {sym} "), &format!(" {quoted} "));
        }
    }
    result
}

/// Translate mu-Z syntax to standard SMT-LIB HORN format.
/// mu-Z uses: declare-rel, declare-var, rule, query
/// Standard uses: declare-fun, forall, assert, check-sat
///
/// Returns (translated_smt2, is_muz_syntax)
fn translate_muz_to_standard(smt2: &str) -> Option<String> {
    let mut has_muz = false;
    let mut decl_vars: Vec<(String, String)> = Vec::new(); // (name, sort)
    let mut decl_rels: Vec<(String, Vec<String>)> = Vec::new(); // (name, [sorts])
    let mut rules: Vec<String> = Vec::new(); // rule bodies
    let mut query: Option<String> = None;

    // Parse mu-Z constructs
    for line in smt2.lines() {
        let code = line.split(';').next().unwrap_or("").trim();
        if code.is_empty() {
            continue;
        }

        // declare-rel: (declare-rel Name (Sort1 Sort2 ...))
        if code.starts_with("(declare-rel ") {
            has_muz = true;
            if let Some(rest) = code.strip_prefix("(declare-rel ") {
                let rest = rest.trim_end_matches(')');
                let parts: Vec<&str> = rest.splitn(2, char::is_whitespace).collect();
                if !parts.is_empty() {
                    let name = parts[0].trim().to_string();
                    let sorts_str = parts.get(1).unwrap_or(&"()").trim();
                    // Parse (Sort1 Sort2 ...)
                    let sorts_inner = sorts_str.trim_matches(|c| c == '(' || c == ')');
                    let sorts: Vec<String> = if sorts_inner.is_empty() {
                        vec![]
                    } else {
                        sorts_inner.split_whitespace().map(String::from).collect()
                    };
                    decl_rels.push((name, sorts));
                }
            }
            continue;
        }

        // declare-var: (declare-var name Sort)
        if code.starts_with("(declare-var ") {
            has_muz = true;
            if let Some(rest) = code.strip_prefix("(declare-var ") {
                let rest = rest.trim_end_matches(')');
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() >= 2 {
                    decl_vars.push((parts[0].to_string(), parts[1].to_string()));
                }
            }
            continue;
        }

        // rule: (rule body)
        if code.starts_with("(rule ") {
            has_muz = true;
            // Extract body - everything after "(rule " and before final ")"
            let body = code
                .strip_prefix("(rule ")
                .and_then(|s| s.strip_suffix(')'))
                .unwrap_or("")
                .trim();
            if !body.is_empty() {
                rules.push(body.to_string());
            }
            continue;
        }

        // query: (query body)
        if code.starts_with("(query ") {
            has_muz = true;
            let body = code
                .strip_prefix("(query ")
                .and_then(|s| s.strip_suffix(')'))
                .unwrap_or("")
                .trim();
            if !body.is_empty() {
                query = Some(body.to_string());
            }
            continue;
        }
    }

    if !has_muz {
        return None; // Not mu-Z syntax
    }

    // Generate standard SMT-LIB HORN
    let mut output = String::new();
    output.push_str("(set-logic HORN)\n");

    // declare-fun for predicates
    for (name, sorts) in &decl_rels {
        output.push_str(&format!(
            "(declare-fun {} ({}) Bool)\n",
            quote_symbol(name),
            sorts.join(" ")
        ));
    }

    // Build forall variable list (with escaped symbols)
    let var_list: String = decl_vars
        .iter()
        .map(|(n, s)| format!("({} {})", quote_symbol(n), s))
        .collect::<Vec<_>>()
        .join(" ");

    // Convert rules to assert forall (with escaped symbols in body)
    for rule_body in &rules {
        let escaped_body = escape_symbols_in_expr(rule_body, &decl_vars);
        output.push_str(&format!("(assert (forall ({var_list}) {escaped_body}))\n"));
    }

    // Convert query to assert forall (... => false) (with escaped symbols)
    if let Some(q) = query {
        let escaped_q = escape_symbols_in_expr(&q, &decl_vars);
        output.push_str(&format!(
            "(assert (forall ({var_list}) (=> {escaped_q} false)))\n"
        ));
    }

    output.push_str("(check-sat)\n");

    Some(output)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Z3Mode {
    /// `check-sat` output: `sat` = Safe, `unsat` = Unsafe
    CheckSat,
}

fn z3_mode_from_smt2(smt2: &str) -> Option<Z3Mode> {
    let mut has_check_sat = false;
    let mut has_query = false;
    let mut has_rule = false;
    let mut has_declare_rel = false;

    for line in smt2.lines() {
        let code = line.split(';').next().unwrap_or("");
        if code.contains("(query") {
            has_query = true;
        }
        if code.contains("(rule") {
            has_rule = true;
        }
        if code.contains("(declare-rel") {
            has_declare_rel = true;
        }
        if code.contains("(check-sat") {
            has_check_sat = true;
        }
    }

    // Z3's mu-Z syntax (rule/query/declare-rel) is not compatible with standard
    // Z3 CLI invocation. Only standard SMT-LIB HORN syntax (check-sat) works.
    if has_rule || has_declare_rel || has_query {
        return None; // Skip - not standard SMT-LIB HORN
    }

    if has_check_sat {
        Some(Z3Mode::CheckSat)
    } else {
        None // No check-sat command
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Safety {
    Safe,
    Unsafe,
    Unknown,
}

fn interpret_z3(mode: Z3Mode, raw: RawResult) -> Result<Safety, String> {
    match (mode, raw) {
        (_, RawResult::Error(e)) => Err(e),
        (_, RawResult::Unknown) => Ok(Safety::Unknown),

        (Z3Mode::CheckSat, RawResult::Sat) => Ok(Safety::Safe),
        (Z3Mode::CheckSat, RawResult::Unsat) => Ok(Safety::Unsafe),
    }
}

fn run_z3(path: &Path, timeout_secs: u64) -> Result<RawResult, String> {
    const TIMEOUT_SLACK_SECS: u64 = 2;

    // Use both Z3's internal timeout and an OS-level kill timeout.
    // This avoids leaving orphaned `z3` subprocesses if Z3 wedges.
    let mut child = Command::new("z3")
        .arg(format!("-T:{timeout_secs}"))
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn z3: {e}"))?;

    let mut timed_out = false;
    let timeout = Duration::from_secs(timeout_secs + TIMEOUT_SLACK_SECS);
    let status = match child
        .wait_timeout(timeout)
        .map_err(|e| format!("failed to wait for z3: {e}"))?
    {
        Some(status) => status,
        None => {
            timed_out = true;
            let _ = child.kill();
            child
                .wait()
                .map_err(|e| format!("failed to kill z3 after timeout: {e}"))?
        }
    };

    let mut stdout_buf = Vec::new();
    if let Some(mut out) = child.stdout.take() {
        out.read_to_end(&mut stdout_buf)
            .map_err(|e| format!("failed to read z3 stdout: {e}"))?;
    }

    let mut stderr_buf = Vec::new();
    if let Some(mut err) = child.stderr.take() {
        err.read_to_end(&mut stderr_buf)
            .map_err(|e| format!("failed to read z3 stderr: {e}"))?;
    }

    if timed_out {
        return Ok(RawResult::Unknown);
    }

    let stdout = String::from_utf8_lossy(&stdout_buf);
    let stderr = String::from_utf8_lossy(&stderr_buf);

    if !status.success() && stdout.trim().is_empty() {
        return Err(stderr.trim().to_string());
    }

    Ok(RawResult::from_z3_output(&stdout, &stderr))
}

fn z3_available() -> bool {
    Command::new("z3")
        .arg("-version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

/// Run Z3 on an SMT2 string (writes to temp file)
fn run_z3_on_smt2(smt2: &str, timeout_secs: u64) -> Result<RawResult, String> {
    use std::io::Write;
    let mut temp =
        tempfile::NamedTempFile::new().map_err(|e| format!("failed to create temp file: {e}"))?;
    temp.write_all(smt2.as_bytes())
        .map_err(|e| format!("failed to write temp file: {e}"))?;
    run_z3(temp.path(), timeout_secs)
}

fn production_portfolio_config() -> PortfolioConfig {
    // Use test_default() (PDR + BMC + Kind) to reduce thread count from 12 to 3.
    // This is sufficient for soundness testing; engine-diversity is tested separately.
    PortfolioConfig::test_default().parallel_timeout(Some(Duration::from_secs(10)))
}

fn run_ay(smt2: &str) -> Result<Safety, String> {
    let problem = ChcParser::parse(smt2).map_err(|e| format!("parse error: {e}"))?;
    let solver = testing::new_portfolio_solver(problem.clone(), production_portfolio_config());
    let result = solver.solve();
    match result {
        PortfolioResult::Safe(model) => {
            // Issue #758: Verify the proof when AY returns Safe.
            // Without this verification, AY can return "Safe" without proving anything.
            let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
            if !verifier.verify_model(&model) {
                return Err("Safe result has invalid proof (model verification failed)".into());
            }
            Ok(Safety::Safe)
        }
        PortfolioResult::Unsafe(_) => Ok(Safety::Unsafe),
        PortfolioResult::Unknown => Ok(Safety::Unknown),
        PortfolioResult::NotApplicable => Ok(Safety::Unknown),
        _ => panic!("unexpected variant"),
    }
}

fn chc_example_paths() -> Vec<PathBuf> {
    let examples_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut paths: Vec<PathBuf> = fs::read_dir(&examples_dir)
        .expect("failed to read ay-chc examples dir")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "smt2"))
        .collect();
    paths.sort();
    paths
}

#[test]
#[timeout(180_000)]
fn test_chc_soundness_vs_z3_examples() {
    if !z3_available() {
        eprintln!("skipping Z3 comparison examples: z3 executable not found");
        return;
    }

    let paths = chc_example_paths();
    assert!(
        !paths.is_empty(),
        "no CHC examples found under crates/ay-chc/examples"
    );

    let mut disagreements = Vec::new();
    let mut translated = Vec::new();
    let mut ay_unknowns = Vec::new();
    let mut tested = 0;
    let mut ay_definitive = 0;

    for path in &paths {
        let smt2 = fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));

        let filename = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();

        // Try to use standard SMT-LIB HORN first, otherwise translate mu-Z
        let (z3_smt2, is_translated) = if z3_mode_from_smt2(&smt2).is_some() {
            // Standard SMT-LIB HORN - use as-is
            (smt2.clone(), false)
        } else if let Some(translated_smt2) = translate_muz_to_standard(&smt2) {
            // mu-Z syntax - translate to standard
            translated.push(filename.clone());
            (translated_smt2, true)
        } else {
            // Neither standard nor translatable mu-Z
            eprintln!("WARNING: Skipping {filename} - unsupported format");
            continue;
        };

        // Run Z3 on the (possibly translated) SMT2
        let z3_raw = if is_translated {
            run_z3_on_smt2(&z3_smt2, 5).unwrap_or_else(|e| {
                panic!("z3 failed on translated {filename}: {e}\nHint: `brew install z3`")
            })
        } else {
            run_z3(path, 5).unwrap_or_else(|e| {
                panic!(
                    "z3 failed on {}: {}\nHint: `brew install z3`",
                    path.display(),
                    e
                )
            })
        };

        let z3 = interpret_z3(Z3Mode::CheckSat, z3_raw.clone())
            .unwrap_or_else(|e| panic!("failed to interpret z3 result for {filename}: {e}"));

        // AY always uses original mu-Z syntax (it supports it natively)
        let ay =
            run_ay(&smt2).unwrap_or_else(|e| panic!("ay parse/solve failed on {filename}: {e}"));

        tested += 1;

        if ay == Safety::Unknown {
            ay_unknowns.push(filename.clone());
        } else {
            ay_definitive += 1;
        }

        // Critical soundness check: AY must never disagree with Z3 on
        // definitive results in either direction.
        if z3 == Safety::Unsafe && ay == Safety::Safe {
            disagreements.push(format!(
                "{filename}: Z3=Unsafe, AY=Safe (false Safe){}",
                if is_translated { " (translated)" } else { "" }
            ));
        }
        if z3 == Safety::Safe && ay == Safety::Unsafe {
            disagreements.push(format!(
                "{filename}: Z3=Safe, AY=Unsafe (false Unsafe){}",
                if is_translated { " (translated)" } else { "" }
            ));
        }
    }

    eprintln!(
        "Soundness test: {tested} tested, {ay_definitive} definitive AY results ({} translated from mu-Z)",
        translated.len()
    );
    if !translated.is_empty() {
        eprintln!("  Translated: {}", translated.join(", "));
    }
    if !ay_unknowns.is_empty() {
        eprintln!("  AY Unknown: {}", ay_unknowns.join(", "));
    }

    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: AY disagrees with Z3 on definitive results:\n{}",
        disagreements.join("\n")
    );

    // Guard against vacuous pass: AY must produce definitive results on at
    // least some benchmarks. If it returns Unknown on everything, this test
    // provides no soundness assurance (#3120).
    assert!(
        ay_definitive >= 5,
        "Vacuous soundness test: AY returned definitive results on only {ay_definitive}/{tested} \
         benchmarks (minimum 5 required). AY returned Unknown on: {}",
        ay_unknowns.join(", ")
    );
}

// Unit tests for translator helper functions

#[test]
fn test_quote_symbol_simple() {
    assert_eq!(quote_symbol("x"), "x");
    assert_eq!(quote_symbol("Inv"), "Inv");
    assert_eq!(quote_symbol("foo_bar"), "foo_bar");
}

#[test]
fn test_quote_symbol_needs_quoting() {
    assert_eq!(quote_symbol("x'"), "|x'|");
    assert_eq!(quote_symbol("x''"), "|x''|");
    assert_eq!(quote_symbol("foo bar"), "|foo bar|");
}

#[test]
fn test_escape_symbols_in_expr() {
    let symbols = vec![("x'".to_string(), "Int".to_string())];

    // Basic case
    let expr = "(= x' 1)";
    assert_eq!(escape_symbols_in_expr(expr, &symbols), "(= |x'| 1)");

    // Multiple occurrences
    let expr = "(and (= x' 1) (< x' 5))";
    assert_eq!(
        escape_symbols_in_expr(expr, &symbols),
        "(and (= |x'| 1) (< |x'| 5))"
    );

    // Symbol at end with closing paren
    let expr = "(Inv x')";
    assert_eq!(escape_symbols_in_expr(expr, &symbols), "(Inv |x'|)");
}

#[test]
fn test_translate_muz_to_standard_simple() {
    let muz = r#"(set-logic HORN)
(declare-rel Inv (Int))
(declare-var x Int)
(rule (=> (= x 0) (Inv x)))
(query (and (Inv x) (> x 5)))"#;

    let result = translate_muz_to_standard(muz).expect("should translate");
    assert!(result.contains("(declare-fun Inv (Int) Bool)"));
    assert!(result.contains("(assert (forall ((x Int))"));
    assert!(result.contains("(check-sat)"));
}

#[test]
fn test_translate_muz_returns_none_for_standard() {
    // Standard SMT-LIB HORN should return None (not mu-Z syntax)
    let standard = r#"(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(check-sat)"#;

    assert!(translate_muz_to_standard(standard).is_none());
}
