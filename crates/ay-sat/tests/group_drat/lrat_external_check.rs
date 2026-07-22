// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! External LRAT proof validation tests.
//!
//! Generates LRAT proofs from AY and validates them using `lrat-check`
//! (from drat-trim suite). This catches incomplete resolution chains
//! that structural-only tests miss.
//!
//! Reference: #4092 (shrink LRAT chain gap), #4380 (feature-isolated LRAT)

use super::common::{
    cargo_binary_path, read_barrel6, read_manol_pipe_c9, require_ay_lrat_check,
    source_identity_from_parts, workspace_checker_target_dir_for_outer, BuiltWorkspaceBinary,
    PHP43_DIMACS,
};
use ay_sat::{parse_dimacs, ProofOutput, SatResult, Solver};
use ntest::timeout;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

fn keep_lrat_artifacts() -> bool {
    matches!(
        std::env::var("AY_KEEP_LRAT_ARTIFACTS").as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE")
    )
}

enum LratCheckerProgram {
    External(PathBuf),
    Exact(&'static BuiltWorkspaceBinary),
}

impl LratCheckerProgram {
    fn command(&self) -> std::process::Command {
        match self {
            Self::External(path) => std::process::Command::new(path),
            Self::Exact(binary) => binary.command(),
        }
    }
}

fn require_lrat_check() -> LratCheckerProgram {
    if let Some(path) = super::common::find_lrat_check() {
        return LratCheckerProgram::External(path);
    }

    eprintln!(
        "lrat-check not found, using immutable exact-source, build-provenance-checked ay-lrat-check"
    );
    LratCheckerProgram::Exact(require_ay_lrat_check())
}

// Checker-consuming tests use a 600-second outer budget because any one of
// them can be the first caller in a fresh checkout and therefore own the
// isolated `cargo build --locked --offline`. Their solve/check assertions
// normally finish far below that cold-build ceiling.

/// PHP(3,2): 6 vars, 9 clauses.
const PHP32_DIMACS: &str = "\
p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0
";

fn stress_formula_dimacs() -> String {
    if cfg!(debug_assertions) {
        PHP43_DIMACS.to_owned()
    } else {
        read_barrel6().unwrap_or_else(|| PHP43_DIMACS.to_owned())
    }
}

/// Small random 3-SAT formula (known UNSAT).
const RANDOM_3SAT_DIMACS: &str = "\
p cnf 8 34
1 2 3 0
-1 2 3 0
1 -2 3 0
1 2 -3 0
-1 -2 3 0
-1 2 -3 0
1 -2 -3 0
-1 -2 -3 0
4 5 6 0
-4 5 6 0
4 -5 6 0
4 5 -6 0
-4 -5 6 0
-4 5 -6 0
4 -5 -6 0
-4 -5 -6 0
1 4 7 0
-1 -4 7 0
2 5 8 0
-2 -5 8 0
3 6 7 0
-3 -6 8 0
1 5 8 0
-1 6 7 0
2 4 8 0
-2 -4 -8 0
3 -5 7 0
-3 5 -7 0
1 -6 8 0
-1 6 -8 0
2 -4 7 0
-2 4 -7 0
7 8 1 0
-7 -8 -1 0
";

/// PHP(4,2): 4 pigeons, 2 holes — guaranteed UNSAT.
const PHP42_MUTEX_DIMACS: &str = "\
p cnf 8 16
1 2 0
3 4 0
5 6 0
7 8 0
-1 -3 0
-1 -5 0
-1 -7 0
-3 -5 0
-3 -7 0
-5 -7 0
-2 -4 0
-2 -6 0
-2 -8 0
-4 -6 0
-4 -8 0
-6 -8 0
";

// ============================================================================
// External LRAT validation tests
// ============================================================================

/// PHP(3,2): 3 pigeons, 2 holes — simple UNSAT, no shrink
#[test]
#[timeout(600_000)]
fn test_lrat_external_php32_no_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP32_DIMACS,
        |s| s.set_shrink_enabled(false),
        &lrat_check,
        "php32_no_shrink",
    );
}

/// PHP(3,2) with shrink enabled — tests shrink LRAT chain (#4092)
#[test]
#[timeout(600_000)]
fn test_lrat_external_php32_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP32_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "php32_with_shrink",
    );
}

/// PHP(4,3): larger pigeon-hole — more conflicts, more shrink opportunities
#[test]
#[timeout(600_000)]
fn test_lrat_external_php43_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "php43_with_shrink",
    );
}

/// Random 3-SAT at threshold (4.26 clause/variable ratio) — stress test
#[test]
#[timeout(600_000)]
fn test_lrat_external_random_3sat_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        RANDOM_3SAT_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "random_3sat_with_shrink",
    );
}

/// Regression for #9068: unit replacement LRAT chains must use the exact
/// signed proof of each removed literal's negation.
#[test]
#[timeout(30_000)]
fn test_lrat_random_3sat_50_213_s12345_bundled_checker() {
    let cnf_path =
        super::common::workspace_root().join("benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf");
    let dimacs = std::fs::read_to_string(&cnf_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", cnf_path.display(), e));
    let formula = parse_dimacs(&dimacs).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "random_3sat_50_213_s12345 must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");
    validate_lrat_proof_with_bundled_checker(&dimacs, &proof, "random_3sat_50_213_s12345");

    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("291 -27 ") && line.contains(" 287 ")),
        "proof must not contain the #9067 wrong-polarity clause 291 shape"
    );
    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("322 -6 ") && line.contains(" 313 ")),
        "proof must not contain the #9067 wrong-polarity clause 322 shape"
    );
}

/// Mutually exclusive pairs — generates many same-level conflicts (shrink target)
#[test]
#[timeout(600_000)]
fn test_lrat_external_mutex_pairs_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP42_MUTEX_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "mutex_pairs_with_shrink",
    );
}

/// Exhaustive LRAT external verification for all UNSAT DIMACS benchmarks.
///
/// Mirrors DRAT corpus coverage in `integration.rs` but validates LRAT proof
/// artifacts with `lrat-check` for every formula in `benchmarks/sat/unsat`.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_unsat_corpus_verification() {
    let lrat_check = require_lrat_check();
    let corpus_dir = super::common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    cnf_files.sort();

    assert!(
        !cnf_files.is_empty(),
        "No .cnf files found in {}. LRAT corpus verification requires at least one benchmark.",
        corpus_dir.display()
    );

    let total = cnf_files.len();
    let mut verified = 0usize;
    for cnf_path in &cnf_files {
        let dimacs = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", cnf_path.display(), e));
        let label = cnf_path
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or("corpus_case");
        solve_and_validate_lrat_configured(
            &dimacs,
            super::common::disable_all_inprocessing,
            &lrat_check,
            &format!("lrat_corpus_{label}"),
        );
        verified += 1;
    }

    assert_eq!(
        verified, total,
        "All UNSAT corpus formulas must verify with lrat-check"
    );
    eprintln!("LRAT corpus: ALL {total}/{total} benchmarks externally verified by lrat-check");
}

/// Exhaustive LRAT external verification with the default LRAT-safe profile (#5103).
///
/// The base corpus test (`test_lrat_external_unsat_corpus_verification`) disables
/// all inprocessing, so it only validates LRAT proofs from the base CDCL engine.
/// This test runs the same corpus with default configuration. Proof-incomplete
/// transforms remain clamped by policy; LRAT-capable default transforms still
/// exercise their hint streams.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_unsat_corpus_all_features() {
    let lrat_check = require_lrat_check();
    let corpus_dir = super::common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    cnf_files.sort();

    assert!(
        !cnf_files.is_empty(),
        "No .cnf files found in {}",
        corpus_dir.display()
    );

    let total = cnf_files.len();
    let mut verified = 0usize;
    for cnf_path in &cnf_files {
        let dimacs = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", cnf_path.display(), e));
        let label = cnf_path
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or("corpus_case");
        solve_and_validate_lrat_configured(
            &dimacs,
            |_solver| {
                // Default LRAT policy: proof-incomplete transforms stay clamped.
            },
            &lrat_check,
            &format!("lrat_corpus_default_features_{label}"),
        );
        verified += 1;
    }

    assert_eq!(
        verified, total,
        "All UNSAT corpus formulas must verify with lrat-check (default LRAT profile)"
    );
    eprintln!(
        "LRAT corpus (default LRAT profile): ALL {total}/{total} benchmarks externally verified by lrat-check"
    );
}

// ============================================================================
// Feature-isolated LRAT external validation tests (#4380)
//
// Each test enables exactly one inprocessing feature (all others disabled)
// and validates the LRAT proof with lrat-check. Uses barrel6 (248 vars,
// 3729 clauses) which generates enough conflicts (>25000) to trigger all
// features at their default scheduling intervals.
//
// Mirrors the DRAT feature-isolation tests in drat_vivify_3481.rs.
// ============================================================================

/// Solve a formula with LRAT proof output and validate with lrat-check.
///
/// The `configure` closure sets up the solver (e.g., disable all inprocessing
/// then enable one feature) before clauses are added and solving begins.
fn solve_and_validate_lrat_configured(
    dimacs: &str,
    configure: impl FnOnce(&mut Solver),
    lrat_checker: &LratCheckerProgram,
    label: &str,
) -> String {
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    configure(&mut solver);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: formula must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");
    assert!(!proof.is_empty(), "{label}: LRAT proof must not be empty");
    validate_lrat_proof_text(dimacs, &proof, lrat_checker, label)
}

/// Solve a formula with binary LRAT proof output and validate with a checker.
///
/// Same as `solve_and_validate_lrat_configured` but uses binary LRAT format.
/// The `checker_path` must support binary LRAT (ay-lrat-check auto-detects;
/// external lrat-check may not support binary).
fn solve_and_validate_lrat_binary_configured(
    dimacs: &str,
    configure: impl FnOnce(&mut Solver),
    checker: &BuiltWorkspaceBinary,
    label: &str,
) -> Vec<u8> {
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::lrat_binary(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    configure(&mut solver);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: formula must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof_bytes = writer.into_vec().expect("proof flush");
    assert!(
        !proof_bytes.is_empty(),
        "{label}: binary LRAT proof must not be empty"
    );
    validate_lrat_proof_binary(dimacs, &proof_bytes, checker, label)
}

fn validate_lrat_proof_text(
    dimacs: &str,
    proof: &str,
    lrat_checker: &LratCheckerProgram,
    label: &str,
) -> String {
    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let cnf_path = std::env::temp_dir().join(format!(
        "ay_lrat_test_{}_{}.cnf",
        std::process::id(),
        run_id
    ));
    let proof_path = std::env::temp_dir().join(format!(
        "ay_lrat_test_{}_{}.lrat",
        std::process::id(),
        run_id
    ));

    std::fs::write(&cnf_path, dimacs).expect("Write CNF");
    std::fs::write(&proof_path, &proof).expect("Write LRAT proof");

    let output = lrat_checker
        .command()
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("Failed to run lrat-check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let has_warning = stdout.contains("WARNING") || stderr.contains("WARNING");
    let keep_artifacts = keep_lrat_artifacts() || has_warning;
    if keep_artifacts {
        eprintln!(
            "Preserving LRAT artifacts ({label}): cnf={} lrat={}",
            cnf_path.display(),
            proof_path.display()
        );
    } else {
        let _ = std::fs::remove_file(&cnf_path);
        let _ = std::fs::remove_file(&proof_path);
    }

    assert!(
        output.status.success() && !stdout.contains("FAILED") && !stderr.contains("FAILED"),
        "LRAT validation FAILED ({label})\n\
         cnf: {}\n\
         lrat: {}\n\
         lrat-check stdout: {}\n\
         lrat-check stderr: {}\n\
         exit code: {}\n\
         proof:\n{}",
        cnf_path.display(),
        proof_path.display(),
        stdout,
        stderr,
        output.status,
        proof
    );

    eprintln!("LRAT validation passed ({label}): {}", stdout.trim());

    proof.to_string()
}

fn validate_lrat_proof_with_bundled_checker(dimacs: &str, proof: &str, label: &str) {
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(dimacs.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: bundled checker failed to parse CNF: {e}"));
    let steps = ay_lrat_check::lrat_parser::parse_text_lrat(proof)
        .unwrap_or_else(|e| panic!("{label}: bundled checker failed to parse LRAT: {e}"));
    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);

    for (id, clause) in &cnf.clauses {
        assert!(
            checker.add_original(*id, clause),
            "{label}: bundled checker rejected original clause {id}"
        );
    }

    assert!(
        checker.verify_proof(&steps),
        "{label}: bundled checker rejected LRAT proof: {}",
        checker.stats_summary()
    );
}

/// Validate binary LRAT proof bytes using an external checker.
///
/// The checker must support binary LRAT auto-detection (e.g., ay-lrat-check).
fn validate_lrat_proof_binary(
    dimacs: &str,
    proof_bytes: &[u8],
    checker: &BuiltWorkspaceBinary,
    label: &str,
) -> Vec<u8> {
    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let cnf_path = std::env::temp_dir().join(format!(
        "ay_lrat_bin_test_{}_{}.cnf",
        std::process::id(),
        run_id
    ));
    let proof_path = std::env::temp_dir().join(format!(
        "ay_lrat_bin_test_{}_{}.lrat",
        std::process::id(),
        run_id
    ));

    std::fs::write(&cnf_path, dimacs).expect("Write CNF");
    std::fs::write(&proof_path, proof_bytes).expect("Write binary LRAT proof");

    let output = checker
        .command()
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("Failed to run checker on binary LRAT");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let keep_artifacts = keep_lrat_artifacts();
    if keep_artifacts {
        eprintln!(
            "Preserving binary LRAT artifacts ({label}): cnf={} lrat={}",
            cnf_path.display(),
            proof_path.display()
        );
    } else {
        let _ = std::fs::remove_file(&cnf_path);
        let _ = std::fs::remove_file(&proof_path);
    }

    assert!(
        output.status.success() && (stdout.contains("s VERIFIED") || stdout.contains("VERIFIED")),
        "Binary LRAT validation FAILED ({label})\n\
         cnf: {}\n\
         lrat: {}\n\
         checker stdout: {}\n\
         checker stderr: {}\n\
         exit code: {}\n\
         proof size: {} bytes",
        cnf_path.display(),
        proof_path.display(),
        stdout,
        stderr,
        output.status,
        proof_bytes.len()
    );

    eprintln!(
        "Binary LRAT validation passed ({label}, {} bytes): {}",
        proof_bytes.len(),
        stdout.trim()
    );

    proof_bytes.to_vec()
}

/// Solve with one feature enabled (all others disabled) and validate LRAT proof.
/// Uses barrel6 in release mode; PHP43 in debug mode (LRAT overhead makes
/// barrel6 exceed 180s debug timeouts). Mirrors `verify_feature_drat`.
fn verify_feature_lrat(feature_name: &str, enable: fn(&mut Solver)) {
    let cnf = stress_formula_dimacs();
    verify_feature_lrat_on_dimacs(feature_name, &cnf, enable);
}

/// Solve a DIMACS formula with one feature enabled (all others disabled) and
/// validate the LRAT proof externally.
fn verify_feature_lrat_on_dimacs(feature_name: &str, cnf: &str, enable: fn(&mut Solver)) {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        cnf,
        |solver| {
            super::common::disable_all_inprocessing(solver);
            enable(solver);
        },
        &lrat_check,
        &format!("lrat_{feature_name}_barrel6"),
    );
}

/// Baseline: bare CDCL LRAT proof on barrel6 (no inprocessing).
/// Pure CDCL on barrel6 is slow in debug mode — requires extended timeout.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_baseline_barrel6() {
    let lrat_check = require_lrat_check();
    let cnf = stress_formula_dimacs();
    solve_and_validate_lrat_configured(
        &cnf,
        super::common::disable_all_inprocessing,
        &lrat_check,
        "lrat_baseline_barrel6",
    );
}

/// LRAT proof for probing in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_probe_barrel6() {
    verify_feature_lrat("probe", |s| s.set_probe_enabled(true));
}

/// LRAT proof for BCE in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_bce_barrel6() {
    verify_feature_lrat("bce", |s| s.set_bce_enabled(true));
}

/// LRAT proof for transitive reduction in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_transred_barrel6() {
    verify_feature_lrat("transred", |s| s.set_transred_enabled(true));
}

/// LRAT proof for conditioning (GBCE) in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_conditioning_barrel6() {
    verify_feature_lrat("conditioning", |s| s.set_condition_enabled(true));
}

/// LRAT proof for vivify in isolation on barrel6 (#4398: hint chain fix).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_vivify_barrel6() {
    verify_feature_lrat("vivify", |s| s.set_vivify_enabled(true));
}

/// LRAT proof for subsumption in isolation on barrel6 (#4398: hint chain fix).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_subsume_barrel6() {
    verify_feature_lrat("subsume", |s| s.set_subsume_enabled(true));
}

/// LRAT proof for HTR in isolation (#4398: antecedent clause ID hint fix).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_htr_barrel6() {
    verify_feature_lrat("htr", |s| s.set_htr_enabled(true));
}

/// LRAT proof with BVE requested in isolation.
///
/// BVE is DRAT-only in the public proof policy, so LRAT mode must clamp the
/// request and still emit a valid base proof.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_bve_barrel6() {
    verify_feature_lrat("bve", |s| {
        s.set_bve_enabled(true);
        assert!(
            !s.inprocessing_feature_profile().bve,
            "LRAT proof mode must clamp BVE requests"
        );
    });
}

/// LRAT proof with BVE requested on manol-pipe-c9 (946 vars, 12786 clauses).
///
/// BVE is clamped in LRAT proof mode; the test rejects Sat and validates the
/// resulting proof if the proof-safe reduced run proves UNSAT.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_bve_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };

    let formula = parse_dimacs(&cnf).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_bve_enabled(true);
    assert!(
        !solver.inprocessing_feature_profile().bve,
        "LRAT proof mode must clamp BVE requests"
    );

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Unsat(_) => {
            let writer = solver
                .take_proof_writer()
                .expect("Proof writer should exist");
            let proof =
                String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");
            assert!(
                !proof.is_empty(),
                "lrat_bve_manol_pipe_c9: LRAT proof must not be empty"
            );
            validate_lrat_proof_text(&cnf, &proof, &lrat_check, "lrat_bve_manol_pipe_c9");
        }
        SatResult::Unknown => {
            // The proof-safe LRAT run may fail to solve this industrial case.
            eprintln!(
                "BVE request was clamped and proof-safe LRAT run returned Unknown on manol-pipe-c9"
            );
        }
        SatResult::Sat(_) => {
            panic!("manol-pipe-c9 is UNSAT — BVE-only must not return Sat");
        }
        _ => unreachable!(),
    }
}

/// LRAT proof with default proof-safe inprocessing on manol-pipe-c9.
/// Tests multi-technique LRAT interaction on an industrial benchmark.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_all_features_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |_solver| {
            // Default LRAT policy clamps proof-incomplete transforms.
        },
        &lrat_check,
        "lrat_default_features_manol_pipe_c9",
    );
}

/// LRAT proof with no inprocessing on manol-pipe-c9 (baseline).
/// Isolates whether LRAT failure is BVE-specific or general.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_baseline_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        super::common::disable_all_inprocessing,
        &lrat_check,
        "lrat_baseline_manol_pipe_c9",
    );
}

/// LRAT proof with decompose requested on barrel6.
///
/// Broad decompose remains clamped in LRAT proof mode; this validates that an
/// explicit request cannot reopen it and the resulting LRAT proof still checks.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_decompose_request_is_clamped_barrel6() {
    verify_feature_lrat("decompose", |s| {
        s.set_decompose_enabled(true);
        assert!(
            !s.inprocessing_feature_profile().decompose,
            "LRAT proof mode must clamp decompose requests"
        );
    });
}

/// LRAT proof with factorize requested on barrel6 (#5020).
///
/// NOTE: Factorize is disabled at runtime in LRAT mode (lrat_override = true
/// in inproc_control.rs) because factorization requires RAT witness semantics
/// which LRAT does not support. This test is a regression guard confirming
/// that LRAT proofs remain valid with factor *requested* but not *executed*.
///
/// For factorize proof output verification, use DRAT mode tests
/// (test_factorize_drat_proof_emission in solver/tests.rs).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_factorize_barrel6() {
    verify_feature_lrat("factorize", |s| {
        s.set_factor_enabled(true);
        assert!(
            !s.inprocessing_feature_profile().factor,
            "LRAT proof mode must clamp factor requests"
        );
    });
}

/// LRAT proof with congruence requested on barrel6.
///
/// Broad congruence remains clamped in LRAT proof mode while decompose is
/// clamped; this validates that an explicit request cannot reopen it and the
/// resulting LRAT proof still checks.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_congruence_request_is_clamped_barrel6() {
    verify_feature_lrat("congruence", |s| {
        s.set_congruence_enabled(true);
        assert!(
            !s.inprocessing_feature_profile().congruence,
            "LRAT proof mode must clamp congruence while decompose is clamped"
        );
    });
}

/// LRAT proof with sweep requested on barrel6 (#5020, #5419).
///
/// Sweep is disabled in proof mode because its substitutions are not
/// checker-visible; this validates that a request stays clamped and the LRAT
/// proof still checks.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_external_sweep_barrel6() {
    verify_feature_lrat("sweep", |s| {
        s.set_sweep_enabled(true);
        assert!(
            !s.inprocessing_feature_profile().sweep,
            "LRAT proof mode must clamp sweep requests"
        );
    });
}

/// DRAT proof mode HONORS decompose requests since 2026-07-09 (registry
/// `Decompose { drat: true }`, externally verified via dpr-trim + cake_lpr;
/// kill-switch AY_AB_DRAT_SUBST=0).
///
/// The formula embeds binary equivalence chains (x13↔x14↔x15↔x16) in
/// PHP(4,3), giving decompose a non-trivial SCC to rewrite — the emitted
/// DRAT proof must still verify externally.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_decompose_request_honored_with_equivalences() {
    // PHP(4,3) + 4-variable equivalence chain: 16 vars, 28 clauses.
    let dimacs = "\
p cnf 16 28
1 2 3 0
4 5 6 0
7 8 9 0
10 11 12 0
-1 -4 0
-1 -7 0
-1 -10 0
-4 -7 0
-4 -10 0
-7 -10 0
-2 -5 0
-2 -8 0
-2 -11 0
-5 -8 0
-5 -11 0
-8 -11 0
-3 -6 0
-3 -9 0
-3 -12 0
-6 -9 0
-6 -12 0
-9 -12 0
-13 14 0
-14 13 0
-14 15 0
-15 14 0
-15 16 0
-16 15 0
";

    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_decompose_enabled(true);
    assert!(
        solver.inprocessing_feature_profile().decompose,
        "DRAT proof mode must honor decompose requests (registry drat=true \
         since 2026-07-09; kill-switch AY_AB_DRAT_SUBST=0)"
    );

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "formula must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof_bytes = writer.into_vec().expect("proof flush");
    assert!(!proof_bytes.is_empty(), "DRAT proof must not be empty");
    super::common::verify_drat_proof(dimacs, &proof_bytes, "drat_decompose_honored");
}

// find_drat_trim removed: use super::common::find_drat_trim() (#3927)

// ── PHP-based LRAT feature tests (fast, no external benchmark) ──

macro_rules! lrat_feature_test {
    ($test_name:ident, $feature_name:literal, $setter:ident) => {
        #[test]
        #[timeout(600_000)]
        fn $test_name() {
            let lrat_check = require_lrat_check();
            solve_and_validate_lrat_configured(
                PHP43_DIMACS,
                |solver| {
                    super::common::disable_all_inprocessing(solver);
                    solver.$setter(true);
                },
                &lrat_check,
                $feature_name,
            );
        }
    };
}

lrat_feature_test!(test_lrat_feature_vivify, "vivify", set_vivify_enabled);
lrat_feature_test!(test_lrat_feature_subsume, "subsume", set_subsume_enabled);
lrat_feature_test!(test_lrat_feature_probe, "probe", set_probe_enabled);
lrat_feature_test!(test_lrat_feature_bce, "bce", set_bce_enabled);
lrat_feature_test!(test_lrat_feature_transred, "transred", set_transred_enabled);
lrat_feature_test!(test_lrat_feature_htr, "htr", set_htr_enabled);
#[test]
#[timeout(600_000)]
fn test_lrat_feature_bve_request_is_clamped() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |solver| {
            super::common::disable_all_inprocessing(solver);
            solver.set_bve_enabled(true);
            assert!(
                !solver.inprocessing_feature_profile().bve,
                "LRAT proof mode must clamp BVE requests"
            );
        },
        &lrat_check,
        "bve",
    );
}
#[test]
#[timeout(600_000)]
fn test_lrat_feature_decompose_request_is_clamped() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |solver| {
            super::common::disable_all_inprocessing(solver);
            solver.set_decompose_enabled(true);
            assert!(
                !solver.inprocessing_feature_profile().decompose,
                "LRAT proof mode must clamp decompose requests"
            );
        },
        &lrat_check,
        "decompose",
    );
}
lrat_feature_test!(
    test_lrat_feature_conditioning,
    "conditioning",
    set_condition_enabled
);
#[test]
#[timeout(600_000)]
fn test_lrat_feature_factorize_request_is_clamped() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |solver| {
            super::common::disable_all_inprocessing(solver);
            solver.set_factor_enabled(true);
            assert!(
                !solver.inprocessing_feature_profile().factor,
                "LRAT proof mode must clamp factor requests"
            );
        },
        &lrat_check,
        "factorize",
    );
}
#[test]
#[timeout(600_000)]
fn test_lrat_feature_congruence_request_is_clamped() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |solver| {
            super::common::disable_all_inprocessing(solver);
            solver.set_congruence_enabled(true);
            assert!(
                !solver.inprocessing_feature_profile().congruence,
                "LRAT proof mode must clamp congruence while decompose is clamped"
            );
        },
        &lrat_check,
        "congruence",
    );
}
#[test]
#[timeout(600_000)]
fn test_lrat_feature_sweep_request_is_clamped() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |solver| {
            super::common::disable_all_inprocessing(solver);
            solver.set_sweep_enabled(true);
            assert!(
                !solver.inprocessing_feature_profile().sweep,
                "LRAT proof mode must clamp sweep requests"
            );
        },
        &lrat_check,
        "sweep",
    );
}
lrat_feature_test!(test_lrat_feature_backbone, "backbone", set_backbone_enabled);

/// BVE request + vivify LRAT validation (#5014).
///
/// BVE is clamped in LRAT proof mode, so this validates that requesting BVE
/// alongside vivify does not reopen the clamp and still leaves a valid LRAT
/// proof stream.
///
/// The specific ClearLevel0 → vivify interaction (where BVE clears reason
/// pointers and vivify encounters the victims) is covered by the unit test
/// test_vivify_probe_lrat_hints_include_level0_proof_id_after_clearlevel0
/// in tests.rs, which uses simulated ClearLevel0 state.
#[test]
#[timeout(600_000)]
fn test_lrat_feature_bve_plus_vivify() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |solver| {
            super::common::disable_all_inprocessing(solver);
            solver.set_bve_enabled(true);
            assert!(
                !solver.inprocessing_feature_profile().bve,
                "LRAT proof mode must clamp BVE requests"
            );
            solver.set_vivify_enabled(true);
        },
        &lrat_check,
        "bve_plus_vivify",
    );
}

// ============================================================================
// Technique-isolation tests on manol-pipe-c9 (#5222 bisection)
//
// These tests enable one LRAT-compatible technique or small combination at a
// time to keep external proof-check coverage localized on an industrial case.
// ============================================================================

/// Vivify-only on manol-pipe-c9. Tests vivify probe LRAT hint chains.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_vivify_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_only_manol_pipe_c9",
    );
}

/// Subsumption-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_subsume_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_subsume_enabled(true);
        },
        &lrat_check,
        "lrat_subsume_only_manol_pipe_c9",
    );
}

/// Probe-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_probe_enabled(true);
        },
        &lrat_check,
        "lrat_probe_only_manol_pipe_c9",
    );
}

/// HTR-only on manol-pipe-c9. Tests hidden ternary resolution LRAT hints.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_htr_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_htr_enabled(true);
        },
        &lrat_check,
        "lrat_htr_only_manol_pipe_c9",
    );
}

/// Congruence-requested on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_congruence_request_is_clamped_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_congruence_enabled(true);
            assert!(
                !s.inprocessing_feature_profile().congruence,
                "LRAT proof mode must clamp congruence while decompose is clamped"
            );
        },
        &lrat_check,
        "lrat_congruence_only_manol_pipe_c9",
    );
}

/// Transred-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_transred_only_manol_pipe_c9",
    );
}

/// BCE-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_bce_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_bce_enabled(true);
        },
        &lrat_check,
        "lrat_bce_only_manol_pipe_c9",
    );
}

/// Vivify + subsume on manol-pipe-c9 (common pair interaction).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_vivify_subsume_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_subsume_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_subsume_manol_pipe_c9",
    );
}

/// Vivify + HTR on manol-pipe-c9. Tests HTR binary → vivify reason interaction.
#[test]
#[cfg_attr(debug_assertions, timeout(900_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_vivify_htr_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_htr_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_htr_manol_pipe_c9",
    );
}

/// Group A: vivify + subsume + probe + transred (no HTR, no BCE, no gate).
#[test]
#[cfg_attr(debug_assertions, timeout(900_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_group_a_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_subsume_enabled(true);
            s.set_probe_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_group_a_manol_pipe_c9",
    );
}

/// Group B: htr + bce + gate (no vivify, no subsume, no probe, no transred).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_group_b_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_htr_enabled(true);
            s.set_bce_enabled(true);
            s.set_gate_enabled(true);
        },
        &lrat_check,
        "lrat_group_b_manol_pipe_c9",
    );
}

/// Vivify + probe on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_vivify_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_probe_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_probe_manol_pipe_c9",
    );
}

/// Vivify + transred on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_vivify_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_transred_manol_pipe_c9",
    );
}

/// Subsume + probe on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_subsume_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_subsume_enabled(true);
            s.set_probe_enabled(true);
        },
        &lrat_check,
        "lrat_subsume_probe_manol_pipe_c9",
    );
}

/// Subsume + transred on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_subsume_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_subsume_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_subsume_transred_manol_pipe_c9",
    );
}

/// Probe + transred on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_isolate_probe_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            super::common::disable_all_inprocessing(s);
            s.set_probe_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_probe_transred_manol_pipe_c9",
    );
}

/// Default LRAT profile with HTR disabled.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_default_except_htr_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_htr_enabled(false);
        },
        &lrat_check,
        "lrat_default_except_htr_manol_pipe_c9",
    );
}

/// Default LRAT profile with BCE disabled.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_default_except_bce_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_bce_enabled(false);
        },
        &lrat_check,
        "lrat_default_except_bce_manol_pipe_c9",
    );
}

/// Default LRAT profile with gate extraction disabled.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_default_except_gate_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_gate_enabled(false);
        },
        &lrat_check,
        "lrat_default_except_gate_manol_pipe_c9",
    );
}

/// Default LRAT profile with transitive reduction disabled.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_default_except_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_transred_enabled(false);
        },
        &lrat_check,
        "lrat_default_except_transred_manol_pipe_c9",
    );
}

/// Default LRAT profile with probing disabled.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(600_000))]
fn test_lrat_default_except_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_probe_enabled(false);
        },
        &lrat_check,
        "lrat_default_except_probe_manol_pipe_c9",
    );
}

// ============================================================================
// Binary LRAT format validation tests (#5334)
//
// All previous tests use lrat_text format. These tests validate that ay's
// binary LRAT output (LEB128-encoded) is correctly formatted and externally
// verifiable. Binary LRAT is the format used by CaDiCaL and SAT Competition
// checkers; gaps here mean ay cannot participate in proof-checked divisions.
//
// Uses ay-lrat-check (auto-detects binary) since external lrat-check from
// drat-trim may not support binary format.
// ============================================================================

#[test]
fn workspace_checker_plan_ignores_missing_and_stale_ambient_binaries() {
    let workspace = tempfile::tempdir().expect("tempdir");
    let binary_name = format!("ay-lrat-check{}", std::env::consts::EXE_SUFFIX);
    let stale_release = workspace.path().join("target/release").join(&binary_name);
    let stale_debug = workspace.path().join("target/debug").join(&binary_name);
    std::fs::create_dir_all(stale_release.parent().unwrap()).unwrap();
    std::fs::create_dir_all(stale_debug.parent().unwrap()).unwrap();
    std::fs::write(&stale_release, b"stale-release").unwrap();
    std::fs::write(&stale_debug, b"stale-debug").unwrap();

    let identity = source_identity_from_parts(b"example-head\n", b"", &[]);
    let target = workspace_checker_target_dir_for_outer(workspace.path(), &identity, None);
    let planned = cargo_binary_path(&target, "ay-lrat-check");
    assert_ne!(planned, stale_release);
    assert_ne!(planned, stale_debug);
    assert!(!planned.exists(), "regression plan should start missing");
    assert!(
        target
            .file_name()
            .and_then(std::ffi::OsStr::to_str)
            .is_some_and(|name| name.contains(&identity)),
        "checker target must be bound to the exact source identity"
    );

    let outer_exe = target.join("debug/deps/group_drat-test");
    let collision_safe =
        workspace_checker_target_dir_for_outer(workspace.path(), &identity, Some(&outer_exe));
    assert_ne!(collision_safe, target);
    assert!(!outer_exe.starts_with(&collision_safe));
}

/// Binary implication chain that becomes UNSAT only after walking a chain of
/// binary reasons from `-1` back to `1`.
const BINARY_REASON_JUMP_CHAIN_DIMACS: &str = "\
p cnf 5 6
1 2 0
-2 3 0
-3 4 0
-4 1 0
-1 5 0
-1 -5 0
";

/// Canary for future proof-safe LRAT binary-reason jump work.
///
/// Today LRAT mode must keep binary propagations as clause reasons because the
/// external LRAT proof needs clause IDs for resolution hints. This test
/// validates the target chain with binary LRAT while asserting that no jump
/// reasons fire. Once a proof-safe LRAT jump-reason gate exists, enable that
/// gate here, and change the local invariant to:
///
/// `assert!(solver.jumped_reasons() > 0, "canary must exercise binary reason jumps");`
///
/// The external `ay-lrat-check` validation below must still pass.
///
/// The timeout includes one source-identified, isolated Cargo build when this
/// is the first checker-consuming test in a fresh checkout.
#[test]
#[timeout(600_000)]
fn test_lrat_external_binary_reason_jump_chain_canary() {
    let checker = require_ay_lrat_check();
    let formula = parse_dimacs(BINARY_REASON_JUMP_CHAIN_DIMACS).expect("canary DIMACS must parse");
    assert_eq!(formula.num_vars, 5);
    assert_eq!(formula.clauses.len(), 6);

    let proof_writer = ProofOutput::lrat_binary(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    super::common::disable_all_inprocessing(&mut solver);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "binary-reason jump-chain canary formula must be UNSAT"
    );
    assert_eq!(
        solver.jumped_reasons(),
        0,
        "LRAT binary mode must not use jump reasons until a proof-safe gate preserves hint IDs"
    );

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof_bytes = writer.into_vec().expect("proof flush");
    assert!(
        !proof_bytes.is_empty(),
        "binary-reason jump-chain canary must emit a binary LRAT proof"
    );
    validate_lrat_proof_binary(
        BINARY_REASON_JUMP_CHAIN_DIMACS,
        &proof_bytes,
        &checker,
        "binary_reason_jump_chain_canary",
    );
}

/// Binary LRAT: PHP(3,2), no inprocessing.
#[test]
#[timeout(600_000)]
fn test_lrat_binary_external_php32() {
    let checker = require_ay_lrat_check();
    solve_and_validate_lrat_binary_configured(
        PHP32_DIMACS,
        super::common::disable_all_inprocessing,
        &checker,
        "binary_php32",
    );
}

/// Binary LRAT: PHP(4,3), no inprocessing.
#[test]
#[timeout(600_000)]
fn test_lrat_binary_external_php43() {
    let checker = require_ay_lrat_check();
    solve_and_validate_lrat_binary_configured(
        PHP43_DIMACS,
        super::common::disable_all_inprocessing,
        &checker,
        "binary_php43",
    );
}

/// Binary LRAT: PHP(4,3) with default proof-safe features enabled.
///
/// Validates binary LRAT proof completeness when inprocessing techniques
/// generate proof steps. This is the counterpart of the text-format
/// all-features tests.
#[test]
#[timeout(600_000)]
fn test_lrat_binary_external_php43_all_features() {
    let checker = require_ay_lrat_check();
    solve_and_validate_lrat_binary_configured(
        PHP43_DIMACS,
        |_solver| {},
        &checker,
        "binary_php43_all_features",
    );
}

/// Binary LRAT: random 3-SAT formula.
#[test]
#[timeout(600_000)]
fn test_lrat_binary_external_random_3sat() {
    let checker = require_ay_lrat_check();
    solve_and_validate_lrat_binary_configured(
        RANDOM_3SAT_DIMACS,
        super::common::disable_all_inprocessing,
        &checker,
        "binary_random_3sat",
    );
}

/// Binary LRAT: UNSAT corpus with no inprocessing.
///
/// Same benchmark set as text-format corpus test, but validates binary
/// encoding. A failure here (with text passing) indicates a binary
/// encoding bug in LratWriter, not a proof chain error.
#[test]
#[timeout(600_000)]
fn test_lrat_binary_external_unsat_corpus() {
    let checker = require_ay_lrat_check();
    let corpus_dir = super::common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    cnf_files.sort();

    assert!(
        !cnf_files.is_empty(),
        "No .cnf files found in {}",
        corpus_dir.display()
    );

    let total = cnf_files.len();
    let mut verified = 0usize;
    for cnf_path in &cnf_files {
        let dimacs = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", cnf_path.display(), e));
        let label = cnf_path
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or("corpus_case");
        solve_and_validate_lrat_binary_configured(
            &dimacs,
            super::common::disable_all_inprocessing,
            &checker,
            &format!("binary_corpus_{label}"),
        );
        verified += 1;
    }

    assert_eq!(verified, total);
    eprintln!("Binary LRAT corpus: ALL {total}/{total} benchmarks verified by ay-lrat-check");
}

/// Binary vs text LRAT cross-validation: both formats on the same formula
/// must produce proofs that independently validate.
///
/// This catches format-specific encoding bugs (e.g., LEB128 overflow,
/// wrong marker bytes) while confirming the proof chains are equivalent.
#[test]
#[timeout(600_000)]
fn test_lrat_binary_vs_text_cross_validate_php43() {
    let ay_checker = require_ay_lrat_check();
    let lrat_check = require_lrat_check();

    // Text format proof validated by external lrat-check.
    let text_proof = solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        super::common::disable_all_inprocessing,
        &lrat_check,
        "cross_text_php43",
    );

    // Binary format proof validated by ay-lrat-check.
    let binary_proof = solve_and_validate_lrat_binary_configured(
        PHP43_DIMACS,
        super::common::disable_all_inprocessing,
        &ay_checker,
        "cross_binary_php43",
    );

    // Both proofs must be non-empty and different formats.
    assert!(!text_proof.is_empty());
    assert!(!binary_proof.is_empty());
    // Binary is typically smaller than text (LEB128 vs decimal ASCII).
    eprintln!(
        "Cross-validation: text={} bytes, binary={} bytes",
        text_proof.len(),
        binary_proof.len()
    );
}
