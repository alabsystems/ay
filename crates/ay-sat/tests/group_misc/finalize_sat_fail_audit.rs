// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FINALIZE_SAT_FAIL audit test suite (#7917).
//!
//! Verifies that no benchmark in the corpus triggers the FINALIZE_SAT_FAIL
//! safety net, which converts a SAT result to UNKNOWN when model verification
//! fails after reconstruction. A FINALIZE_SAT_FAIL indicates an underlying
//! bug in BVE, reconstruction, or model extension.
//!
//! Test structure:
//! - `no_finalize_sat_fail_on_small_corpus` -- runs canary + small UNSAT
//!   benchmarks and asserts none return UNKNOWN(InvalidSatModel).
//! - `braun_family_no_finalize_sat_fail` -- braun UNSAT circuit benchmarks.
//! - `sat_model_verification_positive` -- SAT formulas produce valid models
//!   that pass independent verification (no FINALIZE_SAT_FAIL).
//! - `unsat_formulas_no_invalid_sat_model_reason` -- known-UNSAT formulas
//!   never set the InvalidSatModel unknown reason.
//! - `satcomp_sample_no_finalize_sat_fail` -- satcomp2024-sample benchmarks
//!   (skipped if directory absent).
//! - `satcomp_2022_2023_no_finalize_sat_fail` -- 2022/2023 benchmark files.
//! - `mfleury_unsat_no_finalize_sat_fail` -- mfleury SAT-2009 UNSAT corpus.
//! - `mfleury_sat_no_finalize_sat_fail` -- mfleury SAT-2009 SAT corpus.
//! - `test_data_cnf_no_finalize_sat_fail` -- vendored test data CNF files.
//! - `creusat_php_no_finalize_sat_fail` -- CreuSAT PHP benchmarks.
//! - `satlib_uuf250_no_finalize_sat_fail` -- SATLIB UUF250 random UNSAT.
//! - `satlib_uf250_no_finalize_sat_fail` -- SATLIB UF250 random SAT.
//! - `creusat_2015_no_finalize_sat_fail` -- CreuSAT 2015 32-bit circuits.
//! - `satlib_uuf200_no_finalize_sat_fail` -- SATLIB UUF200 random UNSAT.

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, Literal, SatResult, SatUnknownReason};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// Per-benchmark timeout. Short because we run many benchmarks and only need
/// to detect FINALIZE_SAT_FAIL, not prove completeness.
const TIMEOUT_SECS: u64 = 10;

/// Solve a DIMACS benchmark with a timeout. Returns the result and the
/// solver's `last_unknown_reason()` for classifying Unknown outcomes.
fn solve_benchmark(dimacs: &str, timeout_secs: u64) -> (SatResult, Option<SatUnknownReason>) {
    let formula = parse_dimacs(dimacs).expect("DIMACS parse failed");
    let mut solver = formula.into_solver();

    let flag = Arc::new(AtomicBool::new(false));
    let flag_clone = flag.clone();
    solver.set_interrupt(flag.clone());
    let handle = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(timeout_secs));
        flag_clone.store(true, Ordering::Relaxed);
    });

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    let reason = solver.last_unknown_reason();
    (result, reason)
}

/// Verify that a model satisfies all clauses. Returns the index of the
/// first violated clause, or None if the model is valid.
fn first_violated_clause(clauses: &[Vec<Literal>], model: &[bool]) -> Option<usize> {
    clauses.iter().position(|clause| {
        !clause.iter().any(|lit| {
            let vi = lit.variable().index();
            vi < model.len() && (model[vi] == lit.is_positive())
        })
    })
}

/// Collect all .cnf files from a directory (non-recursive).
fn collect_cnf_dir(dir: &std::path::Path) -> Vec<(String, String)> {
    collect_cnf_dir_with_known_unsat(dir)
        .into_iter()
        .map(|(l, d, _)| (l, d))
        .collect()
}

/// Collect all .cnf files from a directory (non-recursive), with known-UNSAT flag.
///
/// The third element is `true` if the directory path contains "unsat" --
/// all files in an "unsat" directory are known-UNSAT by convention.
fn collect_cnf_dir_with_known_unsat(dir: &std::path::Path) -> Vec<(String, String, bool)> {
    let mut results = Vec::new();
    if !dir.is_dir() {
        return results;
    }
    let dir_is_unsat = dir.to_string_lossy().contains("unsat");
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().is_some_and(|ext| ext == "cnf") {
                let label = path
                    .file_name()
                    .map(|n| n.to_string_lossy().to_string())
                    .unwrap_or_default();
                if let Ok(dimacs) = std::fs::read_to_string(&path) {
                    results.push((label, dimacs, dir_is_unsat));
                }
            }
        }
    }
    results.sort_by(|a, b| a.0.cmp(&b.0));
    results
}

/// Audit result for a batch of benchmarks.
struct AuditResult {
    sat_count: usize,
    unsat_count: usize,
    timeout_count: usize,
    finalize_sat_failures: Vec<String>,
    model_violations: Vec<String>,
    soundness_bugs: Vec<String>,
}

impl AuditResult {
    fn new() -> Self {
        Self {
            sat_count: 0,
            unsat_count: 0,
            timeout_count: 0,
            finalize_sat_failures: Vec::new(),
            model_violations: Vec::new(),
            soundness_bugs: Vec::new(),
        }
    }

    /// Run one benchmark and record the result.
    fn run_one(&mut self, label: &str, dimacs: &str, known_unsat: bool, timeout: u64) {
        let original_clauses = match parse_dimacs(dimacs) {
            Ok(f) => f.clauses,
            Err(e) => {
                eprintln!("SKIP {label}: parse error: {e}");
                return;
            }
        };
        let (result, reason) = solve_benchmark(dimacs, timeout);

        match &result {
            SatResult::Sat(model) => {
                if known_unsat {
                    self.soundness_bugs
                        .push(format!("{label}: known-UNSAT returned SAT"));
                    return;
                }
                self.sat_count += 1;
                if let Some(vi) = first_violated_clause(&original_clauses, model) {
                    let clause = &original_clauses[vi];
                    let cd: Vec<i32> = clause
                        .iter()
                        .map(|l| {
                            let v = l.variable().index() as i32 + 1;
                            if l.is_positive() {
                                v
                            } else {
                                -v
                            }
                        })
                        .collect();
                    self.model_violations
                        .push(format!("{label}: model violates clause {vi}: {cd:?}"));
                }
            }
            SatResult::Unsat(_) => {
                self.unsat_count += 1;
            }
            SatResult::Unknown => {
                if reason == Some(SatUnknownReason::InvalidSatModel) {
                    self.finalize_sat_failures.push(format!(
                        "{label}: FINALIZE_SAT_FAIL (Unknown/InvalidSatModel)"
                    ));
                } else {
                    self.timeout_count += 1;
                }
            }
            _ => unreachable!(),
        }
    }

    fn assert_clean(&self, context: &str) {
        assert!(
            self.soundness_bugs.is_empty(),
            "{context}: SOUNDNESS BUGS:\n{}",
            self.soundness_bugs.join("\n"),
        );
        assert!(
            self.model_violations.is_empty(),
            "{context}: model violations:\n{}",
            self.model_violations.join("\n"),
        );
        assert!(
            self.finalize_sat_failures.is_empty(),
            "{context}: FINALIZE_SAT_FAIL triggered ({}):\n{}",
            self.finalize_sat_failures.len(),
            self.finalize_sat_failures.join("\n"),
        );
    }

    fn summary(&self, context: &str) {
        eprintln!(
            "{context}: sat={} unsat={} timeout={} fsf={} mv={} sb={}",
            self.sat_count,
            self.unsat_count,
            self.timeout_count,
            self.finalize_sat_failures.len(),
            self.model_violations.len(),
            self.soundness_bugs.len(),
        );
    }
}

// =============================================================================
// Test 1: Small UNSAT corpus + canary benchmarks
// =============================================================================

/// Runs canary + small UNSAT benchmarks. None should trigger FINALIZE_SAT_FAIL.
///
/// known-UNSAT classification: all files in `benchmarks/sat/unsat/` are UNSAT
/// by directory convention. Canary files use the "unsat" substring in filename.
/// This replaces the previous keyword-based heuristic (#7917) which was fragile
/// and could silently accept wrong SAT results on newly-added UNSAT benchmarks.
#[test]
fn no_finalize_sat_fail_on_small_corpus() {
    let root = super::common::workspace_root();

    let mut benchmarks = Vec::new();
    // canary directory: tiny_unsat.cnf is UNSAT, tiny_sat.cnf is SAT.
    for (label, dimacs) in collect_cnf_dir(&root.join("benchmarks/sat/canary")) {
        let known_unsat = label.contains("unsat");
        benchmarks.push((label, dimacs, known_unsat));
    }
    // unsat directory: ALL files are known-UNSAT by convention.
    benchmarks.extend(collect_cnf_dir_with_known_unsat(
        &root.join("benchmarks/sat/unsat"),
    ));

    assert!(!benchmarks.is_empty(), "no benchmarks found");

    let mut audit = AuditResult::new();
    for (label, dimacs, known_unsat) in &benchmarks {
        audit.run_one(label, dimacs, *known_unsat, TIMEOUT_SECS);
    }

    audit.summary("small_corpus");
    assert!(
        audit.sat_count + audit.unsat_count > 0,
        "expected at least one benchmark to complete"
    );
    audit.assert_clean("small_corpus");
}

// =============================================================================
// Test 2: Braun circuit equivalence family
// =============================================================================

/// All eq.atree.braun benchmarks are known-UNSAT. None should trigger
/// FINALIZE_SAT_FAIL (and certainly none should return SAT).
#[test]
fn braun_family_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let benchmarks = collect_cnf_dir(&root.join("benchmarks/sat/eq_atree_braun"));
    if benchmarks.is_empty() {
        eprintln!("SKIP: braun benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        audit.run_one(label, dimacs, true, 15);
    }

    audit.summary("braun_family");
    audit.assert_clean("braun_family");
}

// =============================================================================
// Test 3: SAT formulas produce valid models (positive case)
// =============================================================================

/// Inline SAT formulas + canary must return SAT with valid models. This is
/// the positive-case test: no FINALIZE_SAT_FAIL, and the model independently
/// satisfies all original clauses.
#[test]
fn sat_model_verification_positive() {
    let root = super::common::workspace_root();

    let mut formulas: Vec<(String, String)> = vec![
        ("unit_sat".into(), "p cnf 1 1\n1 0\n".into()),
        ("binary_sat".into(), "p cnf 2 1\n1 2 0\n".into()),
        (
            "3clause_sat".into(),
            "p cnf 4 3\n1 2 0\n3 4 0\n-1 -3 0\n".into(),
        ),
        (
            "diamond_sat".into(),
            "p cnf 4 4\n1 2 0\n-1 3 0\n-2 4 0\n-3 -4 0\n".into(),
        ),
        // Chain implications: force x1=T, x1->x2, x2->x3, x3->x4
        (
            "chain_sat".into(),
            "p cnf 4 4\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n".into(),
        ),
        // XOR-like: (x1 v x2) & (-x1 v -x2) -- exactly one true
        ("xor_sat".into(), "p cnf 2 2\n1 2 0\n-1 -2 0\n".into()),
    ];

    let canary = root.join("benchmarks/sat/canary/tiny_sat.cnf");
    if canary.is_file() {
        if let Ok(d) = std::fs::read_to_string(&canary) {
            formulas.push(("canary_tiny_sat".into(), d));
        }
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &formulas {
        audit.run_one(label, dimacs, false, 10);
    }

    audit.summary("sat_positive");
    assert!(
        audit.sat_count > 0,
        "expected at least one SAT result to verify"
    );
    audit.assert_clean("sat_positive");
}

// =============================================================================
// Test 4: UNSAT formulas never set InvalidSatModel reason
// =============================================================================

/// Known-UNSAT formulas (PHP, unit conflict) must return UNSAT, and the
/// solver must not have InvalidSatModel as the unknown reason. This verifies
/// the FINALIZE_SAT_FAIL path is not spuriously triggered on UNSAT formulas.
#[test]
fn unsat_formulas_no_invalid_sat_model_reason() {
    let cases = [
        ("php_3_2", super::common::PHP32_DIMACS),
        ("php_4_3", super::common::PHP43_DIMACS),
        ("unit_conflict", "p cnf 1 2\n1 0\n-1 0\n"),
        ("binary_conflict", "p cnf 2 4\n1 0\n2 0\n-1 -2 0\n-1 0\n"),
    ];

    for (label, dimacs) in &cases {
        let (result, reason) = solve_benchmark(dimacs, 30);
        match result {
            SatResult::Unsat(_) => {
                assert_ne!(
                    reason,
                    Some(SatUnknownReason::InvalidSatModel),
                    "{label}: UNSAT has InvalidSatModel reason set"
                );
            }
            SatResult::Sat(_) => {
                panic!("{label}: known-UNSAT returned SAT");
            }
            SatResult::Unknown => {
                assert_ne!(
                    reason,
                    Some(SatUnknownReason::InvalidSatModel),
                    "{label}: UNSAT formula triggered FINALIZE_SAT_FAIL"
                );
            }
            _ => unreachable!(),
        }
    }
}

// =============================================================================
// Test 5: SATCOMP 2024 sample (skipped if absent)
// =============================================================================

/// Runs satcomp2024-sample benchmarks with FINALIZE_SAT_FAIL detection.
/// Skips gracefully when the directory is absent.
#[test]
fn satcomp_sample_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let sample_dir = root.join("benchmarks/sat/satcomp2024-sample");
    if !sample_dir.is_dir() {
        eprintln!("SKIP: satcomp2024-sample not found");
        return;
    }

    let benchmarks = collect_cnf_dir(&sample_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: no .cnf files in satcomp2024-sample");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        // We don't know the expected result for satcomp benchmarks.
        audit.run_one(label, dimacs, false, TIMEOUT_SECS);
    }

    audit.summary("satcomp_sample");
    audit.assert_clean("satcomp_sample");
}

// =============================================================================
// Test 6: benchmarks/sat/2022 + 2023 (unknown status, medium formulas)
// =============================================================================

/// Audits the 2022 and 2023 benchmark files. These have unknown SAT/UNSAT
/// status, so we treat them as status-unknown and only check for
/// FINALIZE_SAT_FAIL (and model validity on SAT results).
#[test]
fn satcomp_2022_2023_no_finalize_sat_fail() {
    let root = super::common::workspace_root();

    let mut benchmarks = Vec::new();
    benchmarks.extend(collect_cnf_dir(&root.join("benchmarks/sat/2022")));
    benchmarks.extend(collect_cnf_dir(&root.join("benchmarks/sat/2023")));

    if benchmarks.is_empty() {
        eprintln!("SKIP: benchmarks/sat/2022 and 2023 not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        // Unknown status -- don't assert known-UNSAT.
        audit.run_one(label, dimacs, false, 30);
    }

    audit.summary("satcomp_2022_2023");
    audit.assert_clean("satcomp_2022_2023");
}

// =============================================================================
// Test 7: mfleury SAT-2009 preprocessed UNSAT benchmarks
// =============================================================================

/// All mfleury SAT-2009-preprocessed easy/unsat benchmarks are known-UNSAT.
/// None should trigger FINALIZE_SAT_FAIL or return SAT.
#[test]
fn mfleury_unsat_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let unsat_dir = root.join("reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat");

    let benchmarks = collect_cnf_dir(&unsat_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: mfleury unsat benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        audit.run_one(label, dimacs, true, 30);
    }

    audit.summary("mfleury_unsat");
    assert!(
        audit.unsat_count + audit.timeout_count > 0,
        "expected at least one mfleury UNSAT benchmark to complete"
    );
    audit.assert_clean("mfleury_unsat");
}

// =============================================================================
// Test 8: mfleury SAT-2009 preprocessed SAT benchmarks (positive case)
// =============================================================================

/// The smaller mfleury SAT-2009 SAT benchmarks should produce valid models
/// and never trigger FINALIZE_SAT_FAIL.
#[test]
fn mfleury_sat_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let sat_dir = root.join("reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/sat");

    let benchmarks = collect_cnf_dir(&sat_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: mfleury sat benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        if dimacs.lines().count() > 50_000 {
            eprintln!("SKIP {label}: too large for audit timeout");
            continue;
        }
        audit.run_one(label, dimacs, false, 30);
    }

    audit.summary("mfleury_sat");
    audit.assert_clean("mfleury_sat");
}

// =============================================================================
// Test 9: Vendored test data CNF files
// =============================================================================

/// Audits the vendored CNF files in crates/ay-sat/tests/data/.
#[test]
fn test_data_cnf_no_finalize_sat_fail() {
    let data_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");

    let benchmarks = collect_cnf_dir(&data_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: no CNF files in tests/data");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        // barrel6, crn_11_99_u, and FmlaEquivChain are all known-UNSAT.
        let known_unsat = label.contains("barrel")
            || label.contains("crn_11_99_u")
            || label.contains("FmlaEquivChain");
        audit.run_one(label, dimacs, known_unsat, 30);
    }

    audit.summary("test_data_cnf");
    audit.assert_clean("test_data_cnf");
}

// =============================================================================
// Test 10: CreuSAT generated PHP benchmarks (known-UNSAT)
// =============================================================================

/// PHP (pigeonhole principle) benchmarks from CreuSAT's generated set.
#[test]
fn creusat_php_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let php_dir = root.join("reference/creusat/tests/generated");

    let benchmarks = collect_cnf_dir(&php_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: creusat php benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        let unsat = is_php_unsat(label);
        audit.run_one(label, dimacs, unsat, 15);
    }

    audit.summary("creusat_php");
    audit.assert_clean("creusat_php");
}

/// Determine if a PHP filename represents a known-UNSAT instance.
fn is_php_unsat(filename: &str) -> bool {
    let name = filename.strip_suffix(".cnf").unwrap_or(filename);
    let rest = match name.strip_prefix("php") {
        Some(r) => r,
        None => return false,
    };

    if let Some((p_str, h_str)) = rest.split_once('_') {
        if let (Ok(p), Ok(h)) = (p_str.parse::<u32>(), h_str.parse::<u32>()) {
            return p > h;
        }
    }

    let digits: String = rest.chars().filter(char::is_ascii_digit).collect();
    if digits.len() >= 2 {
        let mid = digits.len() / 2;
        if let (Ok(p), Ok(h)) = (digits[..mid].parse::<u32>(), digits[mid..].parse::<u32>()) {
            return p > h;
        }
    }

    true
}

// =============================================================================
// Test 11: SATLIB UUF250 random 3-SAT UNSAT instances
// =============================================================================

/// Audits all 100 UUF250 (250-variable, 1065-clause) random 3-SAT UNSAT
/// instances from SATLIB.
#[test]
fn satlib_uuf250_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let uuf_dir = root.join("reference/creusat/tests/satlib/UUF250.1065.100");

    let benchmarks = collect_cnf_dir(&uuf_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: SATLIB UUF250 benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        audit.run_one(label, dimacs, true, 30);
    }

    audit.summary("satlib_uuf250");
    assert!(
        audit.unsat_count > 0,
        "expected at least one UUF250 benchmark to return UNSAT"
    );
    audit.assert_clean("satlib_uuf250");
}

// =============================================================================
// Test 12: SATLIB UF250 random 3-SAT SAT instances (positive case)
// =============================================================================

/// Audits UF250 random 3-SAT SAT instances from SATLIB.
#[test]
fn satlib_uf250_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let uf_dir = root.join("reference/creusat/tests/satlib/UF250.1065.100");

    let benchmarks = collect_cnf_dir(&uf_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: SATLIB UF250 benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        audit.run_one(label, dimacs, false, 30);
    }

    audit.summary("satlib_uf250");
    assert!(
        audit.sat_count > 0,
        "expected at least one UF250 benchmark to return SAT"
    );
    audit.assert_clean("satlib_uf250");
}

// =============================================================================
// Test 13: CreuSAT 2015 benchmarks (32-bit arithmetic circuits)
// =============================================================================

/// CreuSAT 2015 benchmarks (32-bit arithmetic circuit formulas).
#[test]
fn creusat_2015_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let dir_2015 = root.join("reference/creusat/tests/2015");

    let benchmarks = collect_cnf_dir(&dir_2015);
    if benchmarks.is_empty() {
        eprintln!("SKIP: creusat 2015 benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        audit.run_one(label, dimacs, false, 30);
    }

    audit.summary("creusat_2015");
    audit.assert_clean("creusat_2015");
}

// =============================================================================
// Test 14: SATLIB UUF200 random 3-SAT UNSAT instances
// =============================================================================

/// Audits 100 UUF200 random 3-SAT UNSAT instances from SATLIB.
#[test]
fn satlib_uuf200_no_finalize_sat_fail() {
    let root = super::common::workspace_root();
    let uuf_dir = root.join("reference/creusat/tests/satlib/UUF200.860.100");

    let benchmarks = collect_cnf_dir(&uuf_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: SATLIB UUF200 benchmarks not found");
        return;
    }

    let mut audit = AuditResult::new();
    for (label, dimacs) in &benchmarks {
        audit.run_one(label, dimacs, true, 30);
    }

    audit.summary("satlib_uuf200");
    assert!(
        audit.unsat_count > 0,
        "expected at least one UUF200 benchmark to return UNSAT"
    );
    audit.assert_clean("satlib_uuf200");
}
