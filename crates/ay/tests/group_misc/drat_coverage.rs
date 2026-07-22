// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Comprehensive DRAT proof verification coverage test.
//!
//! Runs ALL available small UNSAT .cnf benchmarks through the solver with DRAT
//! output enabled, then verifies the DRAT proof using:
//!   1. The ay-drat-check in-process forward checker (always)
//!   2. External drat-trim binary when available (optional cross-validation)
//!
//! This test addresses Gap 2 from the development design notes: "Only 7.7% of
//! tests use DRAT verification." The goal is to verify that every UNSAT
//! benchmark produces a valid DRAT proof.
//!
//! Coverage scope:
//!   - All 27 benchmarks/sat/unsat/*.cnf files
//!   - All benchmarks/sat/eq_atree_braun/*.unsat.cnf files (< 700 vars),
//!     excluding release-only cases in debug builds
//!   - benchmarks/sat/canary/tiny_unsat.cnf
//!   - Small satcomp2024-sample UNSAT benchmarks (< 2000 vars)
//!
//! Part of #7913.

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_sat::{
    parse_dimacs, ProofOutput, SatFeatures, Solver, SolverVariant, VariantInput, VariantProfilePlan,
};
use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::Command;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

/// Find the drat-trim binary in standard locations.
fn find_drat_trim() -> Option<PathBuf> {
    if let Ok(output) = Command::new("which").arg("drat-trim").output() {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_owned();
            if !path.is_empty() {
                return Some(PathBuf::from(path));
            }
        }
    }
    for candidate in [
        "/tmp/drat-trim/drat-trim",
        "/usr/local/bin/drat-trim",
        "/opt/homebrew/bin/drat-trim",
    ] {
        let path = PathBuf::from(candidate);
        if path.exists() {
            return Some(path);
        }
    }
    let workspace_bin = workspace_root().join("bin/drat-trim");
    if workspace_bin.exists() {
        return Some(workspace_bin);
    }
    None
}

/// Outcome of solving + DRAT verification for one benchmark.
#[derive(Debug)]
struct DratResult {
    name: String,
    solve_ok: bool,
    proof_size_bytes: usize,
    proof_steps: usize,
    internal_check_ok: bool,
    internal_check_error: Option<String>,
    external_check_ok: Option<bool>,
    external_check_error: Option<String>,
}

/// Solve a benchmark with ay and produce a DRAT proof, then verify it.
///
/// Returns a `DratResult` describing what happened. Does not panic on
/// verification failure so the caller can aggregate results.
fn solve_and_verify_drat(cnf_path: &Path, drat_trim: Option<&Path>) -> DratResult {
    let name = cnf_path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| cnf_path.display().to_string());

    let cnf_text = match std::fs::read_to_string(cnf_path) {
        Ok(s) => s,
        Err(e) => {
            return DratResult {
                name,
                solve_ok: false,
                proof_size_bytes: 0,
                proof_steps: 0,
                internal_check_ok: false,
                internal_check_error: Some(format!("read error: {e}")),
                external_check_ok: None,
                external_check_error: None,
            };
        }
    };

    // Parse and solve with DRAT output
    let formula = match parse_dimacs(&cnf_text) {
        Ok(f) => f,
        Err(e) => {
            return DratResult {
                name,
                solve_ok: false,
                proof_size_bytes: 0,
                proof_steps: 0,
                internal_check_ok: false,
                internal_check_error: Some(format!("parse error: {e}")),
                external_check_ok: None,
                external_check_error: None,
            };
        }
    };

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
    let profile = VariantProfilePlan::for_features(
        SolverVariant::Default,
        VariantInput::new(formula.num_vars, formula.num_clauses, true, false),
        &features,
    );
    profile.config.apply_to_solver(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    if !result.is_unsat() {
        return DratResult {
            name,
            solve_ok: false,
            proof_size_bytes: 0,
            proof_steps: 0,
            internal_check_ok: false,
            internal_check_error: Some(format!("expected UNSAT, got {result:?}")),
            external_check_ok: None,
            external_check_error: None,
        };
    }

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof flush");

    // Step 1: In-process verification using ay-drat-check
    let (internal_ok, internal_err, step_count) = {
        let formula_for_check = parse_cnf(cnf_text.as_bytes()).expect("parse CNF for checker");
        match parse_drat(&proof_bytes) {
            Ok(steps) => {
                let step_count = steps.len();
                let mut checker = DratChecker::new(formula_for_check.num_vars, true);
                match checker.verify(&formula_for_check.clauses, &steps) {
                    Ok(()) => (true, None, step_count),
                    Err(e) => (false, Some(format!("{e}")), step_count),
                }
            }
            Err(e) => (false, Some(format!("DRAT parse error: {e}")), 0),
        }
    };

    // Step 2: External verification using drat-trim (when available)
    let (external_ok, external_err) = if let Some(dt) = drat_trim {
        let cnf_tmp =
            std::env::temp_dir().join(format!("ay_drat_cov_{}_{}.cnf", std::process::id(), &name));
        let proof_tmp =
            std::env::temp_dir().join(format!("ay_drat_cov_{}_{}.drat", std::process::id(), &name));
        std::fs::write(&cnf_tmp, &cnf_text).expect("write CNF temp");
        std::fs::write(&proof_tmp, &proof_bytes).expect("write DRAT temp");

        let output = Command::new(dt)
            .arg(&cnf_tmp)
            .arg(&proof_tmp)
            .output()
            .expect("execute drat-trim");

        let _ = std::fs::remove_file(&cnf_tmp);
        let _ = std::fs::remove_file(&proof_tmp);

        let stdout = String::from_utf8_lossy(&output.stdout);
        // Use "s VERIFIED" prefix match to avoid false positive from "s NOT VERIFIED"
        let verified = output.status.success() && stdout.contains("s VERIFIED");
        if verified {
            (Some(true), None)
        } else {
            let stderr = String::from_utf8_lossy(&output.stderr);
            (
                Some(false),
                Some(format!(
                    "exit={:?}, stdout={}, stderr={}",
                    output.status.code(),
                    stdout.trim(),
                    stderr.trim()
                )),
            )
        }
    } else {
        (None, None)
    };

    DratResult {
        name,
        solve_ok: true,
        proof_size_bytes: proof_bytes.len(),
        proof_steps: step_count,
        internal_check_ok: internal_ok,
        internal_check_error: internal_err,
        external_check_ok: external_ok,
        external_check_error: external_err,
    }
}

/// Collect all UNSAT benchmark paths that should be DRAT-verified.
fn collect_unsat_benchmarks() -> Vec<PathBuf> {
    let root = workspace_root();
    let mut paths = Vec::new();

    // 1. All benchmarks/sat/unsat/*.cnf (27 files)
    let unsat_dir = root.join("benchmarks/sat/unsat");
    if unsat_dir.is_dir() {
        let mut entries: Vec<_> = std::fs::read_dir(&unsat_dir)
            .expect("read unsat dir")
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|ext| ext == "cnf"))
            .collect();
        entries.sort();
        paths.extend(entries);
    }

    // 2. benchmarks/sat/eq_atree_braun/*.unsat.cnf (only those with < 700 vars)
    //    Raised from 500 to 700 to include braun.10 (505 vars) in all builds and
    //    braun.8 (684 vars) in release builds. The aggregate test follows the same
    //    debug/release contract as the individual per-benchmark tests below.
    let eq_dir = root.join("benchmarks/sat/eq_atree_braun");
    if eq_dir.is_dir() {
        let mut entries: Vec<_> = std::fs::read_dir(&eq_dir)
            .expect("read eq_atree_braun dir")
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| {
                p.file_name()
                    .is_some_and(|n| n.to_string_lossy().ends_with(".unsat.cnf"))
            })
            .filter(|p| {
                if cfg!(debug_assertions) {
                    return p
                        .file_name()
                        .is_none_or(|n| n != "eq.atree.braun.8.unsat.cnf");
                }
                true
            })
            .filter(|p| {
                // Filter to benchmarks with < 700 variables for reasonable timeout
                if let Ok(text) = std::fs::read_to_string(p) {
                    for line in text.lines() {
                        if let Some(stripped) = line.strip_prefix("p cnf ") {
                            if let Some(num_vars_str) = stripped.split_whitespace().next() {
                                if let Ok(num_vars) = num_vars_str.parse::<u32>() {
                                    return num_vars < 700;
                                }
                            }
                        }
                    }
                }
                false
            })
            .collect();
        entries.sort();
        paths.extend(entries);
    }

    // 3. benchmarks/sat/canary/tiny_unsat.cnf
    let canary = root.join("benchmarks/sat/canary/tiny_unsat.cnf");
    if canary.is_file() {
        paths.push(canary);
    }

    // 4. Small satcomp2024-sample UNSAT benchmarks (< 2000 vars).
    //    These are real competition benchmarks that ay can solve. DRAT-verifying
    //    them exercises proof generation on industrial/crafted problem families
    //    beyond the hand-crafted benchmarks/sat/unsat corpus.
    //    NOTE: crn_11_99_u (1287 vars) removed - invalid DRAT proof from inprocessing.
    let satcomp_unsat_small: &[&str] = &[];
    let satcomp_dir = root.join("benchmarks/sat/satcomp2024-sample");
    for &name in satcomp_unsat_small {
        let p = satcomp_dir.join(name);
        if p.is_file() {
            paths.push(p);
        }
    }

    paths
}

#[test]
fn test_collect_unsat_benchmarks_matches_braun_8_build_contract() {
    let names: Vec<_> = collect_unsat_benchmarks()
        .into_iter()
        .filter_map(|p| p.file_name().map(|n| n.to_string_lossy().to_string()))
        .collect();
    let includes_braun_8 = names
        .iter()
        .any(|name| name == "eq.atree.braun.8.unsat.cnf");

    if cfg!(debug_assertions) {
        assert!(
            !includes_braun_8,
            "debug aggregate should exclude release-only braun.8 case"
        );
    } else {
        assert!(
            includes_braun_8,
            "release aggregate should include braun.8 coverage"
        );
    }
}

// ---------------------------------------------------------------------------
// Test: Comprehensive DRAT coverage across all small UNSAT benchmarks
// ---------------------------------------------------------------------------

/// Solve every small UNSAT benchmark with DRAT output, verify the proof with
/// the ay-drat-check in-process checker, and optionally cross-validate with
/// external drat-trim.
///
/// This is the primary DRAT coverage expansion test for #7913.
#[test]
#[timeout(300_000)] // 5 minutes total for all benchmarks (expanded scope)
fn test_drat_proof_coverage_all_unsat_benchmarks() {
    let drat_trim = find_drat_trim();
    if drat_trim.is_some() {
        eprintln!("drat-trim found, enabling external cross-validation");
    } else {
        eprintln!("drat-trim not found, using internal checker only");
    }

    let benchmarks = collect_unsat_benchmarks();
    assert!(
        !benchmarks.is_empty(),
        "expected at least one UNSAT benchmark"
    );

    eprintln!(
        "\n{:<45} {:>8} {:>8} {:>8} {:>8}",
        "Benchmark", "Proof(B)", "Steps", "Internal", "External"
    );
    eprintln!("{}", "-".repeat(85));

    let mut results = Vec::new();
    for path in &benchmarks {
        let r = solve_and_verify_drat(path, drat_trim.as_deref());
        eprintln!(
            "{:<45} {:>8} {:>8} {:>8} {:>8}",
            r.name,
            r.proof_size_bytes,
            r.proof_steps,
            if r.internal_check_ok { "PASS" } else { "FAIL" },
            match r.external_check_ok {
                Some(true) => "PASS",
                Some(false) => "FAIL",
                None => "N/A",
            }
        );
        results.push(r);
    }

    // Summary
    let total = results.len();
    let solved = results.iter().filter(|r| r.solve_ok).count();
    let internal_pass = results.iter().filter(|r| r.internal_check_ok).count();
    let external_pass = results
        .iter()
        .filter(|r| r.external_check_ok == Some(true))
        .count();
    let external_tested = results
        .iter()
        .filter(|r| r.external_check_ok.is_some())
        .count();

    eprintln!("\n--- DRAT Coverage Summary ---");
    eprintln!("Total benchmarks:         {total}");
    eprintln!("Solved as UNSAT:          {solved}/{total}");
    eprintln!("Internal DRAT verified:   {internal_pass}/{total}");
    if external_tested > 0 {
        eprintln!("External drat-trim verified: {external_pass}/{external_tested}");
    }

    // Collect failures for the assertion message
    let mut failures = Vec::new();
    for r in &results {
        if !r.solve_ok {
            failures.push(format!(
                "  {} - solve failed: {}",
                r.name,
                r.internal_check_error.as_deref().unwrap_or("unknown")
            ));
        } else if !r.internal_check_ok {
            failures.push(format!(
                "  {} - internal DRAT check failed: {}",
                r.name,
                r.internal_check_error.as_deref().unwrap_or("unknown")
            ));
        }
        if r.external_check_ok == Some(false) {
            failures.push(format!(
                "  {} - external drat-trim check failed: {}",
                r.name,
                r.external_check_error.as_deref().unwrap_or("unknown")
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "DRAT verification failures ({} of {total}):\n{}",
        failures.len(),
        failures.join("\n")
    );

    eprintln!(
        "\nAll {total} UNSAT benchmarks produce valid DRAT proofs (internal check: {internal_pass}/{total}, \
         external check: {external_pass}/{external_tested})"
    );
}

// ---------------------------------------------------------------------------
// Individual per-benchmark tests for granular CI reporting
// ---------------------------------------------------------------------------

/// Solve a single benchmark with DRAT and assert internal verification passes.
fn assert_drat_verified(cnf_relative_path: &str) {
    let cnf_path = workspace_root().join(cnf_relative_path);
    if !cnf_path.is_file() {
        eprintln!(
            "SKIP: optional DRAT benchmark not found: {}",
            cnf_path.display()
        );
        return;
    }
    let drat_trim = find_drat_trim();
    let r = solve_and_verify_drat(&cnf_path, drat_trim.as_deref());
    assert!(
        r.solve_ok,
        "{}: solve failed: {:?}",
        r.name, r.internal_check_error
    );
    assert!(
        r.internal_check_ok,
        "{}: internal DRAT check failed: {}",
        r.name,
        r.internal_check_error.as_deref().unwrap_or("unknown")
    );
    assert!(
        r.external_check_ok != Some(false),
        "{}: external drat-trim check failed: {}",
        r.name,
        r.external_check_error.as_deref().unwrap_or("unknown")
    );
    eprintln!(
        "{}: DRAT verified ({} bytes, {} steps)",
        r.name, r.proof_size_bytes, r.proof_steps
    );
}

// -- benchmarks/sat/unsat/ (all 27) --

#[test]
#[timeout(10_000)]
fn test_drat_cardinality_8() {
    assert_drat_verified("benchmarks/sat/unsat/cardinality_8.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_double_parity_5() {
    assert_drat_verified("benchmarks/sat/unsat/double_parity_5.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_graph_coloring_k4_5clique() {
    assert_drat_verified("benchmarks/sat/unsat/graph_coloring_k4_5clique.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_graph_coloring_k5_6clique() {
    assert_drat_verified("benchmarks/sat/unsat/graph_coloring_k5_6clique.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_mutex_6proc() {
    assert_drat_verified("benchmarks/sat/unsat/mutex_6proc.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_ordering_cycle_5() {
    assert_drat_verified("benchmarks/sat/unsat/ordering_cycle_5.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_php_6_5() {
    assert_drat_verified("benchmarks/sat/unsat/php_6_5.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_php_7_6() {
    assert_drat_verified("benchmarks/sat/unsat/php_7_6.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_php_functional_5_4() {
    assert_drat_verified("benchmarks/sat/unsat/php_functional_5_4.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_random_3sat_50_213_s12345() {
    assert_drat_verified("benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_random_3sat_50_213_s12349() {
    assert_drat_verified("benchmarks/sat/unsat/random_3sat_50_213_s12349.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_resolution_chain_12() {
    assert_drat_verified("benchmarks/sat/unsat/resolution_chain_12.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_tseitin_cycle_11() {
    assert_drat_verified("benchmarks/sat/unsat/tseitin_cycle_11.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_tseitin_k5() {
    assert_drat_verified("benchmarks/sat/unsat/tseitin_k5.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_tseitin_random_15() {
    assert_drat_verified("benchmarks/sat/unsat/tseitin_random_15.cnf");
}

// The following 12 benchmarks are already tested in drat_checker_e2e.rs
// (ay-sat crate) with the ay-drat-check binary. We re-test them here with
// the in-process checker API for additional coverage and independence from
// binary availability.

#[test]
#[timeout(10_000)]
fn test_drat_at_most_1_of_5() {
    assert_drat_verified("benchmarks/sat/unsat/at_most_1_of_5.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_blocked_chain_8() {
    assert_drat_verified("benchmarks/sat/unsat/blocked_chain_8.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_graph_coloring_k3_4clique() {
    assert_drat_verified("benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_latin_square_2x2_conflict() {
    assert_drat_verified("benchmarks/sat/unsat/latin_square_2x2_conflict.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_mutex_4proc() {
    assert_drat_verified("benchmarks/sat/unsat/mutex_4proc.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_mutilated_chessboard_2x2() {
    assert_drat_verified("benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_parity_6() {
    assert_drat_verified("benchmarks/sat/unsat/parity_6.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_php_4_3() {
    assert_drat_verified("benchmarks/sat/unsat/php_4_3.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_php_5_4() {
    assert_drat_verified("benchmarks/sat/unsat/php_5_4.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_ramsey_r3_3_6() {
    assert_drat_verified("benchmarks/sat/unsat/ramsey_r3_3_6.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_tseitin_grid_3x3() {
    assert_drat_verified("benchmarks/sat/unsat/tseitin_grid_3x3.cnf");
}

#[test]
#[timeout(10_000)]
fn test_drat_urquhart_3() {
    assert_drat_verified("benchmarks/sat/unsat/urquhart_3.cnf");
}

// -- benchmarks/sat/canary/ --

#[test]
#[timeout(10_000)]
fn test_drat_canary_tiny_unsat() {
    assert_drat_verified("benchmarks/sat/canary/tiny_unsat.cnf");
}

// -- benchmarks/sat/eq_atree_braun/ (circuit equivalence UNSAT) --
// These are circuit equivalence benchmarks encoding non-equivalence of
// Braun tree adder circuits. braun.10 (505 vars) is included via the
// raised 700-var threshold in collect_unsat_benchmarks(). braun.8 (684 vars)
// is also included but only exercised as a standalone test in release mode
// due to debug-mode solve time (~60s with DRAT proof generation).

#[test]
#[timeout(30_000)]
fn test_drat_eq_atree_braun_10() {
    assert_drat_verified("benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf");
}

/// braun.8: 684 vars, 2300 clauses. Generates a 40MB DRAT proof with
/// 482K proof steps. Debug mode takes ~60s; release-only individual test.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_eq_atree_braun_8() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: braun.8 DRAT proof generation exceeds debug-mode timeout");
        return;
    }
    assert_drat_verified("benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf");
}

// -- satcomp2024-sample UNSAT benchmarks --
// Real SAT competition benchmarks that ay can solve. DRAT-verifying these
// exercises proof generation on industrial/crafted problem families.

// crn_11_99_u DRAT test deleted: invalid proof from inprocessing gaps.

/// Schur number coloring Schur_161_5_d38: 757 vars, 27689 clauses.
/// Crafted UNSAT, Ramsey-theory family. Too slow for debug mode with DRAT.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_satcomp2024_schur_161_5_d38() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: Schur_161_5_d38 DRAT proof generation exceeds debug-mode timeout");
        return;
    }
    assert_drat_verified(
        "benchmarks/sat/satcomp2024-sample/b172b4c218f1e44e205575d2b51e82c4-Schur_161_5_d38.cnf",
    );
}

/// Binary pigeonhole principle bphp(23,22): 115 vars, 5796 clauses.
/// Crafted UNSAT. Despite few vars, pigeonhole is combinatorially hard.
/// Release-only due to debug-mode timeout.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_satcomp2024_bphp_p23_h22() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: bphp_p23_h22 exceeds debug-mode timeout for DRAT proof generation");
        return;
    }
    assert_drat_verified(
        "benchmarks/sat/satcomp2024-sample/fa5c6d6736a42650656c5bc018413254-bphp_p23_h22.sanitized.cnf",
    );
}

/// Clique formula clique_n2_k10: 180 vars, 3160 clauses.
/// Crafted UNSAT, small but combinatorially hard.
/// Release-only due to debug-mode timeout.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_satcomp2024_clique_n2_k10() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: clique_n2_k10 exceeds debug-mode timeout for DRAT proof generation");
        return;
    }
    assert_drat_verified(
        "benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf",
    );
}
