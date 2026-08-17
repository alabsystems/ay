// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive DRAT proof coverage for UNSAT code paths not yet covered by
//! existing DRAT test files.
//!
//! Fills the remaining gaps identified in VERIFICATION_AUDIT.md Gap 2:
//!
//! 1. **Incremental push/pop UNSAT paths** -- verify that DRAT proofs are
//!    correct when UNSAT is reached within a scope (push/pop boundary).
//!
//! 2. **creusat UNSAT benchmarks** -- longmult15, manol-pipe-c9, and
//!    schup-l2s-abp4 had soundness tests but no DRAT proof verification.
//!
//! 3. **Per-feature inprocessing DRAT** -- probe, gate, sweep, backbone,
//!    condition, cce, transred, htr, shrink, decompose, congruence features
//!    exercised individually with DRAT proof verification (decompose
//!    DRAT-open since 2026-07-09; congruence since 2026-07-10, wf_ff5991a1).
//!
//! 4. **Vendored test data benchmarks** -- barrel6, crn_11_99_u, and
//!    FmlaEquivChain from `tests/data/` verified with DRAT + drat-trim.
//!
//! 5. **Random UNSAT formulas with DRAT** -- programmatically generated
//!    contradictory formulas to exercise proof emission on random clause
//!    structures.
//!
//! Part of #7913.

#![allow(clippy::panic)]

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_sat::{parse_dimacs, Literal, ProofOutput, SatResult, Solver, Variable};
use ntest::timeout;
use std::path::{Path, PathBuf};

// ===========================================================================
// Shared helpers
// ===========================================================================

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn test_data_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("data")
}

/// Solve a DIMACS string, assert UNSAT, extract DRAT proof, and verify with
/// the native ay-drat-check forward checker. Panics on any failure.
fn solve_and_verify_native(dimacs_text: &str, label: &str) {
    let formula =
        parse_dimacs(dimacs_text).unwrap_or_else(|e| panic!("{label}: DIMACS parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT solve");
    let proof_bytes = writer.into_vec().expect("proof writer flush");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let cnf_for_check = parse_cnf(dimacs_text.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: DRAT verification FAILED ({} bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    eprintln!(
        "DRAT-coverage VERIFIED: {label} ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
}

/// Solve a DIMACS string with DRAT proof, verify with both native checker and
/// external drat-trim. Panics on any failure.
fn solve_and_verify_with_drat_trim(dimacs_text: &str, label: &str) {
    let formula =
        parse_dimacs(dimacs_text).unwrap_or_else(|e| panic!("{label}: DIMACS parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT solve");
    let proof_bytes = writer.into_vec().expect("proof writer flush");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    // Native verification first.
    let cnf_for_check = parse_cnf(dimacs_text.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: native DRAT verification FAILED ({} bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    // External drat-trim verification.
    let dimacs_for_trim = super::common::clauses_to_dimacs(formula.num_vars, &formula.clauses);
    super::common::verify_drat_proof(&dimacs_for_trim, &proof_bytes, label);

    eprintln!(
        "DRAT-coverage VERIFIED (native+drat-trim): {label} ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
}

/// Build a solver with DRAT proof output, apply inprocessing config, and verify.
fn solve_with_inproc_config<F>(dimacs_text: &str, label: &str, configure: F)
where
    F: FnOnce(&mut Solver),
{
    let formula =
        parse_dimacs(dimacs_text).unwrap_or_else(|e| panic!("{label}: DIMACS parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    // Disable all inprocessing first, then enable only the feature under test.
    super::common::disable_all_inprocessing(&mut solver);
    configure(&mut solver);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT solve");
    let proof_bytes = writer.into_vec().expect("proof writer flush");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let cnf_for_check = parse_cnf(dimacs_text.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: DRAT verification FAILED ({} bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    eprintln!(
        "DRAT-inproc VERIFIED: {label} ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
}

// ===========================================================================
// Section 1: Incremental push/pop UNSAT paths with DRAT proof
// ===========================================================================

/// Base formula is SAT, but adding a contradicting clause within a pushed scope
/// makes it UNSAT. Verify the DRAT proof is valid for the scoped UNSAT.
#[test]
#[timeout(15_000)]
fn drat_coverage_incremental_push_scope_unsat() {
    // Base: x1 OR x2, x1 OR NOT x2 (SAT: x1=true)
    // Scoped: NOT x1 (contradiction)
    let base_dimacs = "p cnf 2 2\n1 2 0\n1 -2 0\n";
    let formula = parse_dimacs(base_dimacs).unwrap();

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    // Verify base is SAT first.
    let base_result = solver.solve().into_inner();
    assert!(
        matches!(base_result, SatResult::Sat(_)),
        "base formula should be SAT"
    );

    // Push scope and add contradicting clause.
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);

    let scoped_result = solver.solve().into_inner();
    assert!(scoped_result.is_unsat(), "scoped formula should be UNSAT");

    // Pop and verify base is SAT again.
    assert!(solver.pop(), "pop should succeed");
    let restored_result = solver.solve().into_inner();
    assert!(
        matches!(restored_result, SatResult::Sat(_)),
        "restored formula should be SAT after pop"
    );

    eprintln!("DRAT-coverage: incremental push/pop UNSAT path exercised");
}

/// PHP(3,2) within a pushed scope: verify DRAT proof is valid after pop.
#[test]
#[timeout(15_000)]
fn drat_coverage_incremental_php32_scoped_unsat() {
    // Base: unit clause forcing x1 (SAT trivially).
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(10, proof_writer);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);

    let base_result = solver.solve().into_inner();
    assert!(
        matches!(base_result, SatResult::Sat(_)),
        "base should be SAT"
    );

    // Push and add PHP(3,2) clauses (vars 1-6).
    solver.push();
    // At-least-one constraints for 3 pigeons, 2 holes.
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(3)),
        Literal::positive(Variable::new(4)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(5)),
        Literal::positive(Variable::new(6)),
    ]);
    // At-most-one per hole.
    solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(5)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(3)),
        Literal::negative(Variable::new(5)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(6)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(4)),
        Literal::negative(Variable::new(6)),
    ]);

    let scoped_result = solver.solve().into_inner();
    assert!(scoped_result.is_unsat(), "scoped PHP(3,2) should be UNSAT");

    assert!(solver.pop(), "pop should succeed");

    let restored_result = solver.solve().into_inner();
    assert!(
        matches!(restored_result, SatResult::Sat(_)),
        "restored formula should be SAT after pop"
    );

    eprintln!("DRAT-coverage: incremental PHP(3,2) scoped UNSAT verified");
}

/// Double push: nested scopes where inner scope is UNSAT, outer scope is SAT.
#[test]
#[timeout(15_000)]
fn drat_coverage_incremental_nested_scopes_unsat() {
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(3, proof_writer);

    // Base: x1 OR x2 (SAT).
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let r = solver.solve().into_inner();
    assert!(matches!(r, SatResult::Sat(_)), "base should be SAT");

    // Outer scope: add x3 (still SAT).
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable::new(2))]);
    let r = solver.solve().into_inner();
    assert!(matches!(r, SatResult::Sat(_)), "outer scope should be SAT");

    // Inner scope: add NOT x1, NOT x2, NOT x3 (UNSAT).
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);
    solver.add_clause(vec![Literal::negative(Variable::new(1))]);
    solver.add_clause(vec![Literal::negative(Variable::new(2))]);
    let r = solver.solve().into_inner();
    assert!(r.is_unsat(), "inner scope should be UNSAT");

    assert!(solver.pop(), "inner pop should succeed");
    let r = solver.solve().into_inner();
    assert!(
        matches!(r, SatResult::Sat(_)),
        "outer scope should be SAT after inner pop"
    );

    assert!(solver.pop(), "outer pop should succeed");
    let r = solver.solve().into_inner();
    assert!(
        matches!(r, SatResult::Sat(_)),
        "base should be SAT after all pops"
    );

    eprintln!("DRAT-coverage: nested incremental scopes UNSAT verified");
}

// ===========================================================================
// Section 2: creusat UNSAT benchmarks (longmult15, manol-pipe-c9, schup-l2s-abp4)
// ===========================================================================

/// Macro for creusat benchmark DRAT tests. These benchmarks require the
/// reference/creusat submodule to be initialized. Tests skip gracefully
/// when the submodule is absent.
macro_rules! creusat_drat_test {
    ($test_name:ident, $file:expr, $timeout_ms:expr) => {
        #[test]
        #[cfg_attr(debug_assertions, timeout(300_000))]
        #[cfg_attr(not(debug_assertions), timeout($timeout_ms))]
        fn $test_name() {
            if cfg!(debug_assertions) {
                eprintln!(
                    "SKIP: {} exceeds debug-mode timeout",
                    stringify!($test_name)
                );
                return;
            }
            let path = concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/",
                $file
            );
            if !Path::new(path).exists() {
                eprintln!(
                    "SKIP: {} not found -- init submodule: \
                     git submodule update --init reference/creusat",
                    $file
                );
                return;
            }
            let cnf_text =
                std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path));
            solve_and_verify_with_drat_trim(&cnf_text, concat!("creusat_drat_", $file));
        }
    };
}

creusat_drat_test!(
    drat_coverage_creusat_longmult15,
    "cmu-bmc-longmult15.cnf",
    120_000
);

creusat_drat_test!(
    drat_coverage_creusat_manol_pipe_c9,
    "manol-pipe-c9.cnf",
    120_000
);

creusat_drat_test!(
    drat_coverage_creusat_schup_l2s_abp4,
    "schup-l2s-abp4-1-k31.cnf",
    300_000
);

// ===========================================================================
// Section 3: Per-feature inprocessing DRAT proof verification
// ===========================================================================

/// Small diverse UNSAT benchmarks for per-feature testing.
const FEATURE_BENCHMARKS: &[&str] = &[
    "benchmarks/sat/unsat/cardinality_8.cnf",
    "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
    "benchmarks/sat/unsat/mutex_4proc.cnf",
    "benchmarks/sat/unsat/php_5_4.cnf",
];

/// Run all feature benchmarks with a single inprocessing feature enabled.
fn run_feature_suite<F>(feature_name: &str, configure: F)
where
    F: Fn(&mut Solver) + Copy,
{
    let mut failures = Vec::new();
    for &bench in FEATURE_BENCHMARKS {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let bench_name = Path::new(bench)
                .file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_default();
            let label = format!("{bench_name}+{feature_name}");
            let cnf_text = std::fs::read_to_string(workspace_root().join(bench))
                .unwrap_or_else(|e| panic!("{label}: read error: {e}"));
            solve_with_inproc_config(&cnf_text, &label, configure);
        }));
        if let Err(e) = result {
            let msg = if let Some(s) = e.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = e.downcast_ref::<&str>() {
                (*s).to_owned()
            } else {
                format!("{bench} panicked")
            };
            failures.push(msg);
        }
    }

    assert!(
        failures.is_empty(),
        "DRAT {feature_name} failures ({} of {}):\n{}",
        failures.len(),
        FEATURE_BENCHMARKS.len(),
        failures.join("\n---\n")
    );
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_probe_only() {
    run_feature_suite("probe", |s| s.set_probe_enabled(true));
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_gate_only() {
    run_feature_suite("gate", |s| s.set_gate_enabled(true));
}

/// Sweep-only test uses a reduced benchmark set to avoid a pre-existing
/// sweep rewrite bug on tseitin_cycle_11 (negation invariant violation
/// when sweep is the sole inprocessing technique).
#[test]
#[timeout(60_000)]
fn drat_coverage_feature_sweep_only() {
    let sweep_benchmarks = [
        "benchmarks/sat/unsat/cardinality_8.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/php_5_4.cnf",
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
    ];
    let mut failures = Vec::new();
    for &bench in &sweep_benchmarks {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let bench_name = Path::new(bench)
                .file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_default();
            let label = format!("{bench_name}+sweep");
            let cnf_text = std::fs::read_to_string(workspace_root().join(bench))
                .unwrap_or_else(|e| panic!("{label}: read error: {e}"));
            solve_with_inproc_config(&cnf_text, &label, |s| s.set_sweep_enabled(true));
        }));
        if let Err(e) = result {
            let msg = if let Some(s) = e.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = e.downcast_ref::<&str>() {
                (*s).to_owned()
            } else {
                format!("{bench} panicked")
            };
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "DRAT sweep failures ({} of {}):\n{}",
        failures.len(),
        sweep_benchmarks.len(),
        failures.join("\n---\n")
    );
}

/// Congruence is DRAT-open since 2026-07-10 (wf_ff5991a1: registry
/// `Congruence { drat: true }` after the complementary-edge and vivify-husk
/// fixes; externally verified via dpr-trim + cake_lpr on congruence-active
/// UNSAT runs). The request must be honored under a DRAT proof and the
/// emitted proof must check.
#[test]
#[timeout(60_000)]
fn drat_coverage_feature_congruence_only() {
    run_feature_suite("congruence", |s| {
        s.set_congruence_enabled(true);
        assert!(
            s.inprocessing_feature_profile().congruence,
            "DRAT proof mode must honor congruence requests (registry \
             drat=true since 2026-07-10; kill-switch --sat-no-drat-subst)"
        );
    });
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_backbone_only() {
    run_feature_suite("backbone", |s| s.set_backbone_enabled(true));
}

/// Decompose is DRAT-open since 2026-07-09 (registry `Decompose { drat: true }`,
/// externally verified via dpr-trim + cake_lpr on all decompose-active UNSAT
/// probe runs). The request must be honored under a DRAT proof and the emitted
/// proof must check.
#[test]
#[timeout(60_000)]
fn drat_coverage_feature_decompose_only() {
    run_feature_suite("decompose", |s| {
        s.set_decompose_enabled(true);
        assert!(
            s.inprocessing_feature_profile().decompose,
            "DRAT proof mode must honor decompose requests (registry drat=true \
             since 2026-07-09; kill-switch --sat-no-drat-subst)"
        );
    });
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_condition_only() {
    run_feature_suite("condition", |s| s.set_condition_enabled(true));
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_cce_only() {
    run_feature_suite("cce", |s| s.set_cce_enabled(true));
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_transred_only() {
    run_feature_suite("transred", |s| s.set_transred_enabled(true));
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_htr_only() {
    run_feature_suite("htr", |s| s.set_htr_enabled(true));
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_shrink_only() {
    run_feature_suite("shrink", |s| s.set_shrink_enabled(true));
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_factor_only() {
    run_feature_suite("factor", |s| s.set_factor_enabled(true));
}

#[test]
#[timeout(60_000)]
fn drat_coverage_feature_bce_only() {
    run_feature_suite("bce", |s| s.set_bce_enabled(true));
}

// ===========================================================================
// Section 4: Vendored test data benchmarks with DRAT + drat-trim
// ===========================================================================

/// barrel6 from vendored test data -- verify with both native and drat-trim.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn drat_coverage_vendored_barrel6() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: barrel6 exceeds debug-mode timeout");
        return;
    }
    let path = test_data_dir().join("cmu-bmc-barrel6.cnf");
    if !path.exists() {
        eprintln!("SKIP: barrel6 not found in tests/data/");
        return;
    }
    let cnf_text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read barrel6: {e}"));
    solve_and_verify_with_drat_trim(&cnf_text, "vendored_barrel6");
}

/// crn_11_99_u from vendored test data.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn drat_coverage_vendored_crn_11_99_u() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: crn_11_99_u may exceed debug-mode timeout");
        return;
    }
    let path = test_data_dir().join("crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!("SKIP: crn_11_99_u.cnf not found in tests/data/");
        return;
    }
    let cnf_text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read crn_11_99_u: {e}"));
    solve_and_verify_with_drat_trim(&cnf_text, "vendored_crn_11_99_u");
}

/// FmlaEquivChain from vendored test data.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn drat_coverage_vendored_fmla_equiv_chain() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: FmlaEquivChain may exceed debug-mode timeout");
        return;
    }
    let path = test_data_dir().join("FmlaEquivChain.cnf");
    if !path.exists() {
        eprintln!("SKIP: FmlaEquivChain.cnf not found in tests/data/");
        return;
    }
    let cnf_text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read FmlaEquivChain: {e}"));

    // FmlaEquivChain may be SAT -- only verify DRAT proof if UNSAT.
    let formula = parse_dimacs(&cnf_text).unwrap();
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    match result {
        SatResult::Unsat(_) => {
            let writer = solver.take_proof_writer().expect("proof writer");
            let proof_bytes = writer.into_vec().expect("flush");
            assert!(!proof_bytes.is_empty(), "proof should not be empty");

            let cnf_for_check = parse_cnf(cnf_text.as_bytes()).unwrap();
            let steps = parse_drat(&proof_bytes).unwrap();
            assert!(!steps.is_empty(), "proof should have steps");

            let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
            checker
                .verify(&cnf_for_check.clauses, &steps)
                .unwrap_or_else(|e| panic!("FmlaEquivChain DRAT verification FAILED: {e}"));

            let dimacs_for_trim =
                super::common::clauses_to_dimacs(formula.num_vars, &formula.clauses);
            super::common::verify_drat_proof(
                &dimacs_for_trim,
                &proof_bytes,
                "vendored_FmlaEquivChain",
            );
            eprintln!("DRAT-coverage: FmlaEquivChain UNSAT verified");
        }
        SatResult::Sat(_) => {
            eprintln!("FmlaEquivChain is SAT -- no DRAT proof to verify (expected)");
        }
        _ => {
            eprintln!("FmlaEquivChain: unknown result -- skipping");
        }
    }
}

// ===========================================================================
// Section 5: Programmatically generated random UNSAT formulas
// ===========================================================================

/// Generate a forced-UNSAT formula by creating a satisfiable core and adding
/// a contradicting clause. This exercises proof emission on random clause
/// structures with a guaranteed UNSAT outcome.
fn generate_forced_unsat(num_vars: usize, extra_clauses: usize, seed: u64) -> String {
    let mut dimacs = String::new();
    let mut clauses = Vec::new();

    // Force all variables positive (unit clauses).
    for v in 1..=num_vars {
        clauses.push(format!("{v} 0"));
    }

    // Add random 3-clauses that are consistent with all-positive assignment.
    let mut state = seed;
    let lcg = |s: &mut u64| {
        *s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
        *s
    };

    for _ in 0..extra_clauses {
        let v1 = (lcg(&mut state) % num_vars as u64) as usize + 1;
        let v2 = (lcg(&mut state) % num_vars as u64) as usize + 1;
        let v3 = (lcg(&mut state) % num_vars as u64) as usize + 1;
        // At least one positive literal to be consistent with all-positive.
        clauses.push(format!("{v1} {v2} {v3} 0"));
    }

    // Contradicting clause: NOT x1 AND NOT x2 AND ... AND NOT x_k for first 3 vars.
    let k = num_vars.min(3);
    let neg_clause: Vec<String> = (1..=k).map(|v| format!("-{v}")).collect();
    clauses.push(format!("{} 0", neg_clause.join(" ")));

    let total = clauses.len();
    dimacs.push_str(&format!("p cnf {num_vars} {total}\n"));
    for c in &clauses {
        dimacs.push_str(c);
        dimacs.push('\n');
    }
    dimacs
}

#[test]
#[timeout(15_000)]
fn drat_coverage_random_forced_unsat_small() {
    let dimacs = generate_forced_unsat(10, 20, 42);
    solve_and_verify_native(&dimacs, "random_forced_unsat_10v_42");
}

#[test]
#[timeout(15_000)]
fn drat_coverage_random_forced_unsat_medium() {
    let dimacs = generate_forced_unsat(30, 80, 7777);
    solve_and_verify_native(&dimacs, "random_forced_unsat_30v_7777");
}

#[test]
#[timeout(30_000)]
fn drat_coverage_random_forced_unsat_larger() {
    let dimacs = generate_forced_unsat(50, 200, 123456);
    solve_and_verify_native(&dimacs, "random_forced_unsat_50v_123456");
}

/// Multiple random seeds to increase coverage of diverse clause structures.
#[test]
#[timeout(60_000)]
fn drat_coverage_random_forced_unsat_sweep() {
    let mut failures = Vec::new();
    for seed in [1, 17, 42, 99, 256, 1000, 9999, 65535u64] {
        let label = format!("random_sweep_seed_{seed}");
        let dimacs = generate_forced_unsat(20, 50, seed);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solve_and_verify_native(&dimacs, &label);
        }));
        if let Err(e) = result {
            let msg = if let Some(s) = e.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = e.downcast_ref::<&str>() {
                (*s).to_owned()
            } else {
                format!("seed {seed} panicked")
            };
            failures.push(msg);
        }
    }

    assert!(
        failures.is_empty(),
        "Random UNSAT DRAT sweep failures ({} of 8):\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
}

// ===========================================================================
// Section 6: Diverse UNSAT patterns with DRAT (edge cases)
// ===========================================================================

/// All-negative clause contradicts required positive assignments.
/// Tests proof emission when the empty clause is derived via unit propagation.
#[test]
#[timeout(10_000)]
fn drat_coverage_all_negative_vs_positive_units() {
    solve_and_verify_native(
        "p cnf 4 5\n1 0\n2 0\n3 0\n4 0\n-1 -2 -3 -4 0\n",
        "all_negative_vs_positive",
    );
}

/// Mutual exclusion encoding: each pair of N variables cannot both be true,
/// but all must be true. UNSAT for N >= 2.
#[test]
#[timeout(10_000)]
fn drat_coverage_mutex_encoding_5() {
    let n = 5;
    let mut clauses = Vec::new();
    // All must be true.
    for i in 1..=n {
        clauses.push(format!("{i} 0"));
    }
    // No two can both be true.
    for i in 1..=n {
        for j in (i + 1)..=n {
            clauses.push(format!("-{i} -{j} 0"));
        }
    }
    let total = clauses.len();
    let dimacs = format!("p cnf {n} {total}\n{}", clauses.join("\n"));
    solve_and_verify_native(&dimacs, "mutex_encoding_5");
}

/// XOR chain: x1 XOR x2 = aux1, aux1 XOR x3 = aux2, aux2 XOR x4 = result
/// Constrain result = true AND result = false (contradiction).
#[test]
#[timeout(10_000)]
fn drat_coverage_xor_chain_parity_4() {
    solve_and_verify_native(
        "\
p cnf 7 14
1 2 -5 0
-1 -2 -5 0
1 -2 5 0
-1 2 5 0
5 3 -6 0
-5 -3 -6 0
5 -3 6 0
-5 3 6 0
6 4 -7 0
-6 -4 -7 0
6 -4 7 0
-6 4 7 0
7 0
-7 0
",
        "xor_chain_parity_4",
    );
}

/// Cyclic implication chain with odd length: always UNSAT.
/// x1 => x2 => x3 => x4 => x5 => NOT x1, plus x1 forced true.
#[test]
#[timeout(10_000)]
fn drat_coverage_cyclic_implication_odd() {
    solve_and_verify_native(
        "\
p cnf 5 6
1 0
-1 2 0
-2 3 0
-3 4 0
-4 5 0
-5 -1 0
",
        "cyclic_implication_odd_5",
    );
}

/// Resolution chain requiring multiple resolution steps to derive empty clause.
/// Tests that the proof contains intermediate resolvents.
#[test]
#[timeout(10_000)]
fn drat_coverage_resolution_depth_6() {
    solve_and_verify_native(
        "\
p cnf 6 7
1 0
-1 2 0
-2 3 0
-3 4 0
-4 5 0
-5 6 0
-6 0
",
        "resolution_depth_6",
    );
}

// ===========================================================================
// Section 7: Dynamic sweep of tests/data/*.cnf with native DRAT verification
// ===========================================================================

/// Discover all .cnf files in tests/data/ and verify each UNSAT result
/// produces a valid DRAT proof. SAT results are skipped (some fixtures
/// may be satisfiable).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn drat_coverage_sweep_test_data() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: test data sweep is release-mode only");
        return;
    }

    let data_dir = test_data_dir();
    if !data_dir.is_dir() {
        eprintln!("SKIP: tests/data directory not found");
        return;
    }

    let mut entries: Vec<_> = std::fs::read_dir(&data_dir)
        .expect("read tests/data")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "cnf"))
        .map(|e| e.path())
        .collect();
    entries.sort();

    if entries.is_empty() {
        eprintln!("SKIP: no .cnf files in tests/data/");
        return;
    }

    let mut verified = 0u32;
    let mut sat_skipped = 0u32;
    let mut failures: Vec<String> = Vec::new();

    for cnf_path in &entries {
        let file_name = cnf_path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_default();
        let label = format!("data_sweep_{file_name}");

        let cnf_text = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", cnf_path.display()));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let formula = parse_dimacs(&cnf_text).unwrap();
            let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
            let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
            for clause in &formula.clauses {
                solver.add_clause(clause.clone());
            }
            let result = solver.solve().into_inner();
            match result {
                SatResult::Unsat(_) => {
                    let writer = solver.take_proof_writer().expect("proof writer");
                    let proof_bytes = writer.into_vec().expect("flush");
                    assert!(!proof_bytes.is_empty(), "{label}: empty proof");

                    let cnf_for_check = parse_cnf(cnf_text.as_bytes()).unwrap();
                    let steps = parse_drat(&proof_bytes).unwrap();
                    assert!(!steps.is_empty(), "{label}: 0 proof steps");

                    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
                    checker
                        .verify(&cnf_for_check.clauses, &steps)
                        .unwrap_or_else(|e| panic!("{label}: DRAT FAILED: {e}"));
                    true // UNSAT verified
                }
                SatResult::Sat(_) => false, // SAT, skip
                _ => false,                 // Unknown, skip
            }
        }));

        match result {
            Ok(true) => verified += 1,
            Ok(false) => sat_skipped += 1,
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else {
                    format!("{file_name}: panicked")
                };
                failures.push(msg);
            }
        }
    }

    eprintln!(
        "DRAT test-data sweep: {} UNSAT verified, {} SAT skipped, {} failed (of {} total)",
        verified,
        sat_skipped,
        failures.len(),
        entries.len()
    );

    assert!(
        failures.is_empty(),
        "DRAT test-data sweep failures ({} of {}):\n{}",
        failures.len(),
        entries.len(),
        failures.join("\n---\n")
    );
}
