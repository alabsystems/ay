// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #7929: forward DRUP checker assertion failure.
//!
//! The inline forward DRUP checker (debug builds only) panicked with
//! "derived clause not RUP implied: [227]" during proof-mode BVE elimination.
//! Root cause: BVE backward subsumption emitted `Derived` proof steps for
//! strengthened clauses that were not RUP-derivable (the subsumer clause's
//! proof chain was incomplete relative to the forward checker's clause DB).
//!
//! Fixed by removing inline backward subsumption during BVE elimination
//! (commit 9ef4b5141, #7917). This test verifies the fix by running each
//! inprocessing feature in isolation with DRAT proof output on all
//! matrix_drat UNSAT benchmarks. In debug builds, the solver's inline
//! forward checker verifies every derived clause is RUP-implied.

use ay_sat::{parse_dimacs, ProofOutput, SatResult, Solver};

/// All features that support DRAT proof emission (excludes sweep).
const DRAT_FEATURES: &[&str] = &[
    "vivify",
    "subsume",
    "probe",
    "shrink",
    "bve",
    "bce",
    "transred",
    "htr",
    "condition",
    "congruence",
    "decompose",
    "factor",
    "backbone",
];

/// Benchmarks from the oracle matrix with matrix_drat=true.
const MATRIX_DRAT_BENCHMARKS: &[(&str, &str)] = &[
    (
        "barrel6",
        "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/cmu-bmc-barrel6.cnf",
    ),
    ("php_4_3", "benchmarks/sat/unsat/php_4_3.cnf"),
    ("ramsey_r3_3_6", "benchmarks/sat/unsat/ramsey_r3_3_6.cnf"),
    (
        "uuf250-01",
        "reference/creusat/tests/satlib/UUF250.1065.100/uuf250-01.cnf",
    ),
];

fn enable_feature(solver: &mut Solver, feature: &str) {
    match feature {
        "vivify" => solver.set_vivify_enabled(true),
        "subsume" => solver.set_subsume_enabled(true),
        "probe" => solver.set_probe_enabled(true),
        "shrink" => solver.set_shrink_enabled(true),
        "bve" => solver.set_bve_enabled(true),
        "bce" => solver.set_bce_enabled(true),
        "transred" => solver.set_transred_enabled(true),
        "htr" => solver.set_htr_enabled(true),
        "condition" => solver.set_condition_enabled(true),
        "congruence" => solver.set_congruence_enabled(true),
        "decompose" => solver.set_decompose_enabled(true),
        "factor" => solver.set_factor_enabled(true),
        "backbone" => solver.set_backbone_enabled(true),
        _ => panic!("unknown feature: {feature}"),
    }
}

fn test_feature_drat(feature: &str, cnf: &str, label: &str) {
    let formula = parse_dimacs(cnf).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    super::common::disable_all_inprocessing(&mut solver);
    enable_feature(&mut solver, feature);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "REGRESSION #7929 [{feature}/{label}]: expected UNSAT with proof-mode solve"
    );
}

fn load_benchmark(rel_path: &str) -> Option<String> {
    let path = super::common::workspace_root().join(rel_path);
    match std::fs::read_to_string(&path) {
        Ok(cnf) => Some(cnf),
        Err(_) => {
            eprintln!("SKIP: benchmark not found at {}", path.display());
            None
        }
    }
}

// ── Per-benchmark regression tests ───────────────────────────────
// Each test iterates over all DRAT-verified features on one benchmark.

#[test]
fn regression_7929_barrel6_forward_checker() {
    let Some(cnf) = load_benchmark(MATRIX_DRAT_BENCHMARKS[0].1) else {
        return;
    };
    for feature in DRAT_FEATURES {
        test_feature_drat(feature, &cnf, "barrel6");
    }
}

#[test]
fn regression_7929_php43_forward_checker() {
    let Some(cnf) = load_benchmark(MATRIX_DRAT_BENCHMARKS[1].1) else {
        return;
    };
    for feature in DRAT_FEATURES {
        test_feature_drat(feature, &cnf, "php_4_3");
    }
}

#[test]
fn regression_7929_ramsey_forward_checker() {
    let Some(cnf) = load_benchmark(MATRIX_DRAT_BENCHMARKS[2].1) else {
        return;
    };
    for feature in DRAT_FEATURES {
        test_feature_drat(feature, &cnf, "ramsey_r3_3_6");
    }
}

#[test]
fn regression_7929_uuf250_forward_checker() {
    let Some(cnf) = load_benchmark(MATRIX_DRAT_BENCHMARKS[3].1) else {
        return;
    };
    for feature in DRAT_FEATURES {
        test_feature_drat(feature, &cnf, "uuf250-01");
    }
}
