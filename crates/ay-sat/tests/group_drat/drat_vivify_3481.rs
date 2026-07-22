// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused reproduction for #3481: DRAT proof verification fails for vivification
//! on cmu-bmc-barrel6.

use super::common::{read_barrel6, PHP43_DIMACS};
use ay_sat::{parse_dimacs, ProofOutput, Solver};
use ntest::timeout;

fn stress_formula_dimacs() -> String {
    if cfg!(debug_assertions) {
        PHP43_DIMACS.to_owned()
    } else {
        read_barrel6().unwrap_or_else(|| PHP43_DIMACS.to_owned())
    }
}

/// Reproduction for #3481: vivification DRAT proof must verify on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_vivify_barrel6() {
    verify_feature_drat("vivify", |s| s.set_vivify_enabled(true));
}

/// Helper: solve with one feature enabled on a DIMACS string and verify DRAT proof.
fn verify_feature_drat_on_dimacs(feature_name: &str, cnf: &str, enable: fn(&mut Solver)) {
    let formula = parse_dimacs(cnf).expect("parse dimacs");

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    super::common::disable_all_inprocessing(&mut solver);
    enable(&mut solver);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "formula must be UNSAT with {feature_name}"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("flush proof writer");
    super::common::verify_drat_proof(cnf, &proof_bytes, feature_name);
}

/// Solve with one feature enabled and verify DRAT proof.
/// Uses barrel6 in release mode; PHP43 in debug mode (parallel barrel6 solves
/// under debug-build overhead exceed 180s timeouts non-deterministically).
fn verify_feature_drat(feature_name: &str, enable: fn(&mut Solver)) {
    let cnf = stress_formula_dimacs();
    verify_feature_drat_on_dimacs(feature_name, &cnf, enable);
}

/// DRAT proof for subsumption in isolation.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_subsume_barrel6() {
    verify_feature_drat("subsume", |s| s.set_subsume_enabled(true));
}

/// DRAT proof for probe in isolation.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_probe_barrel6() {
    verify_feature_drat("probe", |s| s.set_probe_enabled(true));
}

/// DRAT proof for shrink in isolation.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_shrink_barrel6() {
    verify_feature_drat("shrink", |s| s.set_shrink_enabled(true));
}

/// DRAT proof for BCE in isolation.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_bce_barrel6() {
    if cfg!(debug_assertions) {
        verify_feature_drat_on_dimacs("bce", PHP43_DIMACS, |s| s.set_bce_enabled(true));
    } else {
        verify_feature_drat("bce", |s| s.set_bce_enabled(true));
    }
}

/// DRAT proof for transred in isolation.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_transred_barrel6() {
    if cfg!(debug_assertions) {
        verify_feature_drat_on_dimacs("transred", PHP43_DIMACS, |s| s.set_transred_enabled(true));
    } else {
        verify_feature_drat("transred", |s| s.set_transred_enabled(true));
    }
}

/// DRAT proof for HTR in isolation.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_htr_barrel6() {
    verify_feature_drat("htr", |s| s.set_htr_enabled(true));
}

/// Baseline: bare CDCL DRAT proof must verify (proves infra works).
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_baseline_barrel6() {
    verify_feature_drat("baseline", |_| {});
}
