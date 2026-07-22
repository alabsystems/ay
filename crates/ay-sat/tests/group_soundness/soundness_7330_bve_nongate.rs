// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #7330: BVE non-gate×non-gate skip unsoundness.
//!
//! When BVE skips non-gate × non-gate resolvents for a variable with an
//! incomplete gate definition, it can lose information and turn a SAT formula
//! into UNSAT. The `has_incomplete_gate` safety check in resolve.rs (line ~451)
//! prevents this by requiring non-gate × non-gate resolution when both polarity
//! sides have non-gate clauses.
//!
//! CaDiCaL and Kissat both return SAT on stric-bmc-ibm-10. AY must agree.
//!
//! Note: stric-bmc-ibm-10 (59K vars, 323K clauses) exceeds debug-mode timeout.
//! Tests skip in debug mode unless AY_RUN_IBM10_BISECT=1 is set.

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult, Solver};
use ntest::timeout;

const IBM10_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../reference/creusat/tests/cnf-hard/stric-bmc-ibm-10.cnf"
);

fn should_run() -> bool {
    if !cfg!(debug_assertions) {
        return true;
    }
    let enabled = matches!(
        std::env::var("AY_RUN_IBM10_BISECT").as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE")
    );
    if !enabled {
        eprintln!(
            "Skipping ibm10 soundness test in debug mode (59K vars exceeds timeout).\n\
             Set AY_RUN_IBM10_BISECT=1 to enable."
        );
    }
    enabled
}

/// BVE-only configuration must return SAT on stric-bmc-ibm-10.
///
/// This is the specific configuration that triggers false UNSAT when
/// the non-gate×non-gate resolution safety check is removed (#7330).
#[test]
#[timeout(120_000)]
fn ibm10_bve_only_must_be_sat() {
    if !should_run() {
        return;
    }
    let Some(content) = super::common::load_optional_benchmark(IBM10_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let original_clauses = formula.clauses.clone();
    let num_vars = formula.num_vars;
    let mut solver = Solver::new(num_vars);

    // Disable all inprocessing
    super::common::disable_all_inprocessing(&mut solver);

    // Enable only BVE + gate + preprocess (the minimal trigger config)
    solver.set_bve_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_preprocess_enabled(true);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&original_clauses, model, "ibm10-bve-only");
        }
        SatResult::Unsat(_) => {
            panic!(
                "SOUNDNESS BUG (#7330): BVE-only returned UNSAT on known-SAT stric-bmc-ibm-10.\n\
                 This indicates the non-gate×non-gate resolution safety check is broken."
            );
        }
        SatResult::Unknown => {
            let reason = solver.last_unknown_reason();
            eprintln!("ibm10-bve-only: Unknown ({reason:?}) — acceptable (not a soundness bug)");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Full default configuration must also return SAT on stric-bmc-ibm-10.
#[test]
#[timeout(120_000)]
fn ibm10_full_config_must_be_sat() {
    if !should_run() {
        return;
    }
    let Some(content) = super::common::load_optional_benchmark(IBM10_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let original_clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&original_clauses, model, "ibm10-full");
        }
        SatResult::Unsat(_) => {
            panic!(
                "SOUNDNESS BUG (#7330): full config returned UNSAT on known-SAT stric-bmc-ibm-10."
            );
        }
        SatResult::Unknown => {
            let reason = solver.last_unknown_reason();
            eprintln!("ibm10-full: Unknown ({reason:?}) — acceptable (not a soundness bug)");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}
