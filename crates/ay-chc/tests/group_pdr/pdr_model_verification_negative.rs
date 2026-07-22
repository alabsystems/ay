// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

#[path = "../common/smt_inputs.rs"]
mod smt_inputs;

use ay_chc::{testing, ChcExpr, ChcParser, PdrConfig, PdrResult, PredicateInterpretation};
use ntest::timeout;
use smt_inputs::SAFE_INPUT;

/// Prover regression test: `verify_model()` must reject corrupted solver models.
///
/// This ensures proof verification is not vacuous and catches invalid invariants.
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn verify_model_rejects_corrupted_solver_model() {
    let problem = ChcParser::parse(SAFE_INPUT).unwrap();

    let mut solver = testing::new_pdr_solver(problem.clone(), PdrConfig::default());
    let result = solver.solve();

    let PdrResult::Safe(model) = result else {
        panic!("expected Safe, got {result:?}");
    };
    assert!(!model.is_empty(), "expected non-empty model");

    // Sanity check: the unmodified model must verify.
    let mut verifier = testing::new_pdr_solver(problem.clone(), PdrConfig::default());
    assert!(
        verifier.verify_model(&model),
        "expected returned model to satisfy verify_model()"
    );

    // Corrupt one predicate's interpretation to violate the CHC clauses.
    let mut corrupted = model.clone();
    let (pred, interp) = model.iter().next().expect("model is non-empty");
    corrupted.set(
        *pred,
        PredicateInterpretation::new(interp.vars.clone(), ChcExpr::Bool(false)),
    );

    let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
    assert!(
        !verifier.verify_model(&corrupted),
        "expected verify_model() to reject corrupted model"
    );
}
