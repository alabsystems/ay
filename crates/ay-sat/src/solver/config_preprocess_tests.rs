// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

/// `preprocess_once` is used before an incremental MaxSAT loop, whose caller
/// deliberately defers consuming an UNSAT result until the ordinary solve
/// path. Even an UNSAT early exit must therefore disarm preprocessing; rerunning
/// destructive preprocessing over the already-mutated database violates the
/// public one-shot contract.
#[test]
fn preprocess_once_unsat_exit_is_self_disabling() {
    use crate::{Literal, Solver, Variable};

    let mut solver = Solver::new(1);
    let x = Variable::new(0);
    solver.add_clause(vec![Literal::positive(x)]);
    solver.add_clause(vec![Literal::negative(x)]);

    assert!(
        solver.preprocess_once(),
        "contradictory units must be UNSAT"
    );
    assert!(
        !solver.is_preprocess_enabled(),
        "an UNSAT one-shot run must not leave preprocessing armed"
    );
    assert!(
        !solver.preprocess_once(),
        "a completed one-shot run must be inert on a second call"
    );
    assert!(
        solver.solve().into_inner().is_unsat(),
        "deferring the UNSAT result to the normal solve path must remain valid"
    );
}

#[test]
fn local_preprocess_deadline_is_normal_completion_not_solve_stop() {
    use super::*;

    let mut solver = Solver::new(1);
    solver.cold.preprocess_deadline = Some(ay_core::time::Instant::now());

    assert!(solver.preprocess_timed_out());
    assert_eq!(
        solver.classify_preprocess_outcome(false, &|| false),
        PreprocessOutcome::Complete
    );
}
