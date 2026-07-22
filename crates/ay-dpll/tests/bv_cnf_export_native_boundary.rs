// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native-API boundary tests for the process-wide single-query BV CNF export.

use ay_dpll::api::{Logic, Solver, SolverError, Sort, Tactic};
use ay_dpll::ExecutorError;

fn assert_artifact_error<T>(result: Result<T, SolverError>, operation: &str) {
    match result {
        Err(SolverError::ExecutorError(ExecutorError::ArtifactExport(_))) => {}
        Err(error) => panic!("{operation} returned the wrong error: {error}"),
        Ok(_) => panic!("{operation} unexpectedly succeeded"),
    }
}

#[test]
fn fallible_solves_and_composite_operations_preserve_the_single_query_contract() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let dump = temp.path().join("native.cnf");
    std::env::set_var("AY_DUMP_BV_CNF", &dump);
    std::env::remove_var("AY_DUMP_BV_DIMACS");

    // Fallible entrypoints must preserve the typed export failure instead of
    // reporting a successful `Ok(Unknown)` for an unsupported query.
    let mut lia = Solver::new(Logic::QfLia);
    let int_x = lia.declare_const("int_x", Sort::Int);
    let zero = lia.int_const(0);
    let positive = lia.gt(int_x, zero);
    lia.assert_term(positive);
    assert_artifact_error(lia.try_check_sat(), "try_check_sat(QF_LIA)");
    assert!(!dump.exists());

    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let one = solver.bv_const(1, 8);
    let x_is_one = solver.eq(x, one);
    solver.assert_term(x_is_one);

    let result = solver.try_check_sat().expect("pure QF_BV export");
    assert!(result.is_sat());
    assert!(dump.exists());

    // A no-soft MaxSMT call delegates to exactly one ordinary check and remains
    // exportable. A syntactic tactic likewise performs no hidden decision.
    let _ = solver
        .check_sat_max()
        .expect("zero-soft check_sat_max is one decision");
    assert!(dump.exists());
    solver
        .apply_tactic(&Tactic::Skip)
        .expect("syntactic tactic is safe");
    assert!(dump.exists());

    let write_stale = || std::fs::write(&dump, b"STALE\n").expect("write stale artifact");

    write_stale();
    solver
        .assert_soft(x_is_one, 1, None)
        .expect("Boolean soft constraint");
    assert_artifact_error(solver.check_sat_max(), "check_sat_max");
    assert!(!dump.exists());

    write_stale();
    assert_artifact_error(solver.abduce(x_is_one, &[]), "abduce");
    assert!(!dump.exists());

    write_stale();
    assert_artifact_error(
        solver.synthesize_patch(x_is_one, &[x_is_one]),
        "synthesize_patch",
    );
    assert!(!dump.exists());

    write_stale();
    assert_artifact_error(solver.try_minimize_model(), "try_minimize_model");
    assert!(!dump.exists());

    write_stale();
    let nested_solver_tactic = Tactic::Skip.then(Tactic::CtxSolverSimplify);
    assert_artifact_error(
        solver.apply_tactic(&nested_solver_tactic),
        "apply_tactic(ctx-solver-simplify)",
    );
    assert!(!dump.exists());

    write_stale();
    assert_artifact_error(
        Solver::cross_check_smtlib2(
            "(set-logic QF_BV) (declare-const y (_ BitVec 8)) (check-sat)",
            &[],
        ),
        "cross_check_smtlib2",
    );
    assert!(!dump.exists());

    // Post-solve proof validation may independently re-decide deferred-trust
    // steps. Those subordinate checks must never become top-level exporters or
    // alter the certificate for the original decision.
    let mut proof_solver = Solver::new(Logic::QfBv);
    proof_solver.set_produce_proofs(true);
    let proof_x = proof_solver.declare_const("proof_x", Sort::bitvec(8));
    let shift_one = proof_solver.bv_const(1, 8);
    let doubled = proof_solver.bvadd(proof_x, proof_x);
    let shifted = proof_solver.bvshl(proof_x, shift_one);
    let identity = proof_solver.eq(doubled, shifted);
    let counterexample = proof_solver.not(identity);
    proof_solver.assert_term(counterexample);
    assert!(proof_solver
        .try_check_sat()
        .expect("modular identity export")
        .is_unsat());
    let before = std::fs::read(&dump).expect("read sealed CNF before proof export");
    let _ = proof_solver
        .export_last_unsat_artifact()
        .expect("UNSAT proof artifact");
    let after = std::fs::read(&dump).expect("read sealed CNF after proof export");
    assert_eq!(after, before, "proof validation must preserve CNF bytes");
}
