// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #5536: Farkas graceful degradation.
//!
//! When Farkas certificate verification fails (structural or semantic),
//! the solver must keep the conflict clause for CDCL learning instead of
//! returning Unknown. The conflict literals are derived from sound simplex
//! analysis — only the proof certificate is invalid.
//!
//! These tests exercise the degradation path at the executor level by
//! running QF_LRA problems that trigger Farkas conflict generation.
//! Unit coverage in `extension.rs` separately exercises the MockTheory path.

use ay_dpll::Executor;
use ay_frontend::parse;

/// QF_LRA problem that must return unsat — exercises Farkas conflict path.
/// This is the regression from issue #1243 that triggered the original
/// Farkas verification code. If degradation breaks, this would return unknown.
#[test]
fn test_farkas_degradation_qf_lra_unsat_regression_5536() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= y (+ x 1)))
        (assert (or (< y 0.5) (> y 2.5)))
        (check-sat)
    "#;
    // UNSAT: x ∈ [0,1] => y = x+1 ∈ [1,2], contradicts y ∉ [0.5, 2.5]
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unsat"],
        "QF_LRA problem must be unsat, not unknown (#5536)"
    );
}

/// QF_LRA with tight bounds — exercises Farkas on bounded variable conflict.
/// Simple bounds conflict: x >= 5 and x <= 3 is trivially unsatisfiable.
#[test]
fn test_farkas_degradation_tight_bounds_unsat_5536() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 5.0))
        (assert (<= x 3.0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"], "Tight bounds must be unsat (#5536)");
}

/// QF_LRA with multiple interacting constraints — exercises multi-row Farkas.
#[test]
fn test_farkas_degradation_multi_constraint_unsat_5536() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (assert (>= (+ x y) 10.0))
        (assert (>= (+ y z) 10.0))
        (assert (<= x 2.0))
        (assert (<= y 3.0))
        (assert (<= z 4.0))
        (check-sat)
    "#;
    // UNSAT: x+y >= 10 but x <= 2, y <= 3 means x+y <= 5. Contradiction.
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Multi-constraint LRA must be unsat (#5536)"
    );
}
