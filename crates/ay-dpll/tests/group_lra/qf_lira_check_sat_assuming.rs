// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for `check-sat-assuming` in LIRA-family logics.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `(* 2 x) = 1` is UNSAT for Int x, but requires an integer split in the LRA relaxation.
///
/// Regression test for #1835: LIRA `check-sat-assuming` must not return `unknown` on `NeedSplit`.
#[test]
#[timeout(60_000)]
fn test_qf_lira_check_sat_assuming_handles_integer_splits_regression_1835() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= y 0.0))
        (assert (= (* 2 x) 1))
        (check-sat-assuming ())
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Same as `test_qf_lira_*`, but through AUFLIRA logic selection.
#[test]
#[timeout(60_000)]
fn test_qf_auflira_check_sat_assuming_handles_integer_splits_regression_1835() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= y 0.0))
        (assert (= (* 2 x) 1))
        (check-sat-assuming ())
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Same UNSAT, but the split-triggering constraint appears only in assumptions (not in assertions).
#[test]
#[timeout(60_000)]
fn test_qf_lira_check_sat_assuming_encodes_assumptions_regression_1835() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= y 0.0))
        (check-sat-assuming ((= (* 2 x) 1)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Same as `test_qf_lira_check_sat_assuming_encodes_assumptions_regression_1835`,
/// but through AUFLIRA logic selection.
#[test]
#[timeout(60_000)]
fn test_qf_auflira_check_sat_assuming_encodes_assumptions_regression_1835() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= y 0.0))
        (check-sat-assuming ((= (* 2 x) 1)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// SAT control for the deferred-postprocessing helper used by LIRA-family
/// assumption solving. Permanent assertions validate after the temporary
/// rewritten assertion view is restored.
#[test]
#[timeout(60_000)]
fn test_qf_lira_check_sat_assuming_sat_keeps_reason_unknown_clear_6731() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= (+ x 1) 4))
        (check-sat-assuming ((= y 0.5) (= (+ (to_real x) y) 3.5)))
    "#;

    let commands = parse(smt).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
    assert!(
        exec.unknown_reason().is_none(),
        "LIRA assumption-side SAT must not leave reason-unknown set: {:?}",
        exec.unknown_reason()
    );
}

/// Composite Boolean assumption: `(and (= x 0) (= x 1))` is UNSAT because x
/// cannot be both 0 and 1.
///
/// Regression for #6689: the incremental assumption path must materialize
/// Tseitin definitional clauses for composite (non-atomic) assumptions.
/// Without this, the SAT solver sees an unconstrained gate variable and
/// reports `sat`.
#[test]
#[timeout(60_000)]
fn test_qf_lira_check_sat_assuming_composite_boolean_assumption_6689() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (check-sat-assuming ((and (= x 0) (= x 1))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Same composite-assumption test through AUFLIRA logic selection.
#[test]
#[timeout(60_000)]
fn test_qf_auflira_check_sat_assuming_composite_boolean_assumption_6689() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (check-sat-assuming ((and (= x 0) (= x 1))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Composite assumption cores must map back to the original user-facing term,
/// not the internal Tseitin gate introduced to encode `(and ...)`.
#[test]
#[timeout(60_000)]
fn test_qf_lira_get_unsat_assumptions_preserves_composite_term_6689() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (check-sat-assuming ((and (= x 0) (= x 1))))
        (get-unsat-assumptions)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("(and"),
        "expected composite assumption in UNSAT core, got: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("(= x 0)") && outputs[1].contains("(= x 1)"),
        "expected both conjuncts in original composite assumption, got: {}",
        outputs[1]
    );
}

/// Same UNSAT-core preservation check through AUFLIRA logic selection.
#[test]
#[timeout(60_000)]
fn test_qf_auflira_get_unsat_assumptions_preserves_composite_term_6689() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (check-sat-assuming ((and (= x 0) (= x 1))))
        (get-unsat-assumptions)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("(and"),
        "expected composite assumption in UNSAT core, got: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("(= x 0)") && outputs[1].contains("(= x 1)"),
        "expected both conjuncts in original composite assumption, got: {}",
        outputs[1]
    );
}
