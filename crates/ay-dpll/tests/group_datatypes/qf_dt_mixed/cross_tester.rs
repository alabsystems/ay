// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-tester datatype regressions.

use super::*;

/// UNSAT: Cross-tester reasoning for non-nullary constructors (#2766).
///
/// Asserting `is-Err(x)` should imply `¬is-Ok(x)` for a two-constructor datatype.
/// The expected derivation path:
/// 1. Exhaustiveness: (or (is-Ok x) (is-Err x))
/// 2. Constructor axiom: (=> (is-Err x) (= x (Err (sel-err x))))
/// 3. Tester evaluation: is-Ok(Err(...)) = false
/// Combined: is-Err(x) → x = Err(...) → is-Ok(x) = false
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_cross_tester_non_nullary() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype ResultIntInt (
            (Ok (sel-ok Int))
            (Err (sel-err Int))
        ))
        (declare-fun x () ResultIntInt)
        (assert (is-Err x))
        (assert (ite (is-Ok x) (not (= (sel-ok x) 0)) false))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Bug #2766: is-Err(x) should derive ¬is-Ok(x), making the ITE take the false branch → UNSAT.
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2766: is-Err(x) should imply not(is-Ok(x)) [QF_DT]"
    );
}

/// UNSAT: Cross-tester reasoning under ALL logic with DT+Int (#2766).
///
/// Same scenario as test_qf_dt_unsat_cross_tester_non_nullary but using
/// `(set-logic ALL)`, which routes through DT+AUFLIA combined solver.
/// The cross-tester derivation must work in the combined theory path.
#[test]
#[timeout(60_000)]
fn test_all_logic_unsat_cross_tester_non_nullary() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype ResultIntInt (
            (Ok (sel-ok Int))
            (Err (sel-err Int))
        ))
        (declare-fun x () ResultIntInt)
        (assert (is-Err x))
        (assert (not (= (ite (is-Ok x) (sel-ok x) 0) 0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2766: is-Err(x) should imply not(is-Ok(x)) [ALL logic]"
    );
}

/// UNSAT: Cross-tester reasoning via check-sat-assuming under ALL logic (#2766).
///
/// The check-sat-assuming path has separate axiom generation code (executor.rs:1503-1529)
/// that includes assumptions in the base_set before calling dt_selector_axioms().
/// This test verifies axiom (B') works in that path too.
#[test]
#[timeout(60_000)]
fn test_all_logic_unsat_cross_tester_check_sat_assuming() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype ResultIntInt (
            (Ok (sel-ok Int))
            (Err (sel-err Int))
        ))
        (declare-fun x () ResultIntInt)
        (assert (not (= (ite (is-Ok x) (sel-ok x) 0) 0)))
        (check-sat-assuming ((is-Err x)))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2766: is-Err(x) via assumption should imply not(is-Ok(x)) [ALL logic, check-sat-assuming]"
    );
}
