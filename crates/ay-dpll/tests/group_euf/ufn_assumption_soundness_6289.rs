// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6289: `check-sat-assuming` in QF_UFN* logics must not
//! silently drop assumptions and return false SAT.

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn qf_ufnia_check_sat_assuming_does_not_drop_assumptions_6289() {
    let smt = r#"
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(check-sat-assuming ((not (= (f x) (f y)))))
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown output");
    assert_ne!(
        result, "sat",
        "QF_UFNIA check-sat-assuming must not ignore assumptions and return false SAT",
    );
}

#[test]
#[timeout(10_000)]
fn qf_ufnra_check_sat_assuming_does_not_drop_assumptions_6289() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a b))
(check-sat-assuming ((not (= (g a) (g b)))))
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown output");
    assert_ne!(
        result, "sat",
        "QF_UFNRA check-sat-assuming must not ignore assumptions and return false SAT",
    );
}

#[test]
#[timeout(10_000)]
fn qf_ufnira_check_sat_assuming_does_not_drop_assumptions_6289() {
    let smt = r#"
(set-logic QF_UFNIRA)
(declare-fun h (Int) Real)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(check-sat-assuming ((not (= (h x) (h y)))))
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown output");
    assert_ne!(
        result, "sat",
        "QF_UFNIRA check-sat-assuming must not ignore assumptions and return false SAT",
    );
}
