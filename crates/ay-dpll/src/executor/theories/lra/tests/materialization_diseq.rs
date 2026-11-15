// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A disequality under Boolean structure (an equality atom the SAT layer
//! assigned false) must survive the LRA model's δ-materialisation: with
//! `x > 0, x <= 1` the simplex puts x at 0+ε, and the bound envelope alone
//! chose δ = 1/2, publishing x = 1/2 where `2x = 1` holds. Validation caught
//! it (`MODEL-UNCONFIRMED`) and the recovery re-solve had to run; with a Bool
//! constant in the skeleton the recovery then failed too and the answer was
//! `unknown` (DPLL_LRA_perf_2026-09-23 §1; the om1 BMC depth-3 signature).

use crate::Executor;
use ay_frontend::parse;

fn solve(script: &str) -> (Vec<String>, u64) {
    let commands = parse(script).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let out = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");
    (out, exec.statistics().model_validation_failures)
}

#[test]
fn ite_condition_disequality_survives_materialization() {
    let (out, failures) = solve(
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (> x 0.0))
(assert (<= x 1.0))
(assert (ite (= (* 2.0 x) 1.0) (> x 5.0) true))
(check-sat)
",
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}");
    assert_eq!(
        failures, 0,
        "the first published model must already be valid"
    );
}

#[test]
fn disequality_with_bool_skeleton_is_sat_not_unknown() {
    let (out, failures) = solve(
        "(set-logic QF_LRA)
(declare-const x Real)
(declare-const b Bool)
(assert (> x 0.0))
(assert (<= x 1.0))
(assert (or b (= (* 2.0 x) 1.0)))
(assert (=> b (not (= x (/ 1.0 2.0)))))
(assert (=> (= x (/ 1.0 2.0)) (> x 5.0)))
(check-sat)
",
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}");
    assert_eq!(
        failures, 0,
        "the first published model must already be valid"
    );
}
