// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression contract for #3402 using `distinct` syntax.
//!
//! Guards formulas of the form:
//!   (assert (distinct c (str.fn ...)))
//! where the function application evaluates to `c`.
//! These must be UNSAT and must match Z3.

use crate::common::z3::{check_z3_or_skip as z3_available, solve_with_z3};
use ntest::timeout;

#[test]
#[timeout(10_000)]
fn distinct_ground_extf_equalities_are_unsat() {
    let cases = [
        (
            "str.at",
            r#"
(set-logic QF_S)
(assert (distinct "h" (str.at "hello" 0)))
(check-sat)
"#,
        ),
        (
            "str.substr",
            r#"
(set-logic QF_S)
(assert (distinct "ell" (str.substr "hello" 1 3)))
(check-sat)
"#,
        ),
        (
            "str.replace",
            r#"
(set-logic QF_S)
(assert (distinct "herlo" (str.replace "hello" "l" "r")))
(check-sat)
"#,
        ),
        (
            "str.replace_all",
            r#"
(set-logic QF_S)
(assert (distinct "hello" (str.replace_all "hello" "x" "y")))
(check-sat)
"#,
        ),
        (
            "str.indexof",
            r#"
(set-logic QF_SLIA)
(assert (distinct 2 (str.indexof "hello" "ll" 0)))
(check-sat)
"#,
        ),
        (
            "str.to_int",
            r#"
(set-logic QF_SLIA)
(assert (distinct 42 (str.to_int "42")))
(check-sat)
"#,
        ),
        (
            "str.from_int",
            r#"
(set-logic QF_SLIA)
(assert (distinct "42" (str.from_int 42)))
(check-sat)
"#,
        ),
    ];

    let has_z3 = z3_available();

    for (name, smt) in cases {
        let ay_output = crate::common::solve(smt);
        let ay = crate::common::sat_result(&ay_output);
        assert_eq!(
            ay,
            Some("unsat"),
            "{name}: ay must return unsat for distinct ground equality; output={ay_output}"
        );

        if has_z3 {
            let z3_output = solve_with_z3(smt).unwrap_or_else(|e| panic!("{name}: z3 failed: {e}"));
            let z3 = crate::common::sat_result(&z3_output);
            assert_eq!(
                z3,
                Some("unsat"),
                "{name}: z3 must return unsat for distinct ground equality; output={z3_output}"
            );
            assert_eq!(ay, z3, "{name}: ay/z3 mismatch");
        }
    }
}
