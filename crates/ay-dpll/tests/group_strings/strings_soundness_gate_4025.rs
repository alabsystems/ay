// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4025.
//!
//! Originally, all string logics were gated to `unknown` under a soundness-first
//! policy. The gate has been lifted (#7527) — QF_S and QF_SLIA now return
//! correct results. Model validation runs for string theories (#8456).

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn string_logics_solve_correctly_after_gate_removal() {
    let cases = [
        (
            "QF_S",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "abc"))
(check-sat)
"#,
            "sat",
        ),
        (
            "QF_SLIA",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(check-sat)
"#,
            "sat",
        ),
    ];

    for (logic, smt, expected) in cases {
        let result = crate::common::solve(smt);
        assert_eq!(
            crate::common::sat_result(&result),
            Some(expected),
            "{logic}: expected {expected}"
        );
    }
}

/// QF_SNIA routes supported string/integer formulas through the combined
/// strings+arithmetic lane and validates the resulting model.
#[test]
#[timeout(10_000)]
fn qf_snia_to_int_supported_case_is_sat() {
    let smt = r#"
(set-logic QF_SNIA)
(declare-fun x () String)
(assert (= (str.to_int x) 42))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_int(x) = 42 has the validated witness x = \"42\""
    );
}

#[test]
#[timeout(10_000)]
fn check_sat_assuming_on_string_logic_solves() {
    let implication_sat = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun a () Bool)
(assert (=> a (= x "a")))
(check-sat-assuming (a))
"#;
    let result = crate::common::solve(implication_sat);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "check-sat-assuming on QF_S should return sat after gate removal"
    );

    // Requires endpoint-empty reasoning with no explicit "" literal.
    // Assumptions-mode must pre-register the empty string exactly like
    // solve_strings()/solve_strings_lia() to keep this SAT.
    let endpoint_empty_sat = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun a () Bool)
(assert (=> a (= (str.++ x "a") "a")))
(check-sat-assuming (a))
"#;
    let result = crate::common::solve(endpoint_empty_sat);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "check-sat-assuming endpoint-empty case should return sat after gate removal"
    );
}
