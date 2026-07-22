// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

/// Regression for #3892: all eight extended string functions parsed by the
/// frontend must be semantically enforced by the theory solver.
///
/// Each case is a ground negated equality that is UNSAT under SMT-LIB 2.6.
#[test]
#[timeout(20_000)]
fn extf_ground_negated_equalities_are_unsat_issue_3892() {
    let cases = [
        (
            "str.replace_all",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.replace_all "aaba" "a" "c") "ccbc")))
(check-sat)
"#,
        ),
        (
            "str.replace_re",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.replace_re "hello" (str.to_re "l") "r") "herlo")))
(check-sat)
"#,
        ),
        (
            "str.replace_re_all",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.replace_re_all "hello" (str.to_re "l") "r") "herro")))
(check-sat)
"#,
        ),
        (
            "str.from_int",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.from_int 42) "42")))
(check-sat)
"#,
        ),
        (
            "str.from_code",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.from_code 97) "a")))
(check-sat)
"#,
        ),
        (
            "str.to_code",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.to_code "A") 65)))
(check-sat)
"#,
        ),
        (
            "str.to_lower",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.to_lower "HeLLo") "hello")))
(check-sat)
"#,
        ),
        (
            "str.to_upper",
            r#"
(set-logic QF_SLIA)
(assert (not (= (str.to_upper "HeLLo") "HELLO")))
(check-sat)
"#,
        ),
    ];

    for (name, smt) in cases {
        let output = crate::common::solve(smt);
        assert_eq!(
            crate::common::sat_result(&output),
            Some("unsat"),
            "{name}: expected UNSAT for ground negated equality, got output:\n{output}"
        );
    }
}
