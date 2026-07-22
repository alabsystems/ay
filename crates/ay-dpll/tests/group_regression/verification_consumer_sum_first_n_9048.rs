// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression guard for #9048: verification-consumer `examples/sum_first_n.rs` postcondition.
//!
//! The minimized postcondition VC is UNSAT after substituting `n = 2`. UFNIA
//! must expose the constant-divisor `div` atom to arithmetic preprocessing
//! instead of returning `unknown` or cycling in the Nelson-Oppen loop.

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn qf_ufnia_sum_first_n_int_div_postcondition_is_not_false_sat_9048() {
    let smt = r#"
(set-logic QF_UFNIA)
(declare-const n Int)
(assert (= n 2))
(assert (not (= (div (* n (+ n 1)) 2) 3)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output);

    assert_eq!(
        result,
        Some("unsat"),
        "#9048 reducer should be UNSAT, not verification-consumer-incomplete or false-SAT; got {output}"
    );
}
