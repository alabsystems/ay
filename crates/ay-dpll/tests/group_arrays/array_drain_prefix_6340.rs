// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression for #6340: duplicate pre-existing array assertions must not panic
//! the AUFLIA drain path after eager array-axiom preprocessing.

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn qf_auflia_duplicate_prefix_does_not_panic_6340() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const v Int)
(assert (= (select a i) v))
(assert (= (select a i) v))
(check-sat)
"#,
    );

    assert_eq!(
        outputs[0], "sat",
        "duplicate protected-prefix assertions must not shrink below axiom_start before drain",
    );
}
