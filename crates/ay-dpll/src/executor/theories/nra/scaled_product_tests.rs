// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor-boundary scaled-product model publication regressions.

use crate::Executor;
use ay_frontend::parse;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("scaled-product script parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("scaled-product script executes")
}

#[test]
fn executor_publishes_exact_scaled_product_sat() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 3.0))
(assert (= y 5.0))
(assert (= (* 4.0 x y) 60.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
fn executor_validates_representative_and_alias_values_together() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 3.0))
(assert (= y 5.0))
(assert (= (* x y) 15.0))
(assert (= (* 2.0 x y) 30.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
fn executor_never_refutes_negative_scaled_square() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= x 1.0))
(assert (<= (* -2.0 x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}
