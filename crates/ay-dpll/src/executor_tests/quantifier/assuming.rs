// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// #7150: simple trigger-based instantiation over a ground UF term.
///
/// Auto-trigger extraction should pick up `(f x)` from the quantified body,
/// match it against the ground term `(f 5)`, and instantiate the body to
/// prove the ground assertion directly.
#[test]
fn test_simple_quantified_uflia_ground_instance_sat_7150() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (> (f x) 0)))
        (assert (> (f 5) 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown, got {outputs:?}"
    );
}

/// #7150: quantified `check-sat-assuming` must run the same E-matching
/// preprocessing as plain `check-sat`.
///
/// Without the quantified fallback path, `check_sat_assuming()` bypasses
/// quantifier preprocessing and incorrectly returns SAT here.
#[test]
fn test_simple_quantified_uflia_assumption_unsat_7150() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (> (f x) 0)))
        (check-sat-assuming ((<= (f 5) 0)))
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "quantified assumptions must instantiate (f 5) and detect the contradiction"
    );
}
