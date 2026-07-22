// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #2824 incremental model synchronization.
//!
//! Incremental SAT push/pop allocates internal scope selector variables that are
//! not part of returned SAT models. These tests churn selector scopes before
//! introducing a contradictory scoped assertion, then require the contradiction
//! to be detected. This guards theory-model synchronization in EUF/LIA/LRA.
//!
//! Part of #2824

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute_all")
}

#[test]
#[timeout(10_000)]
fn incremental_euf_detects_contradiction_after_selector_churn() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)

        ; Global base fact
        (assert (= a b))

        ; First incremental check initializes persistent solver state
        (push 1)
        (check-sat)
        (pop 1)

        ; Churn SAT scope selectors with no additional assertions
        (push 1) (pop 1)
        (push 1) (pop 1)
        (push 1) (pop 1)
        (push 1) (pop 1)

        ; New scoped contradiction using a fresh congruence atom
        (push 1)
        (assert (distinct (f a) (f b)))
        (check-sat)
        (pop 1)

        ; Base fact still satisfiable after pop
        (check-sat)
    "#;

    let outputs = run_script(input);
    assert_eq!(outputs, vec!["sat", "unsat", "sat"]);
}

#[test]
#[timeout(10_000)]
fn incremental_lia_detects_contradiction_after_selector_churn() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)

        ; Global base fact
        (assert (<= x 0))

        ; First incremental check initializes persistent solver state
        (push 1)
        (check-sat)
        (pop 1)

        ; Churn SAT scope selectors with no additional assertions
        (push 1) (pop 1)
        (push 1) (pop 1)
        (push 1) (pop 1)
        (push 1) (pop 1)

        ; New scoped contradiction with base fact
        (push 1)
        (assert (> x 0))
        (check-sat)
        (pop 1)

        ; Base fact still satisfiable after pop
        (check-sat)
    "#;

    let outputs = run_script(input);
    assert_eq!(outputs, vec!["sat", "unsat", "sat"]);
}

#[test]
#[timeout(10_000)]
fn incremental_lra_detects_contradiction_after_selector_churn() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)

        ; Global base fact
        (assert (<= x 0.0))

        ; First incremental check initializes persistent solver state
        (push 1)
        (check-sat)
        (pop 1)

        ; Churn SAT scope selectors with no additional assertions
        (push 1) (pop 1)
        (push 1) (pop 1)
        (push 1) (pop 1)
        (push 1) (pop 1)

        ; New scoped contradiction with base fact
        (push 1)
        (assert (> x 0.0))
        (check-sat)
        (pop 1)

        ; Base fact still satisfiable after pop
        (check-sat)
    "#;

    let outputs = run_script(input);
    assert_eq!(outputs, vec!["sat", "unsat", "sat"]);
}
