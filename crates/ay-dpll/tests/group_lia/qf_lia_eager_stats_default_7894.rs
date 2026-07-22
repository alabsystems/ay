// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for QF_LIA eager routing (#7894, Fix B1).
//!
//! Standalone QF_LIA should use the eager split-loop arm so LIA theory
//! propagation runs during SAT search. Since Fix B1 (lia-hot-loop plan),
//! incremental push/pop sessions get the same eager arm through a temporary
//! isolated state at scope depth 0 (kill switch
//! `AY_DPLL_LIA_INCREMENTAL_EAGER=0`; proof-producing sessions stay lazy).

use ay_dpll::Executor;
use ay_frontend::parse;

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: QF_LIA script should execute");
    (exec, outputs)
}

#[test]
fn test_default_qf_lia_exports_eager_stats_7894() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= (+ x y) 1))
        (assert (<= x 0))
        (assert (<= y 0))
        (check-sat)
    "#;

    let (exec, outputs) = run_script(input);
    assert_eq!(outputs, vec!["unsat"]);

    let propagate_calls = exec
        .statistics()
        .get_int("dpll.eager.propagate_calls")
        .unwrap_or(0);
    assert!(
        propagate_calls > 0,
        "expected standalone QF_LIA to use eager propagation; got dpll.eager.propagate_calls={propagate_calls}"
    );

    assert!(
        exec.statistics().theory_conflicts > 0 || exec.statistics().theory_propagations > 0,
        "expected theory interaction on standalone QF_LIA: conflicts={}, propagations={}",
        exec.statistics().theory_conflicts,
        exec.statistics().theory_propagations
    );
}

#[test]
fn test_default_qf_lia_eager_final_check_handles_disequality_7894() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (not (= x 5)))
        (assert (>= x 5))
        (assert (<= x 5))
        (check-sat)
    "#;

    let (exec, outputs) = run_script(input);
    assert_eq!(outputs, vec!["unsat"]);

    let propagate_calls = exec
        .statistics()
        .get_int("dpll.eager.propagate_calls")
        .unwrap_or(0);
    assert!(
        propagate_calls > 0,
        "expected standalone QF_LIA disequality check to stay on the eager path; got dpll.eager.propagate_calls={propagate_calls}"
    );
}

#[test]
fn test_incremental_qf_lia_routes_eager_b1() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (>= x 1))
        (assert (<= x 0))
        (check-sat)
    "#;

    let (exec, outputs) = run_script(input);
    assert_eq!(outputs, vec!["unsat"]);

    // Fix B1: incremental push/pop sessions route to the eager
    // BCP-interleaved arm (on a temporary isolated state) by default, so
    // eager propagation statistics must be exported just like standalone.
    let propagate_calls = exec
        .statistics()
        .get_int("dpll.eager.propagate_calls")
        .unwrap_or(0);
    assert!(
        propagate_calls > 0,
        "expected incremental QF_LIA to route to the eager arm (Fix B1); \
         got dpll.eager.propagate_calls={propagate_calls}"
    );
}
