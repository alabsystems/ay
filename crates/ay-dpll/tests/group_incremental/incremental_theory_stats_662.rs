// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::Executor;
use ay_frontend::parse;

#[test]
fn test_incremental_lia_theory_statistics_monotone_across_check_sat_662() {
    // Two check-sat calls in one incremental session:
    // 1) SAT under partial constraints
    // 2) UNSAT after adding a bound that creates a cross-variable LIA conflict.
    // Theory counters should be cumulative and monotone. The second check must
    // require theory reasoning rather than a pure SAT-level contradiction.
    let input = r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs false)
        (declare-const x Int)
        (declare-const y Int)
        (push 1)
        (assert (>= (+ x y) 1))
        (assert (<= x 0))
        (check-sat)
        (assert (<= y 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let mut outputs: Vec<String> = Vec::new();
    let mut stats_by_check = Vec::new();

    for cmd in &commands {
        if let Some(output) = exec
            .execute(cmd)
            .expect("invariant: execute should not fail")
        {
            outputs.push(output);
            stats_by_check.push(exec.statistics().clone());
        }
    }

    assert_eq!(outputs, vec!["sat", "unsat"]);
    assert_eq!(stats_by_check.len(), 2);

    let first = &stats_by_check[0];
    let second = &stats_by_check[1];

    assert!(
        second.theory_conflicts >= first.theory_conflicts,
        "theory_conflicts must be monotone across incremental checks: first={}, second={}",
        first.theory_conflicts,
        second.theory_conflicts
    );
    assert!(
        second.theory_propagations >= first.theory_propagations,
        "theory_propagations must be monotone across incremental checks: first={}, second={}",
        first.theory_propagations,
        second.theory_propagations
    );

    let conflict_delta = second
        .theory_conflicts
        .saturating_sub(first.theory_conflicts);
    let propagation_delta = second
        .theory_propagations
        .saturating_sub(first.theory_propagations);
    assert!(
        conflict_delta > 0 || propagation_delta > 0,
        "expected at least one theory counter to increase across checks; \
         first=(conflicts={}, propagations={}), second=(conflicts={}, propagations={})",
        first.theory_conflicts,
        first.theory_propagations,
        second.theory_conflicts,
        second.theory_propagations
    );
}
