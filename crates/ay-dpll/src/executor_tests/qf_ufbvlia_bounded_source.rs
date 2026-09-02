// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact-source bounded Bool/BV/LIA refutation routing.

use crate::Executor;
use ay_frontend::parse;

fn execute(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    (executor, output)
}

fn bounded_source_outcome(executor: &Executor) -> Option<&str> {
    executor
        .statistics()
        .get_string("solver.bv_lia_bounded_source")
}

#[test]
fn bounded_source_refutes_mixed_boolean_implication() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const enabled Bool)
        (declare-const index (_ BitVec 64))
        (assert enabled)
        (assert (=> enabled (>= (bv2nat index) 18446744073709551616)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert_eq!(bounded_source_outcome(&executor), Some("unsat"));
}

#[test]
fn bounded_source_refutes_out_of_range_bv2nat() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const bits (_ BitVec 8))
        (assert (= (bv2nat bits) 256))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert_eq!(bounded_source_outcome(&executor), Some("unsat"));
}

#[test]
fn bounded_source_checks_negative_int2bv_modulo_semantics() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const source Int)
        (assert (= source (- 1)))
        (assert (not (= ((_ int2bv 8) source) #xff)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert_eq!(bounded_source_outcome(&executor), Some("unsat"));
}

#[test]
fn bounded_source_refutation_publishes_with_checked_authority() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const result (_ BitVec 16))
        (declare-const bits (_ BitVec 16))
        (assert (= bits #x9c40))
        (assert (= bits result))
        (assert (<= (* (bv2nat bits) 2) 65535))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert_eq!(bounded_source_outcome(&executor), Some("unsat"));
    assert!(
        executor.last_command_unsat_was_independently_verified()
            || executor.last_command_unsat_was_strictly_verified(),
        "published UNSAT must consume checked source or strict authority"
    );
}

#[test]
fn disjunctive_pseudo_bounds_do_not_produce_unsat_authority() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const source Int)
        (assert (or
            (and (>= source 0) (<= source 0))
            (and (>= source 2) (<= source 2))))
        (assert (= ((_ int2bv 8) source) #x00))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["sat"]);
    assert_eq!(bounded_source_outcome(&executor), Some("declined"));
}

#[test]
fn satisfiable_unbounded_int_source_declines() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const source Int)
        (assert (= ((_ int2bv 8) source) #x00))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert!(matches!(output.as_slice(), [answer] if answer == "sat" || answer == "unknown"));
    assert_eq!(bounded_source_outcome(&executor), Some("declined"));
}

#[test]
fn bounded_source_assumptions_are_exact_and_do_not_leak() {
    let commands = parse(
        r#"
            (set-logic QF_UFBVLIA)
            (declare-const bits (_ BitVec 8))
            (check-sat-assuming ((= (bv2nat bits) 256)))
            (get-unsat-assumptions)
            (check-sat)
        "#,
    )
    .expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let mut outputs = Vec::new();
    let mut outcomes = Vec::new();
    for command in &commands {
        if let Some(output) = executor.execute(command).expect("command must execute") {
            outputs.push(output);
            outcomes.push(bounded_source_outcome(&executor).map(str::to_owned));
        }
    }

    assert_eq!(outputs, vec!["unsat", "((= (bv2nat bits) 256))", "sat"]);
    assert_eq!(
        outcomes,
        vec![Some("unsat".to_string()), Some("unsat".to_string()), None]
    );
}

#[test]
fn declined_source_bridge_keeps_full_assumption_core_and_does_not_leak() {
    let commands = parse(
        r#"
            (set-logic QF_UFBVLIA)
            (declare-const b (_ BitVec 2))
            (declare-const gate Bool)
            (declare-const witness (_ BitVec 2))
            (declare-fun p ((_ BitVec 2)) Bool)
            (assert gate)
            (assert (p witness))
            (check-sat-assuming (
                (bvult b #b01)
                (=> gate (= (bv2nat b) 1))))
            (get-unsat-assumptions)
            (check-sat)
        "#,
    )
    .expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let mut outputs = Vec::new();
    let mut bounded_outcomes = Vec::new();
    let mut routes = Vec::new();
    for command in &commands {
        if let Some(output) = executor.execute(command).expect("command must execute") {
            outputs.push(output);
            bounded_outcomes.push(bounded_source_outcome(&executor).map(str::to_owned));
            routes.push(
                executor
                    .statistics()
                    .get_string("solver.logic_category")
                    .map(str::to_owned),
            );
        }
    }

    assert_eq!(
        outputs,
        vec![
            "unsat",
            "((bvult b #b01) (or (= (bv2nat b) 1) (not gate)))",
            "sat",
        ]
    );
    assert_eq!(
        bounded_outcomes,
        vec![
            Some("declined".to_string()),
            Some("declined".to_string()),
            None
        ]
    );
    assert_eq!(routes, vec![None, None, Some("QfUfbv".to_string()),]);
}
