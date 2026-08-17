// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{parse, Executor};
use crate::executor::model::{with_isolated_eval_memo, EvalValue};

#[test]
fn forall_equality_publishes_only_with_exact_rewrite_and_model_authority() {
    // Array extensionality makes this root exactly equivalent to `b != cc`.
    // The narrow SAT-only lane must independently replay that rewrite and
    // evaluate the rewritten root in the exact retained model before emission.
    let input = r#"
        (set-logic ALIA)
        (declare-const b (Array Int Int))
        (declare-const cc (Array Int Int))
        (assert (not (forall ((X0 Int)) (= (select b X0) (select cc X0)))))
        (check-sat)
    "#;
    let commands = parse(input).expect("negated pointwise array formula parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("negated pointwise array formula executes");
    assert_eq!(
        outputs,
        vec!["sat"],
        "different constant arrays witness the negated pointwise equality"
    );
    assert!(exec.was_model_validated());
    let roots = exec.independent_gate_query_roots();
    assert_eq!(
        roots.len(),
        1,
        "authority must bind the exact authored root"
    );
    assert!(exec.has_current_model_bound_quantified_sat_authority(&roots));

    let rewritten = exec
        .replay_exact_top_level_array_negation(roots[0])
        .expect("the authored root has the canonical extensional rewrite");
    let model = exec.last_model.as_ref().expect("validated retained model");
    assert_eq!(
        with_isolated_eval_memo(|| exec.evaluate_term(model, rewritten)),
        EvalValue::Bool(true),
        "the independently replayed ground root must hold in the sealed model"
    );
}
