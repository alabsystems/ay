// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn repeated_projection_restores_distinct_binders_and_original_model() {
    let input = r#"
        (set-logic HORN)
        (declare-fun P (Int Int Int) Bool)
        (assert (forall ((b Int) (c Int) (d Int)) (=> (= c d) (P 0 b c))))
        (assert (forall ((x Int) (b Int) (c Int))
          (=> (and (P x b c) (< x 3)) (P (+ x 1) b c))))
        (assert (forall ((x Int) (b Int) (c Int))
          (=> (and (P x b c) (> x 3)) false)))
        (check-sat)
    "#;
    let original = parse_problem(input);
    let first = Box::new(DeadParamEliminator::new()).transform(original.clone());
    let locals = Box::new(LocalVarEliminator::new()).transform(first.problem);
    let second = Box::new(DeadParamEliminator::new()).transform(locals.problem);
    assert_eq!(second.problem.predicates()[0].arity(), 1);
    let crate::pdr::PdrResult::Safe(model) =
        crate::pdr::PdrSolver::new(second.problem, PdrConfig::default()).solve()
    else {
        panic!("reduced loop must be safe");
    };
    let model = second.back_translator.translate_validity(model);
    let model = locals.back_translator.translate_validity(model);
    let model = first.back_translator.translate_validity(model);
    let interpretation = model.get(&PredicateId::new(0)).expect("restored P");
    let names: std::collections::HashSet<_> = interpretation.vars.iter().map(|v| &v.name).collect();
    assert_eq!(
        names.len(),
        3,
        "each restored argument has a distinct binder"
    );
    assert!(crate::pdr::PdrSolver::new(original, PdrConfig::default()).verify_model(&model));
}

#[test]
fn slicing_keeps_actions_and_the_original_pruned_query_registry() {
    let mut original = parse_problem(
        r#"
        (set-logic HORN)
        (declare-fun P (Int Int) Bool)
        (assert (forall ((dead Int)) (P 0 dead)))
        (assert (forall ((x Int) (dead Int))
          (=> (and (P x dead) (> x 0)) false)))
        (assert (forall ((x Int) (dead Int))
          (=> (and (P x dead) false) false)))
        (check-sat)
    "#,
    );
    let action = original.declare_action("native call");
    for clause in original.clauses_mut() {
        clause.action_id = Some(action);
    }
    let source_ids = original.pruned_false_query_ids();
    assert_eq!(source_ids.len(), 1);
    let (projected, _) = DeadParamEliminator::new().eliminate(&original);
    assert_eq!(projected.predicates()[0].arity(), 1);
    assert_eq!(projected.action_names(), original.action_names());
    assert_eq!(projected.pruned_false_query_ids(), source_ids);
    for (before, after) in original.clauses().iter().zip(projected.clauses()) {
        assert_eq!(after.action_id, before.action_id);
        assert_eq!(after.source_query_ordinal, before.source_query_ordinal);
    }
    projected
        .validate()
        .expect("live and frozen source registries remain typed");
}
