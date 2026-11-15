// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::engines::{prove_external_invariant_model, validate_external_invariant_model};
use crate::VerifiedChcResult;
use std::time::Duration;

#[test]
fn public_exact_model_gate_rejects_filtered_head_and_accepts_original_valid_model() {
    for valid in [false, true] {
        let solver = solver(TWO_FACTS);
        let model = pair_model(&solver, valid);
        let (pred_c, _) = pair(&solver);
        let expected = model.get(&pred_c).unwrap().formula.clone();
        let config = PdrConfig::default();
        assert_eq!(
            validate_external_invariant_model(&solver.problem, &model, &config).unwrap(),
            valid,
            "the public gate must check the submitted interpretation"
        );
        let run = prove_external_invariant_model(solver.problem.clone(), model, config).unwrap();
        assert_eq!(run.accepted_as_proof(), valid, "got {run:?}");
        if valid {
            let VerifiedChcResult::Safe(checked) = run.result() else {
                panic!("expected checked Safe, got {run:?}");
            };
            assert_eq!(checked.model().get(&pred_c).unwrap().formula, expected);
        } else {
            assert!(run.result().is_unknown(), "got {run:?}");
        }
    }
}

#[test]
fn reachable_error_query_rejects_both_excluding_and_inductive_candidates() {
    let source = TWO_FACTS.replace(
        "(check-sat)",
        "(assert (forall ((a Int) (b Int)) \
         (=> (and (C a b) (= a 0) (= b 1)) false)))\n(check-sat)",
    );
    for valid_transition in [false, true] {
        let mut solver = solver(&source);
        assert_eq!(solver.problem.clauses().len(), 4);
        assert!(matches!(
            solver.problem.clauses()[3].head,
            ClauseHead::False
        ));
        assert_eq!(solver.problem.clauses()[3].body.predicates.len(), 1);
        let model = pair_model(&solver, valid_transition);
        // The negated-pair candidate excludes the error but is not inductive;
        // the pair candidate is inductive but permits the reachable error.
        assert!(
            !validate_external_invariant_model(&solver.problem, &model, &PdrConfig::default(),)
                .unwrap()
        );
        let run = prove_external_invariant_model(
            solver.problem.clone(),
            model.clone(),
            PdrConfig::default(),
        )
        .unwrap();
        assert!(!run.accepted_as_proof(), "got {run:?}");
        assert!(run.result().is_unknown(), "got {run:?}");
        let result = solver.finish_safe_with_result_trace(model, "reachable-error-regression");
        assert!(matches!(result, PdrResult::Unknown), "got {result:?}");
    }
}

#[test]
fn strict_teacher_preserves_concrete_original_transition_failure() {
    let mut solver = solver(TWO_FACTS);
    solver.config.strict_proofs = true;
    let model = pair_model(&solver, false);
    let (pred_c, reachable_pair) = pair(&solver);
    let pred_a = solver.problem.lookup_predicate("A").unwrap();
    let (body_pred, pre, head_pred, post) = solver
        .verify_model_fresh_with_failure(&model)
        .expect("the exact transition must fail, even when head filtering would pass");
    assert_eq!(body_pred, pred_a);
    assert_eq!(head_pred, pred_c);
    let initial_a = ChcExpr::eq(
        ChcExpr::var(solver.canonical_vars(pred_a).unwrap()[0].clone()),
        ChcExpr::Int(0),
    );
    assert_eq!(pre, initial_a);
    let actual = post.collect_conjuncts();
    let expected = reachable_pair.collect_conjuncts();
    assert_eq!(actual.len(), expected.len());
    for conjunct in expected {
        assert!(
            actual.contains(&conjunct),
            "incomplete teacher poststate: {post}"
        );
    }
    assert_eq!(solver.candidate_repair_rounds_used, 0);
    assert_eq!(
        model.get(&pred_c).unwrap().formula,
        ChcExpr::not(reachable_pair)
    );
}

#[test]
fn checked_repair_publishes_changed_model_only_after_fresh_validation() {
    let mut solver = solver(TWO_FACTS);
    let model = pair_model(&solver, false);
    let (pred_c, _) = pair(&solver);
    let original = model.get(&pred_c).unwrap().formula.clone();
    let result = solver
        .finish_safe_or_continue(model, "filtered-head-repair-regression")
        .expect("a no-query problem permits the genuinely repaired model");
    let PdrResult::Safe(repaired) = result else {
        panic!("expected checked repaired model, got {result:?}");
    };
    assert_eq!(solver.candidate_repair_rounds_used, 1);
    assert_ne!(repaired.get(&pred_c).unwrap().formula, original);
    assert_eq!(repaired.get(&pred_c).unwrap().formula, ChcExpr::Bool(true));
    assert!(!repaired.individually_inductive && !repaired.convergence_proven);
    assert!(
        validate_external_invariant_model(&solver.problem, &repaired, &PdrConfig::default(),)
            .unwrap()
    );
}

#[test]
fn strict_fast_model_gate_checks_original_head() {
    for valid in [false, true] {
        let mut solver = solver(TWO_FACTS);
        solver.config.strict_proofs = true;
        let model = pair_model(&solver, valid);
        let deadline = ay_core::time::Instant::now() + Duration::from_secs(5);
        assert_eq!(solver.verify_model_fast(&model, deadline), valid);
    }
}
