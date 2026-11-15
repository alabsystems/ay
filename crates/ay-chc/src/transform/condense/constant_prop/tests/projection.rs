// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};

use super::*;

fn check(input: &str, safe: bool) {
    let original = parse(input);
    let projected = Box::new(ConstantPropagator::new()).transform(original.clone());
    assert!(projected
        .problem
        .predicates()
        .iter()
        .zip(original.predicates())
        .any(|(after, before)| after.arity() < before.arity()));
    if safe {
        let PdrResult::Safe(model) = PdrSolver::new(projected.problem, config()).solve() else {
            panic!("projected problem must prove safe: {input}");
        };
        let restored = projected.back_translator.translate_validity(model);
        assert!(PdrSolver::new(original.clone(), config()).verify_model(&restored));
    }
    let configuration = PortfolioConfig {
        engines: vec![EngineConfig::Pdr(config())],
        parallel: false,
        timeout: Some(Duration::from_secs(15)),
        strict_proofs: true,
        ..PortfolioConfig::default()
    };
    let result = PortfolioSolver::new(original, configuration).solve();
    assert!(
        if safe {
            matches!(result, PortfolioResult::Safe(_))
        } else {
            matches!(result, PortfolioResult::Unsafe(_))
        },
        "original model/replay acceptance must preserve polarity: {result:?}\n{input}"
    );
}

#[test]
fn constant_fields_disappear_and_models_restore_original_positions() {
    let input = r#"
        (set-logic HORN)
        (declare-fun P (Int Int Int) Bool)
        (assert (P 7 0 9))
        (assert (forall ((a Int) (x Int) (b Int))
          (=> (and (P a x b) (< x 3)) (P a (+ x 1) b))))
        (assert (forall ((a Int) (x Int) (b Int))
          (=> (and (P a x b) (> x 3)) false)))
        (check-sat)
    "#;
    check(input, true);
    check(&input.replace("(> x 3)", "(= x 3)"), false);
}

#[test]
fn literal_body_match_cannot_be_erased_with_a_constant_position() {
    let input = r#"
        (set-logic HORN)
        (declare-fun P (Int) Bool)
        (assert (P 7))
        (assert (=> (P 8) false))
        (check-sat)
    "#;
    check(input, true);
    check(&input.replace("(P 8)", "(P 7)"), false);
}

#[test]
fn compound_body_matches_retain_their_arithmetic_guard() {
    let input = r#"
        (set-logic HORN)
        (declare-fun P (Int Int) Bool)
        (assert (P 0 7))
        (assert (forall ((x Int) (tag Int))
          (=> (and (P x tag) (< x 3)) (P (+ x 1) tag))))
        (assert (forall ((x Int))
          (=> (and (P x (+ x 5)) (= x 1)) false)))
        (check-sat)
    "#;
    check(input, true);
    check(&input.replace("(= x 1)", "(= x 2)"), false);
}

#[test]
fn conflicting_constant_premises_do_not_silently_unify() {
    let input = r#"
        (set-logic HORN)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (assert (P 7))
        (assert (Q 8))
        (assert (forall ((x Int)) (=> (and (P x) (Q x)) false)))
        (check-sat)
    "#;
    check(input, true);
    check(&input.replace("(Q 8)", "(Q 7)"), false);
}

#[test]
fn projection_preserves_action_and_pruned_source_query_identity() {
    let mut original = parse(
        r#"
        (set-logic HORN)
        (declare-fun P (Int Int) Bool)
        (assert (P 0 7))
        (assert (forall ((x Int) (tag Int))
          (=> (and (P x tag) (> x 0)) false)))
        (assert (forall ((x Int) (tag Int))
          (=> (and (P x tag) false) false)))
        (check-sat)
    "#,
    );
    let action = original.declare_action("native initialization");
    for clause in original.clauses_mut() {
        clause.action_id = Some(action);
    }
    let pruned = original.pruned_false_query_ids();
    assert_eq!(pruned.len(), 1);
    let transformed = Box::new(ConstantPropagator::new()).transform(original.clone());
    assert_eq!(transformed.problem.action_names(), original.action_names());
    assert_eq!(transformed.problem.pruned_false_query_ids(), pruned);
    for (before, after) in original.clauses().iter().zip(transformed.problem.clauses()) {
        assert_eq!(after.action_id, before.action_id);
        assert_eq!(after.source_query_ordinal, before.source_query_ordinal);
    }
    transformed
        .problem
        .validate()
        .expect("projected query registry");
}
