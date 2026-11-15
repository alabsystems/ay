// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::validate_ground_derivation_with_progress;
use crate::{ChcParser, ChcSort, ChcVar};
use fixtures::{problem, source, Site};

fn candidate(problem: &ChcProblem, depth: usize) -> Option<GroundDerivation> {
    ground_linear_refutation(problem, depth, &mut || true).expect("healthy ground search")
}

fn validates(problem: &ChcProblem, derivation: &GroundDerivation) -> bool {
    validate_ground_derivation_with_progress(problem, derivation, &mut || true).is_ok()
}

#[test]
fn complete_array_exit_requires_eight_edges_and_ten_original_steps() {
    let original = problem(Site::Exit, 9, 10);
    assert!(candidate(&original, 7).is_none());
    let derivation = candidate(&original, 8).expect("four original iterations");
    assert_eq!(derivation.len(), 10);
    assert_eq!(derivation.query_step, 9);
    assert_eq!(derivation.steps[0].clause_index, 0);
    assert_eq!(derivation.steps[9].clause_index, 3);
    assert!(validates(&original, &derivation));
    for (index, step) in derivation.steps.iter().enumerate().skip(1) {
        assert_eq!(step.premises, vec![index - 1]);
    }
}

#[test]
fn body_and_exit_arrays_keep_the_unobserved_total_default() {
    for site in [Site::Body, Site::Exit] {
        let original = problem(site, 9, 10);
        let derivation = candidate(&original, 8).expect("original violation");
        assert!(validates(&original, &derivation));
        let env = &derivation.steps[derivation.query_step].env;
        let array = env
            .values()
            .find(|value| matches!(value, SmtValue::ArrayMap { .. }))
            .expect("complete carried nonconstant array");
        let SmtValue::ArrayMap { default, entries } = array else {
            unreachable!()
        };
        assert_eq!(default.as_ref(), &SmtValue::BitVec(5, 32));
        assert!(entries.iter().any(
            |(key, value)| key == &SmtValue::BitVec(1, 64) && value == &SmtValue::BitVec(9, 32)
        ));
    }
}

#[test]
fn safe_nine_and_store_ten_never_propose_a_refutation() {
    for site in [Site::Body, Site::Exit] {
        for (store, expected) in [(9, 9), (10, 10)] {
            assert!(candidate(&problem(site, store, expected), 8).is_none());
        }
    }
}

#[test]
fn changed_source_cannot_validate_the_old_store_nine_assignment() {
    let original = problem(Site::Exit, 9, 10);
    let derivation = candidate(&original, 8).expect("original violation");
    for (store, expected) in [(9, 9), (10, 10), (8, 10)] {
        let changed = problem(Site::Exit, store, expected);
        assert!(
            !validates(&changed, &derivation),
            "old values are not new source authority"
        );
        if store == 8 {
            let fresh = candidate(&changed, 8).expect("new source still violates ten");
            assert!(validates(&changed, &fresh));
        }
    }
}

#[test]
fn extra_guard_variable_is_not_defaulted_or_searched() {
    let input = source(Site::Exit, 9, 10)
        .replace("(i (_ BitVec 64)))", "(i (_ BitVec 64)) (j (_ BitVec 64)))")
        .replace(
            "(bvuge i #x0000000000000004)",
            "(and (bvuge i #x0000000000000004) (= j #x0000000000000000))",
        );
    let original = ChcParser::parse(&input).expect("unbound clause-local source variable");
    assert!(candidate(&original, 8).is_none());
}

#[test]
fn composite_body_argument_is_not_inverted_or_guessed() {
    let input =
        source(Site::Exit, 9, 10).replace("(=> (B a i)", "(=> (B a (bvadd i #x0000000000000001))");
    let original = ChcParser::parse(&input).expect("typed composite body argument");
    assert!(candidate(&original, 8).is_none());
}

#[test]
fn malformed_body_variable_sort_refuses_before_evaluation() {
    let mut original = problem(Site::Exit, 9, 10);
    let arguments = &mut original.clauses_mut()[1].body.predicates[0].1;
    let ChcExpr::Var(variable) = &arguments[0] else {
        panic!("array source variable")
    };
    arguments[0] = ChcExpr::Var(ChcVar::new(variable.name.clone(), ChcSort::Int));
    assert!(ground_linear_refutation(&original, 8, &mut || true).is_err());
}

#[test]
fn missing_binding_and_stale_premise_are_independently_rejected() {
    let original = problem(Site::Exit, 9, 10);
    let derivation = candidate(&original, 8).expect("original violation");
    let mut missing = derivation.clone();
    missing.steps[1].env.clear();
    assert!(!validates(&original, &missing));
    let mut stale = derivation;
    stale.steps[9].premises[0] = 0;
    assert!(!validates(&original, &stale));
}

#[test]
fn complete_array_default_is_not_an_observed_key_approximation() {
    let original = problem(Site::Exit, 9, 10);
    let mut derivation = candidate(&original, 8).expect("original violation");
    for value in derivation.steps[1].env.values_mut() {
        if let SmtValue::ConstArray(default) = value {
            **default = SmtValue::BitVec(6, 32);
        }
    }
    assert!(!validates(&original, &derivation));
}

#[test]
fn caller_refusal_and_terminal_refusal_cannot_return_a_candidate() {
    let original = problem(Site::Exit, 9, 10);
    let mut healthy_calls = 0usize;
    let result = ground_linear_refutation(&original, 8, &mut || {
        healthy_calls += 1;
        true
    })
    .expect("healthy reference");
    assert!(result.is_some());
    for reject_at in [
        1,
        healthy_calls / 3,
        healthy_calls / 2,
        healthy_calls - 1,
        healthy_calls,
    ] {
        let mut calls = 0;
        let refused = ground_linear_refutation(&original, 8, &mut || {
            calls += 1;
            calls != reject_at
        });
        assert_eq!(
            refused.expect_err("no candidate after observed false"),
            GroundDerivationError::Interrupted
        );
        assert_eq!(
            calls, reject_at,
            "sticky refusal never re-polls a recovering callback"
        );
    }
}

#[test]
fn true_ground_query_without_a_body_still_requires_independent_validation() {
    let original = ChcParser::parse("(set-logic HORN) (assert false) (check-sat)")
        .expect("original false fact");
    let derivation = candidate(&original, 0).expect("one true-body false head");
    assert_eq!(derivation.len(), 1);
    assert!(validates(&original, &derivation));
}

#[test]
fn repeated_body_variables_must_match_the_whole_typed_tuple() {
    let original = ChcParser::parse(
        "(set-logic HORN) (declare-fun p ((_ BitVec 8) (_ BitVec 8)) Bool)
         (assert (p #x01 #x02))
         (assert (forall ((x (_ BitVec 8))) (=> (p x x) false))) (check-sat)",
    )
    .expect("repeated exact body variable");
    assert!(candidate(&original, 8).is_none());
}
