// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::{
    validate_ground_derivation, validate_ground_derivation_with_progress,
};
use crate::{ChcExpr, ChcSort, ClauseBody, ClauseHead, HornClause};

fn input() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let fail = problem.declare_predicate("FAIL", vec![]);
    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        p,
        vec![ChcExpr::Int(0)],
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::Int(0)])], None),
        ClauseHead::Predicate(fail, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(fail, vec![])],
        None,
    )));
    problem
}

fn expanded_derivation() -> GroundDerivation {
    GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: FxHashMap::default(),
                premises: vec![0],
            },
        ],
        query_step: 1,
    }
}

fn fixture() -> (ChcProblem, NullaryExpansion, GroundDerivation) {
    let mut problem = input();
    let expansion = problem.expand_nullary_fail_queries_recorded(false).unwrap();
    assert_eq!(problem.clauses().len(), 2);
    assert_eq!(
        expansion.origins(),
        &[
            ExpandedClauseOrigin::Kept(0),
            ExpandedClauseOrigin::Expanded {
                into_fail: 1,
                fail_query: 2
            }
        ]
    );
    (problem, expansion, expanded_derivation())
}

#[test]
fn accepting_control_keeps_the_compatibility_mapping_and_original_validation() {
    let (problem, expansion, derivation) = fixture();
    let compatibility = expansion
        .translate_derivation(&derivation, problem.clauses().len())
        .unwrap();
    let controlled = expansion
        .translate_derivation_with_progress(&derivation, problem.clauses().len(), &mut || true)
        .unwrap()
        .unwrap();
    assert_eq!(format!("{compatibility:?}"), format!("{controlled:?}"));
    assert_eq!(
        controlled
            .steps
            .iter()
            .map(|s| s.clause_index)
            .collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
    assert_eq!(controlled.query_step, 2);
    assert_eq!(controlled.steps[2].premises, vec![1]);
    assert_eq!(validate_ground_derivation(&input(), &controlled), Ok(()));
}

#[test]
fn every_mapping_and_validation_observation_is_terminal_including_final_cleanup() {
    let (problem, expansion, derivation) = fixture();
    let mut observations = 0usize;
    assert!(expansion
        .translate_derivation_with_progress(&derivation, problem.clauses().len(), &mut || {
            observations += 1;
            true
        },)
        .unwrap()
        .is_some());
    assert!(observations > 10);
    for refusal in 1..=observations {
        let mut seen = 0usize;
        assert!(
            matches!(
                expansion.translate_derivation_with_progress(
                    &derivation,
                    problem.clauses().len(),
                    &mut || {
                        seen += 1;
                        seen != refusal
                    },
                ),
                Err(GroundDerivationError::Interrupted)
            ),
            "refusal {refusal}"
        );
        assert_eq!(seen, refusal, "no new accepting owner after a refusal");
    }
}

#[test]
fn native_validator_observes_the_same_owner_after_releasing_its_temporaries() {
    let (_, expansion, derivation) = fixture();
    let translated = expansion.translate_derivation(&derivation, 2).unwrap();
    let problem = input();
    let mut observations = 0usize;
    assert_eq!(
        validate_ground_derivation_with_progress(&problem, &translated, &mut || {
            observations += 1;
            true
        }),
        Ok(())
    );
    assert!(observations > 1);
    for refusal in 1..=observations {
        let mut seen = 0usize;
        assert_eq!(
            validate_ground_derivation_with_progress(&problem, &translated, &mut || {
                seen += 1;
                seen != refusal
            }),
            Err(GroundDerivationError::Interrupted)
        );
        assert_eq!(seen, refusal);
    }
}

#[test]
fn precancellation_is_not_count_or_empty_proof_rejection() {
    let (_, expansion, _) = fixture();
    let mut seen = 0usize;
    assert!(matches!(
        expansion.translate_derivation_with_progress(
            &GroundDerivation::default(),
            usize::MAX,
            &mut || {
                seen += 1;
                false
            },
        ),
        Err(GroundDerivationError::Interrupted)
    ));
    assert_eq!(seen, 1);
    assert_eq!(
        validate_ground_derivation_with_progress(
            &input(),
            &GroundDerivation::default(),
            &mut || false,
        ),
        Err(GroundDerivationError::Interrupted)
    );
}

#[test]
fn ordinary_mapping_rejection_remains_none_with_an_accepting_owner() {
    let (_, expansion, mut derivation) = fixture();
    derivation.steps[1].premises = vec![99];
    assert!(expansion
        .translate_derivation_with_progress(&derivation, 2, &mut || true,)
        .unwrap()
        .is_none());
    assert!(expansion.translate_derivation(&derivation, 2).is_none());
}

#[test]
fn equal_counts_and_in_range_origins_do_not_grant_original_proof_authority() {
    let expansion = NullaryExpansion::new(
        input(),
        vec![
            ExpandedClauseOrigin::Kept(0),
            ExpandedClauseOrigin::Expanded {
                into_fail: 0,
                fail_query: 2,
            },
        ],
    );
    // A valid index is not the original FAIL-producing clause. Only actual
    // native re-validation on the captured input can reject this substitution.
    assert!(expansion
        .translate_derivation_with_progress(&expanded_derivation(), 2, &mut || true,)
        .unwrap()
        .is_none());
}

#[test]
fn refusal_inside_native_validation_is_not_collapsed_to_lost_ground() {
    let (problem, expansion, derivation) = fixture();
    let mut mapping_calls = 0usize;
    assert!(expansion
        .map_derivation(&derivation, 2, &mut || {
            mapping_calls += 1;
            true
        })
        .is_some());
    // Initial outer poll + map polls + post-map poll + first native poll.
    let first_native = mapping_calls + 3;
    let mut seen = 0usize;
    assert!(matches!(
        expansion.translate_derivation_with_progress(
            &derivation,
            problem.clauses().len(),
            &mut || {
                seen += 1;
                seen != first_native
            },
        ),
        Err(GroundDerivationError::Interrupted)
    ));
    assert_eq!(seen, first_native);
}

#[test]
fn the_captured_input_keeps_its_own_frozen_pruned_registry_without_new_authority() {
    let mut original = input();
    let p = original.lookup_predicate("P").unwrap();
    original.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::Int(0)])],
        Some(ChcExpr::Bool(false)),
    )));
    original.preserve_pruned_query_source();
    assert!(original.validate().is_ok());
    let frozen = Arc::clone(original.pruned_query_source.as_ref().unwrap());
    let expansion = original
        .expand_nullary_fail_queries_recorded(false)
        .unwrap();
    assert!(Arc::ptr_eq(
        &frozen,
        expansion.input.pruned_query_source.as_ref().unwrap()
    ));
    assert!(expansion.input.validate().is_ok());
    let translated = expansion
        .translate_derivation_with_progress(&expanded_derivation(), 2, &mut || true)
        .unwrap()
        .unwrap();
    assert_eq!(
        validate_ground_derivation(&expansion.input, &translated),
        Ok(())
    );
    // This tests preservation, not independent native/wire admission of the
    // frozen registry: native ground replay authenticates live clauses only.
}
