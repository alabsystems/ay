// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! UNRUN real AY validation/search/artifact fixtures. Synthetic typed AY
//! constructors are not actual MODEL_CHECKER_CONSUMER fresh private replay or source binding.
//! Execute only with the reviewed serial resource guard and Trust toolchain.

use super::super::{run, run_observed};
use super::run::{configured, deadline};
use super::static_hints_support::{hint_snapshot, scalar_hint, shape_candidate, typed_shape};
use super::*;
use crate::{LemmaHint, PdrResult};

#[test]
fn real_original_validator_admits_shifted_typed_array_model_with_static_hint() {
    let original = typed_shape(9);
    let before = original.clone();
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1)];
    let snapshot = hint_snapshot(&config.user_hints);
    let candidate = shape_candidate(&project(&original));
    let result = run_observed(
        &original,
        &config,
        Some(deadline()),
        &mut |_, _| PdrResult::Safe(candidate.clone()),
        &mut |lifted, validation, until| {
            super::super::super::validate_pdr_proof_result(
                &original,
                PdrResult::Safe(lifted),
                validation,
                until,
            )
        },
        &mut |_| {},
    )
    .unwrap();
    assert!(result.is_safe());
    assert_eq!(hint_snapshot(&config.user_hints), snapshot);
    same_source(&before, &original);
}

#[test]
fn real_original_validator_refuses_false_typed_array_property_despite_static_hint() {
    let original = typed_shape(10);
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1)];
    let candidate = shape_candidate(&project(&original));
    let result = run_observed(
        &original,
        &config,
        Some(deadline()),
        &mut |_, _| PdrResult::Safe(candidate.clone()),
        &mut |lifted, validation, until| {
            super::super::super::validate_pdr_proof_result(
                &original,
                PdrResult::Safe(lifted),
                validation,
                until,
            )
        },
        &mut |_| {},
    );
    assert!(result.is_none());
}

#[test]
fn real_candidate_search_with_static_hint_retains_original_body_model_authority() {
    let original = source(9, false);
    let before = original.clone();
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1)];
    assert!(run(&original, &config, Some(deadline())).unwrap().is_safe());
    same_source(&before, &original);
}

#[test]
fn real_shifted_typed_proof_artifact_rebinds_to_fresh_original_not_projection() {
    let original = typed_shape(9);
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1)];
    let run = crate::engines::solve_pdr_proof(original.clone(), config.clone()).unwrap();
    assert!(run.result().is_safe());
    assert!(run.accepted_as_proof());
    same_source(&original, run.problem());
    let artifact = run.quantifier_free_invariant_model_artifact().unwrap();
    let fresh = typed_shape(9);
    let model = crate::parse_qf_invariant_model_artifact(&fresh, artifact.bytes()).unwrap();
    assert_eq!(model.get(&fresh.predicates()[0].id).unwrap().vars.len(), 2);
    assert!(crate::engines::validate_external_invariant_model(&fresh, &model, &config).unwrap());
    let projected = project(&fresh);
    assert!(
        crate::parse_qf_invariant_model_artifact(projected.reduced(), artifact.bytes()).is_err()
    );
    assert!(crate::parse_qf_invariant_model_artifact(&typed_shape(10), artifact.bytes()).is_err());
}

#[test]
fn poisoned_static_hint_never_proves_a_false_array_property_safe() {
    let original = typed_shape(10);
    let mut config = configured();
    config.user_hints = vec![LemmaHint::new(
        original.predicates()[0].id,
        ChcExpr::Bool(false),
        0,
        "poisoned-static-hint",
    )];
    let run = crate::engines::solve_pdr_proof(original, config).unwrap();
    assert!(!run.result().is_safe());
}
