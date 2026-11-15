// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! UNRUN real original-clause checks and candidate PDR search. These semantic
//! fixtures are not MODEL_CHECKER_CONSUMER typed/source consumer acceptance. Root must run
//! them only under the reviewed serial resource guard and Trust toolchain.

use super::super::{run, run_observed};
use super::run::{configured, deadline};
use super::*;
use crate::problem::ArrayScalarizedArg;
use crate::{PdrResult, VerifiedChcResult};

fn validate(lifted: InvariantModel, original: &ChcProblem) -> VerifiedChcResult {
    let until = deadline();
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(until));
    super::super::super::validate_pdr_proof_result(
        original,
        PdrResult::Safe(lifted),
        &configured(),
        Some(until),
    )
}

#[test]
fn real_original_validator_admits_body_write9_read9_model() {
    let original = source(9, false);
    let projected = project(&original);
    let lifted = projected
        .lift(&candidate(projected.reduced()), &mut || true)
        .unwrap();
    assert!(validate(lifted, &original).is_safe());
}

#[test]
fn real_original_validator_admits_four_iteration_exit_write9_read9_model() {
    let original = source(9, true);
    let projected = project(&original);
    let lifted = projected
        .lift(&candidate(projected.reduced()), &mut || true)
        .unwrap();
    assert!(validate(lifted, &original).is_safe());
}

#[test]
fn real_original_validator_refuses_body_and_exit_assert10_candidates() {
    for exit in [false, true] {
        let original = source(10, exit);
        let projected = project(&original);
        let lifted = projected
            .lift(&candidate(projected.reduced()), &mut || true)
            .unwrap();
        assert!(!validate(lifted, &original).is_safe());
    }
}

#[test]
fn real_original_validator_refuses_changed_store_initializer_and_store_key() {
    for (written, initial, key) in [(8, 5, 1), (9, 7, 1), (9, 5, 2)] {
        let original = source_values(9, false, written, initial, key);
        let projected = project(&original);
        let lifted = projected
            .lift(&candidate(projected.reduced()), &mut || true)
            .unwrap();
        assert!(
            !validate(lifted, &original).is_safe(),
            "{written}/{initial}/{key}"
        );
    }
}

#[test]
fn a_typed_but_forged_observation_key_has_no_original_verification_authority() {
    let original = source(9, false);
    let mut projected = project(&original);
    let reduced_model = candidate(projected.reduced());
    for mapping in projected.map.pred_args.values_mut() {
        for entry in mapping {
            if let ArrayScalarizedArg::Select { index, .. } = entry {
                *index = bv(2, 64);
            }
        }
    }
    // Structurally valid map != semantically correct candidate or proof.
    let lifted = projected.lift(&reduced_model, &mut || true).unwrap();
    assert!(!validate(lifted, &original).is_safe());
}

#[test]
fn real_validator_refusal_returns_fallback_not_safe_from_the_candidate_lane() {
    let original = source(10, false);
    let result = run_observed(
        &original,
        &configured(),
        Some(deadline()),
        &mut |reduced, _| PdrResult::Safe(candidate(reduced)),
        &mut |lifted, config, until| {
            super::super::super::validate_pdr_proof_result(
                &original,
                PdrResult::Safe(lifted),
                config,
                until,
            )
        },
        &mut |_| {},
    );
    assert!(result.is_none());
}

#[test]
fn real_candidate_search_proves_original_body_write9_read9() {
    let original = source(9, false);
    let before = original.clone();
    let result =
        run(&original, &configured(), Some(deadline())).expect("read-aware Safe candidate");
    assert!(result.is_safe());
    same_source(&before, &original);
}

#[test]
fn real_candidate_search_proves_original_exit_write9_read9() {
    let original = source(9, true);
    let result =
        run(&original, &configured(), Some(deadline())).expect("read-aware exit Safe candidate");
    assert!(result.is_safe());
}
