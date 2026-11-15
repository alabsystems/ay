// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Injected control-flow tests, not safety proofs. Both search and validation
//! are test closures: these tests never call PDR/SMT or the real validator.

use super::super::{run_observed, Phase};
use super::*;
use crate::engine_result::ValidationEvidence;
use crate::{CancellationToken, ChcEngineResult, PdrConfig, PdrResult, VerifiedChcResult};
use ay_core::time::Instant;
use std::time::Duration;

mod ambient;
mod controls;

fn configured() -> PdrConfig {
    PdrConfig {
        strict_proofs: true,
        preserve_original_clauses: true,
        solve_timeout: Some(Duration::from_secs(60)),
        ..PdrConfig::production(false)
    }
}

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn phases() -> [Phase; 7] {
    [
        Phase::Projection,
        Phase::Search,
        Phase::Lift,
        Phase::Validation,
        Phase::Validated,
        Phase::Publication,
        Phase::Cleanup,
    ]
}

// Test-only simulated validator result. This deliberately does not constitute
// original-clause verification or evidence that the R22 query is solved.
fn fake_safe(model: InvariantModel) -> VerifiedChcResult {
    VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(model),
        ValidationEvidence::FullVerification,
    )
}

fn fake_unknown() -> VerifiedChcResult {
    VerifiedChcResult::from_validated(
        ChcEngineResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

fn assert_original_signature(original: &ChcProblem, model: &InvariantModel) {
    assert_eq!(model.len(), original.predicates().len());
    for predicate in original.predicates() {
        assert_eq!(
            model
                .get(&predicate.id)
                .unwrap()
                .vars
                .iter()
                .map(|var| var.sort.clone())
                .collect::<Vec<_>>(),
            predicate.arg_sorts
        );
    }
}

#[test]
fn simulated_safe_search_must_pass_the_original_signature_validator_before_publication() {
    let original = source();
    let before = format!("{original:?}");
    for accept in [false, true] {
        let until = deadline();
        let mut searched = 0;
        let mut validated = 0;
        let mut observed = Vec::new();
        let result = run_observed(
            &original,
            &configured(),
            Some(until),
            &mut |reduced, config| {
                searched += 1;
                assert_fixed_erasure(&original, reduced);
                assert!(config.strict_proofs && config.preserve_original_clauses);
                PdrResult::Safe(model(reduced))
            },
            &mut |lifted, config, clock| {
                validated += 1;
                assert_original_signature(&original, &lifted);
                assert!(config.strict_proofs && config.preserve_original_clauses);
                assert_eq!(clock, Some(until));
                if accept {
                    fake_safe(lifted)
                } else {
                    fake_unknown()
                }
            },
            &mut |phase| observed.push(phase),
        );
        assert_eq!((searched, validated), (1, 1));
        if accept {
            assert!(result.unwrap().is_safe());
            assert_eq!(observed, phases());
        } else {
            assert!(
                result.is_none(),
                "refused candidate permits ordinary fallback"
            );
            assert_eq!(
                observed,
                phases()
                    .into_iter()
                    .filter(|phase| *phase != Phase::Publication)
                    .collect::<Vec<_>>()
            );
        }
        assert_eq!(format!("{original:?}"), before);
    }
}

#[test]
fn projected_unsafe_unknown_and_not_applicable_never_acquire_original_authority() {
    let original = source();
    for raw in [
        PdrResult::Unsafe(crate::Counterexample::new(Vec::new())),
        PdrResult::Unknown,
        PdrResult::NotApplicable,
    ] {
        let mut raw = Some(raw);
        let mut observed = Vec::new();
        let result = run_observed(
            &original,
            &configured(),
            Some(deadline()),
            &mut |_, _| raw.take().unwrap(),
            &mut |_, _, _| panic!("non-Safe projection must not be validated"),
            &mut |phase| observed.push(phase),
        );
        assert!(raw.is_none(), "injected search really ran");
        assert!(result.is_none());
        assert_eq!(observed, [Phase::Projection, Phase::Search, Phase::Cleanup]);
    }
}

#[test]
fn malformed_projected_model_is_not_forwarded_to_original_validation() {
    let original = source();
    let mut observed = Vec::new();
    let result = run_observed(
        &original,
        &configured(),
        Some(deadline()),
        &mut |reduced, _| {
            let mut candidate = model(reduced);
            candidate
                .interpretations
                .remove(&reduced.lookup_predicate("body").unwrap());
            PdrResult::Safe(candidate)
        },
        &mut |_, _, _| panic!("partial interpretation inventory must not reach validation"),
        &mut |phase| observed.push(phase),
    );
    assert!(result.is_none());
    assert_eq!(
        observed,
        [
            Phase::Projection,
            Phase::Search,
            Phase::Lift,
            Phase::Cleanup
        ]
    );
}

struct NoHints;

impl crate::lemma_hints::LemmaHintProvider for NoHints {
    fn collect(
        &self,
        _: &crate::lemma_hints::HintRequest<'_>,
        _: &mut Vec<crate::lemma_hints::LemmaHint>,
    ) {
        panic!("a source-bound provider must not be invoked by the prepass");
    }
}

#[test]
fn source_bound_hooks_skip_search_instead_of_rebinding_original_positions() {
    let original = source();
    for case in 0..11 {
        let mut config = configured();
        match case {
            0 => config.enable_tla_trace = true,
            1 => config.tla_trace_path = Some("unused-test-trace".into()),
            2 => config.user_hints.push(crate::lemma_hints::LemmaHint::new(
                original.predicates()[0].id,
                ChcExpr::Bool(true),
                0,
                "test-only",
            )),
            3 => config.user_hint_providers.0.push(Arc::new(NoHints)),
            4 => config.lemma_hints = Some(crate::lemma_pool::LemmaPool::new()),
            5 => config.lemma_cache = Some(crate::lemma_cache::LemmaCache::new()),
            6 => config.blackboard = Some(crate::blackboard::SharedBlackboard::new()),
            7 => config.bv_bit_groups.push((0, 64)),
            8 => config
                .array_scalarization_extra_indices
                .push((ChcSort::BitVec(64), ChcExpr::BitVec(0, 64))),
            9 => config.bv_to_int_relaxed = true,
            _ => {
                config.progress_snapshot =
                    Some(Arc::new(crate::progress::ChcProgressSnapshot::new(3)))
            }
        }
        let mut observed = Vec::new();
        assert!(run_observed(
            &original,
            &config,
            Some(deadline()),
            &mut |_, _| panic!("source-bound case {case} must not search"),
            &mut |_, _, _| panic!("source-bound case {case} must not validate"),
            &mut |phase| observed.push(phase),
        )
        .is_none());
        assert_eq!(observed, [Phase::Cleanup]);
    }
}

#[test]
fn absent_array_columns_or_absolute_clock_never_start_optional_search() {
    let array = source();
    let scalar = ChcParser::parse(R22_SCALAR).unwrap();
    for (problem, clock) in [(&array, None), (&scalar, Some(deadline()))] {
        assert!(run_observed(
            problem,
            &configured(),
            clock,
            &mut |_, _| panic!("inapplicable source must not search"),
            &mut |_, _, _| panic!("inapplicable source must not validate"),
            &mut |_| {},
        )
        .is_none());
    }
}
