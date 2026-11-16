// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! UNRUN injected lifecycle controls, not solver or replay evidence.

use super::super::{run_observed, Phase};
use super::run::{configured, deadline, fake_safe, fake_unknown};
use super::static_hints_support::{hint_snapshot, scalar_hint, typed_shape};
use super::*;
use crate::{CancellationToken, LemmaHint, PdrResult};
use ay_core::time::Instant;
use std::time::Duration;

struct NoHints;

impl crate::lemma_hints::LemmaHintProvider for NoHints {
    fn collect(&self, _: &crate::lemma_hints::HintRequest<'_>, _: &mut Vec<LemmaHint>) {
        panic!("a guarded provider must not be called by array observation");
    }
}

#[test]
fn projected_search_gets_rebased_hints_and_original_validation_gets_original_hints() {
    let original = typed_shape(9);
    let before = original.clone();
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1)];
    let snapshot = hint_snapshot(&config.user_hints);
    let mut searched = false;
    let mut validated = false;
    let result = run_observed(
        &original,
        &config,
        Some(deadline()),
        &mut |reduced, search| {
            searched = true;
            let id = original.lookup_predicate("H").unwrap();
            assert_eq!(
                search.user_hints[0].formula,
                operation(
                    ChcOp::BvULe,
                    variable(&crate::canonical_var_name(id, 2), ChcSort::BitVec(64)),
                    bv(4, 64)
                )
            );
            assert_eq!(reduced.predicates()[0].arg_sorts.len(), 3);
            let projected = project(&original);
            PdrResult::Safe(super::static_hints_support::shape_candidate(&projected))
        },
        &mut |lifted, validation, _| {
            validated = true;
            assert_eq!(hint_snapshot(&validation.user_hints), snapshot);
            assert_eq!(
                lifted.get(&original.predicates()[0].id).unwrap().vars.len(),
                2
            );
            fake_safe(lifted)
        },
        &mut |_| {},
    );
    assert!(result.unwrap().is_safe());
    assert!(searched && validated);
    assert_eq!(hint_snapshot(&config.user_hints), snapshot);
    same_source(&before, &original);
}

#[test]
fn one_unsupported_hint_declines_the_whole_attempt_without_dropping_valid_hints() {
    let original = source(9, false);
    let before = original.clone();
    let mut config = configured();
    config.user_hints = vec![
        scalar_hint(&original, "H", 1),
        LemmaHint::new(
            original.predicates()[0].id,
            variable("free", ChcSort::Bool),
            1,
            "unsupported",
        ),
    ];
    let snapshot = hint_snapshot(&config.user_hints);
    assert!(run_observed(
        &original,
        &config,
        Some(deadline()),
        &mut |_, _| panic!("whole batch must decline"),
        &mut |_, _, _| panic!("no candidate"),
        &mut |_| {}
    )
    .is_none());
    assert_eq!(hint_snapshot(&config.user_hints), snapshot);
    same_source(&before, &original);
}

#[test]
fn static_hint_support_never_reuses_dynamic_cache_trace_bv_or_extra_key_channels() {
    let original = source(9, false);
    for case in 0..10 {
        let mut config = configured();
        config.user_hints = vec![scalar_hint(&original, "H", 1)];
        match case {
            0 => config.enable_tla_trace = true,
            1 => config.tla_trace_path = Some("never-opened-trace".into()),
            2 => config.user_hint_providers.0.push(Arc::new(NoHints)),
            3 => config.lemma_hints = Some(crate::lemma_pool::LemmaPool::new()),
            4 => config.lemma_cache = Some(crate::lemma_cache::LemmaCache::new()),
            5 => config.blackboard = Some(crate::blackboard::SharedBlackboard::new()),
            6 => config.bv_bit_groups.push((0, 64)),
            7 => config
                .array_scalarization_extra_indices
                .push((ChcSort::BitVec(64), bv(1, 64))),
            8 => config.bv_to_int_relaxed = true,
            _ => {
                config.progress_snapshot =
                    Some(Arc::new(crate::progress::ChcProgressSnapshot::new(3)))
            }
        }
        let snapshot = hint_snapshot(&config.user_hints);
        let mut observed = Vec::new();
        assert!(run_observed(
            &original,
            &config,
            Some(deadline()),
            &mut |_, _| panic!("untranslated channel {case}"),
            &mut |_, _, _| panic!("no candidate"),
            &mut |phase| observed.push(phase)
        )
        .is_none());
        assert_eq!(observed, [Phase::Cleanup]);
        assert_eq!(hint_snapshot(&config.user_hints), snapshot);
    }
}

#[test]
fn erasure_candidate_still_declines_static_hints_without_its_own_bridge() {
    let original = source(9, false);
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1)];
    assert!(super::super::super::array_projection::source_bound_channels(&config));
    assert!(!super::super::super::array_projection::untranslated_source_bound_channels(&config));
}

#[test]
fn original_cancellation_at_new_hint_phases_remains_sticky_through_cleanup_reset() {
    let original = typed_shape(9);
    for external in [false, true] {
        for stop in [Phase::HintAdmission, Phase::HintRebase] {
            let parent = CancellationToken::new();
            let mut config = configured();
            config.user_hints = vec![scalar_hint(&original, "H", 1)];
            if external {
                config.external_cancellation_token = Some(parent.clone());
            } else {
                config.cancellation_token = Some(parent.clone());
            }
            let snapshot = hint_snapshot(&config.user_hints);
            let mut observed = Vec::new();
            let result = run_observed(
                &original,
                &config,
                Some(deadline()),
                &mut |_, _| panic!("stopped before search"),
                &mut |_, _, _| panic!("no candidate"),
                &mut |phase| {
                    observed.push(phase);
                    if phase == stop {
                        parent.cancel();
                    }
                    if phase == Phase::Cleanup {
                        parent.reset();
                    }
                },
            )
            .unwrap();
            assert!(result.is_unknown());
            assert!(observed.contains(&stop));
            assert_eq!(observed.last(), Some(&Phase::Cleanup));
            assert_eq!(hint_snapshot(&config.user_hints), snapshot);
        }
    }
}

#[test]
fn stopped_caller_clock_channels_and_term_memory_never_scan_or_search_hints() {
    let original = source(9, false);
    for case in 0..4 {
        let mut config = configured();
        config.user_hints = vec![scalar_hint(&original, "H", 1)];
        let parent = CancellationToken::new();
        if case == 1 {
            parent.cancel();
            config.cancellation_token = Some(parent.clone());
        }
        if case == 2 {
            parent.cancel();
            config.external_cancellation_token = Some(parent);
        }
        let until = if case == 0 {
            Instant::now()
                .checked_sub(Duration::from_secs(1))
                .expect("fixture instant supports a one-second offset")
        } else {
            deadline()
        };
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(if case == 3 {
            Some(0)
        } else {
            None
        });
        let mut observed = Vec::new();
        assert!(run_observed(
            &original,
            &config,
            Some(until),
            &mut |_, _| panic!("caller stopped"),
            &mut |_, _, _| panic!("no candidate"),
            &mut |phase| observed.push(phase)
        )
        .unwrap()
        .is_unknown());
        assert_eq!(observed, [Phase::Cleanup]);
    }
}

#[test]
fn over_cap_hint_batch_refuses_before_projection_and_keeps_fallback_inputs() {
    let original = typed_shape(9);
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1); super::super::hints::MAX_HINTS + 1];
    let snapshot = hint_snapshot(&config.user_hints);
    let mut observed = Vec::new();
    assert!(run_observed(
        &original,
        &config,
        Some(deadline()),
        &mut |_, _| panic!("batch exceeded admission"),
        &mut |_, _, _| panic!("no candidate"),
        &mut |phase| observed.push(phase)
    )
    .is_none());
    assert_eq!(observed, [Phase::HintAdmission, Phase::Cleanup]);
    assert_eq!(hint_snapshot(&config.user_hints), snapshot);
}

#[test]
fn original_validator_refusal_dominates_a_rebased_hint_and_safe_search_candidate() {
    let original = source(9, false);
    let mut config = configured();
    config.user_hints = vec![scalar_hint(&original, "H", 1)];
    assert!(run_observed(
        &original,
        &config,
        Some(deadline()),
        &mut |reduced, _| PdrResult::Safe(candidate(reduced)),
        &mut |_, _, _| fake_unknown(),
        &mut |_| {}
    )
    .is_none());
}
