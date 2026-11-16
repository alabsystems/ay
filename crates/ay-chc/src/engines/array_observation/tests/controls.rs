// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{run_observed, Phase};
use super::run::{configured, deadline, fake_safe, phases};
use super::*;
use crate::{CancellationToken, PdrResult};
use ay_core::time::Instant;
use std::time::Duration;

mod ambient;

#[test]
fn caller_cancellation_is_sticky_at_every_phase_including_cleanup_and_parent_reset() {
    let original = source(9, false);
    for external in [false, true] {
        for stop in phases() {
            let parent = CancellationToken::new();
            let mut config = configured();
            if external {
                config.external_cancellation_token = Some(parent.clone());
            } else {
                config.cancellation_token = Some(parent.clone());
            }
            let mut observed = Vec::new();
            let result = run_observed(
                &original,
                &config,
                Some(deadline()),
                &mut |reduced, _| PdrResult::Safe(candidate(reduced)),
                &mut |lifted, _, _| fake_safe(lifted),
                &mut |phase| {
                    observed.push(phase);
                    if phase == stop {
                        parent.cancel();
                    }
                    if phase == Phase::Cleanup && stop != Phase::Cleanup {
                        parent.reset();
                    }
                },
            )
            .unwrap();
            assert!(result.is_unknown(), "external={external} phase={stop:?}");
            assert!(observed.contains(&stop));
            assert_eq!(observed.last(), Some(&Phase::Cleanup));
        }
    }
}

#[test]
fn expired_caller_clock_precancelled_channels_and_zero_term_memory_never_search() {
    let original = source(9, false);
    for case in 0..4 {
        let parent = CancellationToken::new();
        let mut config = configured();
        let until = if case == 0 {
            Instant::now()
                .checked_sub(Duration::from_secs(1))
                .expect("fixture instant supports a one-second offset")
        } else {
            deadline()
        };
        if case == 1 {
            config.cancellation_token = Some(parent.clone());
            parent.cancel();
        }
        if case == 2 {
            config.external_cancellation_token = Some(parent.clone());
            parent.cancel();
        }
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(if case == 3 {
            Some(0)
        } else {
            None
        });
        let mut observed = Vec::new();
        let result = run_observed(
            &original,
            &config,
            Some(until),
            &mut |_, _| panic!("caller already stopped"),
            &mut |_, _, _| panic!("no candidate"),
            &mut |phase| observed.push(phase),
        )
        .unwrap();
        assert!(result.is_unknown());
        assert_eq!(observed, [Phase::Cleanup]);
    }
}

#[test]
fn speculative_child_stop_is_local_but_observed_caller_stop_remains_terminal() {
    let original = source(9, false);
    for external in [false, true] {
        for caller in [false, true] {
            let parent = CancellationToken::new();
            let mut config = configured();
            if external {
                config.external_cancellation_token = Some(parent.clone());
            } else {
                config.cancellation_token = Some(parent.clone());
            }
            let result = run_observed(
                &original,
                &config,
                Some(deadline()),
                &mut |_, search| {
                    let token = if external {
                        search.external_cancellation_token.as_ref()
                    } else {
                        search.cancellation_token.as_ref()
                    }
                    .unwrap();
                    if caller {
                        parent.cancel();
                    } else {
                        token.cancel();
                    }
                    assert!(token.is_cancelled());
                    parent.reset();
                    PdrResult::Unknown
                },
                &mut |_, _, _| panic!("Unknown does not validate"),
                &mut |_| {},
            );
            if caller {
                assert!(result.unwrap().is_unknown());
            } else {
                assert!(result.is_none());
            }
        }
    }
}

#[test]
fn caller_cleanup_stop_dominates_channel_inapplicability_and_local_search_refusal() {
    let original = source(9, false);
    for inapplicable in [false, true] {
        let parent = CancellationToken::new();
        let mut config = configured();
        config.external_cancellation_token = Some(parent.clone());
        config.enable_tla_trace = inapplicable;
        let result = run_observed(
            &original,
            &config,
            Some(deadline()),
            &mut |_, _| PdrResult::Unknown,
            &mut |_, _, _| panic!("no candidate"),
            &mut |phase| {
                if phase == Phase::Cleanup {
                    parent.cancel();
                }
            },
        )
        .unwrap();
        assert!(result.is_unknown());
    }
}

#[test]
fn each_projection_and_lift_checkpoint_can_refuse_without_mutating_borrowed_inputs() {
    let original = source(9, false);
    let before = original.clone();
    let mut total = 0usize;
    let projected = Projection::new(&original, &mut || {
        total += 1;
        true
    })
    .unwrap();
    for stop in 1..=total {
        let mut calls = 0usize;
        assert!(Projection::new(&original, &mut || {
            calls += 1;
            calls < stop
        })
        .is_none());
        assert_eq!(calls, stop);
    }
    let model = candidate(projected.reduced());
    let mut total = 0usize;
    projected
        .lift(&model, &mut || {
            total += 1;
            true
        })
        .unwrap();
    for stop in 1..=total {
        let mut calls = 0usize;
        assert!(projected
            .lift(&model, &mut || {
                calls += 1;
                calls < stop
            })
            .is_none());
        assert_eq!(calls, stop);
    }
    same_source(&before, &original);
}

#[test]
fn original_deadline_and_term_memory_scope_survive_short_search_and_validation() {
    let original = source(9, false);
    let now = Instant::now();
    let until = now + Duration::from_secs(20);
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(until));
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(16 * 1024 * 1024));
    let result = run_observed(
        &original,
        &configured(),
        Some(until),
        &mut |reduced, config| {
            assert!(config.solve_timeout.unwrap() <= Duration::from_secs(4));
            assert!(crate::smt::current_thread_solve_deadline().unwrap() < until);
            assert_eq!(
                crate::smt::SmtContext::current_thread_term_memory_budget(),
                Some(16 * 1024 * 1024)
            );
            PdrResult::Safe(candidate(reduced))
        },
        &mut |lifted, _, clock| {
            assert_eq!(clock, Some(until));
            assert_eq!(crate::smt::current_thread_solve_deadline(), Some(until));
            assert_eq!(
                crate::smt::SmtContext::current_thread_term_memory_budget(),
                Some(16 * 1024 * 1024)
            );
            fake_safe(lifted)
        },
        &mut |_| {},
    )
    .unwrap();
    assert!(result.is_safe());
    assert_eq!(crate::smt::current_thread_solve_deadline(), Some(until));
}
