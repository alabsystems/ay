// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Injected control-flow checks only: no BMC/SMT or real witness validation.
//! The synthetic Unsafe value below is not evidence of a source refutation.

use super::*;

#[test]
fn every_phase_refuses_both_caller_channels_after_observed_parent_reset() {
    let original = source();
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
                &mut |_, _, _| Some(candidate()),
                &mut |candidate, _, _| fake_unsafe(candidate),
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
            .expect("observed original cancellation must forbid fallback");
            assert!(result.is_unknown(), "external={external}, stop={stop:?}");
            assert!(observed.contains(&stop));
            assert_eq!(observed.last(), Some(&Phase::Cleanup));
            let ordinal = phases().iter().position(|phase| *phase == stop).unwrap();
            for later in &phases()[ordinal + 1..] {
                if *later != Phase::Cleanup {
                    assert!(!observed.contains(later));
                }
            }
            parent.reset();
            assert!(!parent.is_cancelled());
        }
    }
}

#[test]
fn descendant_caller_observation_sticks_but_local_search_cancel_allows_fallback() {
    let original = source();
    for external in [false, true] {
        for caller_cancel in [false, true] {
            let parent = CancellationToken::new();
            let mut config = configured();
            if external {
                config.external_cancellation_token = Some(parent.clone());
            } else {
                config.cancellation_token = Some(parent.clone());
            }
            let mut searched = false;
            let result = run_observed(
                &original,
                &config,
                Some(deadline()),
                &mut |_, _, configured| {
                    searched = true;
                    // BMC consumes the primary channel: both caller channels
                    // must reach this linked child without cancelling parents.
                    let child = configured.cancellation_token.as_ref().unwrap();
                    if caller_cancel {
                        parent.cancel();
                    } else {
                        child.cancel();
                    }
                    assert!(child.is_cancelled());
                    parent.reset();
                    None
                },
                &mut |_, _, _| panic!("no witness must not validate"),
                &mut |_| {},
            );
            assert!(searched);
            assert!(!parent.is_cancelled());
            if caller_cancel {
                assert!(result.unwrap().is_unknown());
            } else {
                assert!(result.is_none(), "local cancellation permits fallback");
            }
        }
    }
}

#[test]
fn cleanup_stop_dominates_missing_clock_and_witness_free_search() {
    let original = source();
    for clock in [None, Some(deadline())] {
        let parent = CancellationToken::new();
        let mut config = configured();
        config.external_cancellation_token = Some(parent.clone());
        let mut searched = 0;
        let result = run_observed(
            &original,
            &config,
            clock,
            &mut |_, _, _| {
                searched += 1;
                None
            },
            &mut |_, _, _| panic!("no witness must not validate"),
            &mut |phase| {
                if phase == Phase::Cleanup {
                    parent.cancel();
                }
            },
        )
        .unwrap();
        assert!(result.is_unknown());
        assert_eq!(searched, usize::from(clock.is_some()));
    }
}

#[test]
fn expired_original_deadline_precancellation_and_zero_memory_skip_search() {
    let original = source();
    for case in 0..4 {
        let mut config = configured();
        let parent = CancellationToken::new();
        let until = if case == 0 {
            Instant::now() - Duration::from_secs(1)
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
            &mut |_, _, _| panic!("closed caller must not search"),
            &mut |_, _, _| panic!("closed caller must not validate"),
            &mut |phase| observed.push(phase),
        )
        .unwrap();
        assert!(result.is_unknown());
        assert_eq!(observed, [Phase::Cleanup]);
    }
}

#[test]
fn short_search_clock_restores_original_validation_and_ambient_scopes() {
    let original = source();
    let now = Instant::now();
    let supplied = now + Duration::from_secs(80);
    let solve = now + Duration::from_secs(70);
    let smt = now + Duration::from_secs(60);
    let old_solve = crate::smt::current_thread_solve_deadline();
    let old_smt = crate::smt::deadline::current_smt_deadline();
    let old_memory = crate::smt::SmtContext::current_thread_term_memory_budget();
    {
        let _solve = crate::smt::ScopedSolveDeadline::new(Some(solve));
        let _smt = crate::smt::ScopedSmtDeadline::install_until(smt);
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(4096));
        let mut observed = Vec::new();
        let result = run_observed(
            &original,
            &configured(),
            Some(supplied),
            &mut |actual, budget, config| {
                assert!(std::ptr::eq(actual, &original));
                let short = crate::smt::current_thread_solve_deadline().unwrap();
                assert!(short < smt);
                assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(short));
                assert!(budget >= Duration::from_millis(250));
                assert!(budget <= Duration::from_secs(4));
                assert!(config.strict_proofs && config.preserve_original_clauses);
                assert_eq!(
                    crate::smt::SmtContext::current_thread_term_memory_budget(),
                    Some(4096)
                );
                Some(candidate())
            },
            &mut |candidate, _, clock| {
                assert_eq!(clock, Some(smt));
                assert_eq!(crate::smt::current_thread_solve_deadline(), Some(smt));
                assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(smt));
                fake_unsafe(candidate)
            },
            &mut |phase| observed.push(phase),
        )
        .unwrap();
        assert!(result.is_unsafe());
        assert_eq!(observed, phases());
        assert_eq!(crate::smt::current_thread_solve_deadline(), Some(solve));
        assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(smt));
        assert_eq!(
            crate::smt::SmtContext::current_thread_term_memory_budget(),
            Some(4096)
        );
    }
    assert_eq!(crate::smt::current_thread_solve_deadline(), old_solve);
    assert_eq!(crate::smt::deadline::current_smt_deadline(), old_smt);
    assert_eq!(
        crate::smt::SmtContext::current_thread_term_memory_budget(),
        old_memory
    );
}

#[test]
fn injected_search_and_restricted_subsetup_panics_unwind_scopes_without_source_mutation() {
    let original = source();
    let before = format!("{original:?}");
    for cleanup in [false, true] {
        let until = deadline();
        let _solve = crate::smt::ScopedSolveDeadline::new(Some(until));
        let old_smt = crate::smt::deadline::current_smt_deadline();
        let old_memory = crate::smt::SmtContext::current_thread_term_memory_budget();
        let mut searched = false;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_observed(
                &original,
                &configured(),
                Some(until),
                &mut |_, _, _| {
                    searched = true;
                    assert!(cleanup, "injected search panic");
                    Some(candidate())
                },
                &mut |candidate, _, _| fake_unsafe(candidate),
                &mut |phase| {
                    assert!(
                        !(cleanup && phase == Phase::Cleanup),
                        "injected cleanup panic"
                    );
                },
            )
        }));
        assert!(searched);
        assert!(result.is_err());
        assert_eq!(format!("{original:?}"), before);
        assert_eq!(crate::smt::current_thread_solve_deadline(), Some(until));
        assert_eq!(crate::smt::deadline::current_smt_deadline(), old_smt);
        assert_eq!(
            crate::smt::SmtContext::current_thread_term_memory_budget(),
            old_memory
        );
    }
}
