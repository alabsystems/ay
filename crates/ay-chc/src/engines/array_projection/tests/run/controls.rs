// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_phase_refuses_both_caller_channels_even_after_observed_parent_reset() {
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
                &mut |reduced, _| PdrResult::Safe(model(reduced)),
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
            .expect("an observed original stop must not permit fallback");
            assert!(result.is_unknown(), "external={external}, stop={stop:?}");
            assert!(observed.contains(&stop));
            assert_eq!(observed.last(), Some(&Phase::Cleanup));
            let stop_position = phases().iter().position(|phase| *phase == stop).unwrap();
            for later in &phases()[stop_position + 1..] {
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
fn search_descendant_observation_is_sticky_but_its_local_cancel_is_not_caller_stop() {
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
            let result = run_observed(
                &original,
                &config,
                Some(deadline()),
                &mut |_, search| {
                    let child = if external {
                        search.external_cancellation_token.as_ref()
                    } else {
                        search.cancellation_token.as_ref()
                    }
                    .unwrap();
                    if caller_cancel {
                        parent.cancel();
                    } else {
                        child.cancel();
                    }
                    assert!(child.is_cancelled());
                    parent.reset();
                    PdrResult::Unknown
                },
                &mut |_, _, _| panic!("Unknown must not validate"),
                &mut |_| {},
            );
            assert!(!parent.is_cancelled());
            if caller_cancel {
                assert!(result.unwrap().is_unknown());
            } else {
                assert!(result.is_none(), "lane-local cancellation permits fallback");
            }
        }
    }
}

#[test]
fn cleanup_stop_dominates_inapplicability_or_non_safe_search_refusal() {
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
            &mut |_, _| {
                searched += 1;
                PdrResult::Unknown
            },
            &mut |_, _, _| panic!("no candidate to validate"),
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
fn expired_original_clock_precancellation_and_zero_memory_refuse_before_search() {
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
            &mut |_, _| panic!("closed caller must not search"),
            &mut |_, _, _| panic!("closed caller must not validate"),
            &mut |phase| observed.push(phase),
        )
        .unwrap();
        assert!(result.is_unknown());
        assert_eq!(observed, [Phase::Cleanup]);
    }
}

#[test]
fn search_short_clock_and_memory_scope_restore_before_original_validation_and_return() {
    let original = source();
    let now = Instant::now();
    let supplied = now + Duration::from_secs(80);
    let solve = now + Duration::from_secs(70);
    let smt = now + Duration::from_secs(60);
    {
        let _solve = crate::smt::ScopedSolveDeadline::new(Some(solve));
        let _smt = crate::smt::ScopedSmtDeadline::install_until(smt);
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(4096));
        let result = run_observed(
            &original,
            &configured(),
            Some(supplied),
            &mut |reduced, config| {
                let short = crate::smt::current_thread_solve_deadline().unwrap();
                assert!(short < smt);
                assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(short));
                assert!(config.solve_timeout.unwrap() <= Duration::from_secs(4));
                assert_eq!(
                    crate::smt::SmtContext::current_thread_term_memory_budget(),
                    Some(4096)
                );
                PdrResult::Safe(model(reduced))
            },
            &mut |lifted, _, clock| {
                assert_eq!(clock, Some(smt));
                assert_eq!(crate::smt::current_thread_solve_deadline(), Some(smt));
                assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(smt));
                fake_safe(lifted)
            },
            &mut |_| {},
        )
        .unwrap();
        assert!(result.is_safe());
        assert_eq!(crate::smt::current_thread_solve_deadline(), Some(solve));
        assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(smt));
        assert_eq!(
            crate::smt::SmtContext::current_thread_term_memory_budget(),
            Some(4096)
        );
    }
    assert_eq!(crate::smt::current_thread_solve_deadline(), None);
    assert_eq!(crate::smt::deadline::current_smt_deadline(), None);
    assert_eq!(
        crate::smt::SmtContext::current_thread_term_memory_budget(),
        None
    );
}

#[test]
fn injected_search_panic_unwinds_scopes_without_mutating_original_problem() {
    let original = source();
    let before = format!("{original:?}");
    let until = deadline();
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(until));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_observed(
            &original,
            &configured(),
            Some(until),
            &mut |_, _| panic!("injected search panic"),
            &mut |_, _, _| panic!("never validates"),
            &mut |_| {},
        )
    }));
    assert!(result.is_err());
    assert_eq!(format!("{original:?}"), before);
    assert_eq!(crate::smt::current_thread_solve_deadline(), Some(until));
    assert_eq!(crate::smt::deadline::current_smt_deadline(), None);
}
