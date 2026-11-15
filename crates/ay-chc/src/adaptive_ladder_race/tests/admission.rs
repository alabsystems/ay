// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

#[path = "admission/cancellation_reset.rs"]
mod cancellation_reset;

#[test]
fn empty_members_accept_a_healthy_foreground() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let (result, _) = portfolio.race_ladder("empty", Vec::new(), safe);
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn empty_members_refuse_a_cancelled_caller_candidate() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let ran = AtomicBool::new(false);
    let (result, _) = portfolio.race_ladder("empty", Vec::new(), || {
        ran.store(true, Ordering::Relaxed);
        portfolio.cancellation_token.cancel();
        safe()
    });
    assert!(
        ran.load(Ordering::Relaxed),
        "cancellation occurs in the callback"
    );
    assert!(matches!(result, PortfolioResult::Unknown));
}

#[test]
fn empty_members_refuse_outer_lane_cancellation_with_live_caller() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let outer = CancellationToken::new();
    let _lane = crate::smt::ScopedLaneCancellation::install(outer.clone(), None);
    let ran = AtomicBool::new(false);
    let (result, _) = portfolio.race_ladder("empty", Vec::new(), || {
        ran.store(true, Ordering::Relaxed);
        outer.cancel();
        safe()
    });
    assert!(ran.load(Ordering::Relaxed));
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn empty_members_refuse_the_original_solve_deadline() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(Instant::now()));
    let ran = AtomicBool::new(false);
    let (result, _) = portfolio.race_ladder("empty", Vec::new(), || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(!ran.load(Ordering::Relaxed));
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn empty_members_refuse_the_original_smt_deadline() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let _smt = crate::smt::ScopedSmtDeadline::install_until(Instant::now());
    let ran = AtomicBool::new(false);
    let (result, _) = portfolio.race_ladder("empty", Vec::new(), || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(!ran.load(Ordering::Relaxed));
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn serial_cancellation_preserves_member_order_and_refuses_foreground() {
    let portfolio = portfolio(
        AdaptiveConfig::test_default()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let outer = CancellationToken::new();
    let _lane = crate::smt::ScopedLaneCancellation::install(outer.clone(), None);
    let order = Mutex::new(Vec::new());
    let caller_thread = std::thread::current().id();
    let members = vec![
        LadderMember::new("first", || {
            assert_eq!(std::thread::current().id(), caller_thread);
            order.lock().expect("order").push("first");
            outer.cancel();
            Some(safe())
        }),
        LadderMember::new("second", || {
            order.lock().expect("order").push("second");
            Some(safe())
        }),
    ];
    let (result, _) = portfolio.race_ladder("serial", members, || {
        order.lock().expect("order").push("foreground");
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*order.lock().expect("order"), ["first"]);
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn serial_original_deadline_refuses_member_and_foreground_candidates() {
    let portfolio = portfolio(
        AdaptiveConfig::test_default()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(Instant::now()));
    let order = Mutex::new(Vec::new());
    let members = vec![LadderMember::new("late", || {
        order.lock().expect("order").push("member");
        Some(safe())
    })];
    let (result, _) = portfolio.race_ladder("serial", members, || {
        order.lock().expect("order").push("foreground");
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(order.lock().expect("order").is_empty());
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn serial_healthy_member_retains_its_first_winner_order() {
    let portfolio = portfolio(
        AdaptiveConfig::test_default()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let order = Mutex::new(Vec::new());
    let members = vec![LadderMember::new("first", || {
        order.lock().expect("order").push("first");
        Some(safe())
    })];
    let (result, _) = portfolio.race_ladder("serial", members, || {
        order.lock().expect("order").push("foreground");
        unknown()
    });
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert_eq!(*order.lock().expect("order"), ["first"]);
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn captured_memory_trip_remains_authoritative_after_scope_drop_and_replacement() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let flag = Arc::new(AtomicBool::new(false));
    let original = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, flag);
    let scope = ay_sys::enter_memory_group(original);
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    ay_sys::charge_current_for_testing(2 * 1024 * 1024);
    drop(scope);
    let replacement =
        ay_sys::MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _replacement = ay_sys::enter_memory_group(replacement);
    assert!(!ay_sys::current_memory_group_soft_tripped());
    let ran = AtomicBool::new(false);
    let member = Mutex::new(Some(LadderMember::new("late", || {
        ran.store(true, Ordering::Relaxed);
        Some(safe())
    })));
    portfolio.run_ladder_member(&state, &member, &state.tokens[0]);
    let foreground = portfolio.run_ladder_foreground(&state, || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(!ran.load(Ordering::Relaxed));
    assert!(matches!(foreground, Some((PortfolioResult::Unknown, _))));
    assert!(matches!(
        state.offer("late", &state.tokens[0], safe()),
        Err((PortfolioResult::Unknown, _))
    ));
    assert!(!state.decided());
    assert!(!state.foreground_token().is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn current_memory_trip_refuses_a_foreground_without_a_captured_group() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _group = ay_sys::enter_memory_group(group);
    let ran = AtomicBool::new(false);
    let foreground = portfolio.run_ladder_foreground(&state, || {
        ran.store(true, Ordering::Relaxed);
        ay_sys::charge_current_for_testing(2 * 1024 * 1024);
        safe()
    });
    assert!(ran.load(Ordering::Relaxed));
    assert!(!state.decided());
    let (result, _) = portfolio.conclude_ladder_race("memory", Instant::now(), &state, foreground);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn empty_members_refuse_a_sticky_memory_trip_with_live_caller() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _group = ay_sys::enter_memory_group(group);
    let ran = AtomicBool::new(false);
    let (result, _) = portfolio.race_ladder("empty", Vec::new(), || {
        ran.store(true, Ordering::Relaxed);
        ay_sys::charge_current_for_testing(2 * 1024 * 1024);
        safe()
    });
    assert!(ran.load(Ordering::Relaxed));
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn serial_members_refuse_a_sticky_memory_trip_with_live_caller() {
    let portfolio = portfolio(
        AdaptiveConfig::test_default()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _group = ay_sys::enter_memory_group(group);
    let order = Mutex::new(Vec::new());
    let members = vec![LadderMember::new("memory", || {
        order.lock().expect("order").push("member");
        ay_sys::charge_current_for_testing(2 * 1024 * 1024);
        Some(safe())
    })];
    let (result, _) = portfolio.race_ladder("serial", members, || {
        order.lock().expect("order").push("foreground");
        safe()
    });
    assert_eq!(*order.lock().expect("order"), ["member"]);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn winning_race_cancellation_does_not_refuse_the_healthy_cached_winner() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(state.offer("winner", &state.tokens[0], safe()).is_ok());
    assert!(state.tokens.iter().all(CancellationToken::is_cancelled));
    let (result, _) = portfolio.conclude_ladder_race("winner", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn memory_trip_after_admission_refuses_the_cached_winner() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _group = ay_sys::enter_memory_group(group);
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(state.offer("winner", &state.tokens[0], safe()).is_ok());
    ay_sys::charge_current_for_testing(2 * 1024 * 1024);
    let (result, _) = portfolio.conclude_ladder_race("memory", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn caller_cancellation_during_scoped_joins_refuses_the_cached_winner() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let started = AtomicBool::new(false);
    let members = vec![LadderMember::new("loser", || {
        started.store(true, Ordering::Release);
        assert!(wait_for_lane_cancellation());
        portfolio.cancellation_token.cancel();
        None
    })];
    let (result, _) = portfolio.race_ladder("join", members, || {
        let waiting = Instant::now();
        while !started.load(Ordering::Acquire) && waiting.elapsed() < SAFETY {
            std::thread::yield_now();
        }
        assert!(started.load(Ordering::Acquire));
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
}

#[test]
fn original_deadline_expiry_during_cleanup_refuses_the_cached_winner() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let deadline = Instant::now() + Duration::from_secs(1);
    let state = RaceState::new(&portfolio.cancellation_token, 1, Some(deadline));
    assert!(state.offer("winner", &state.tokens[0], safe()).is_ok());
    // A bounded cleanup interval consumes the same absolute caller clock.
    std::thread::sleep(deadline.saturating_duration_since(Instant::now()));
    let (result, _) = portfolio.conclude_ladder_race("expiry", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[path = "admission/owners.rs"]
mod owners;
use owners::{with_closed_owner, CLOSED_OWNERS};

#[test]
fn empty_preclosed_owners_skip_the_foreground_callback() {
    for owner in CLOSED_OWNERS {
        let portfolio = portfolio(AdaptiveConfig::test_default());
        let ran = AtomicBool::new(false);
        with_closed_owner(&portfolio, owner, || {
            let (result, _) = portfolio.race_ladder("preclosed", Vec::new(), || {
                ran.store(true, Ordering::Relaxed);
                safe()
            });
            assert!(matches!(result, PortfolioResult::Unknown));
        });
        assert!(!ran.load(Ordering::Relaxed));
    }
}

#[test]
fn serial_preclosed_owners_skip_all_callbacks() {
    for owner in CLOSED_OWNERS {
        let portfolio = portfolio(
            AdaptiveConfig::test_default()
                .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
        );
        let order = Mutex::new(Vec::new());
        with_closed_owner(&portfolio, owner, || {
            let members = vec![LadderMember::new("member", || {
                order.lock().expect("order").push("member");
                Some(safe())
            })];
            let (result, _) = portfolio.race_ladder("preclosed", members, || {
                order.lock().expect("order").push("foreground");
                safe()
            });
            assert!(matches!(result, PortfolioResult::Unknown));
        });
        assert!(order.lock().expect("order").is_empty());
    }
}

#[test]
fn concurrent_preclosed_owners_skip_member_and_foreground_callbacks() {
    for owner in CLOSED_OWNERS {
        let portfolio = portfolio(AdaptiveConfig::test_default());
        let ran = AtomicBool::new(false);
        with_closed_owner(&portfolio, owner, || {
            let state = RaceState::new(&portfolio.cancellation_token, 1, None);
            let member = Mutex::new(Some(LadderMember::new("member", || {
                ran.store(true, Ordering::Relaxed);
                Some(safe())
            })));
            portfolio.run_ladder_member(&state, &member, &state.tokens[0]);
            let foreground = portfolio.run_ladder_foreground(&state, || {
                ran.store(true, Ordering::Relaxed);
                safe()
            });
            assert!(!state.decided());
            let (result, _) =
                portfolio.conclude_ladder_race("preclosed", Instant::now(), &state, foreground);
            assert!(matches!(result, PortfolioResult::Unknown));
            let members = vec![LadderMember::new("member", || {
                ran.store(true, Ordering::Relaxed);
                Some(safe())
            })];
            let (result, _) = portfolio.race_ladder("preclosed", members, || {
                ran.store(true, Ordering::Relaxed);
                safe()
            });
            assert!(matches!(result, PortfolioResult::Unknown));
        });
        assert!(!ran.load(Ordering::Relaxed));
    }
}

#[test]
fn preclosed_participant_flags_skip_callbacks_without_cancelling_the_caller() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    let ran = AtomicBool::new(false);
    state.tokens[0].cancel();
    state.foreground_token().cancel();
    let member = Mutex::new(Some(LadderMember::new("member", || {
        ran.store(true, Ordering::Relaxed);
        Some(safe())
    })));
    portfolio.run_ladder_member(&state, &member, &state.tokens[0]);
    let foreground = portfolio.run_ladder_foreground(&state, || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    let members = vec![LadderMember::new("serial", || {
        ran.store(true, Ordering::Relaxed);
        Some(safe())
    })];
    let (result, _) = super::super::admission::run_serial(&state, members, || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!ran.load(Ordering::Relaxed));
    assert!(!state.decided());
    let (result, _) =
        portfolio.conclude_ladder_race("preclosed", Instant::now(), &state, foreground);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn serial_deadline_expiry_during_member_skips_later_callbacks() {
    let portfolio = portfolio(
        AdaptiveConfig::test_default()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let deadline = Instant::now() + Duration::from_secs(1);
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(deadline));
    let order = Mutex::new(Vec::new());
    let members = vec![LadderMember::new("member", || {
        order.lock().expect("order").push("member");
        std::thread::sleep(deadline.saturating_duration_since(Instant::now()));
        Some(safe())
    })];
    let (result, _) = portfolio.race_ladder("expiry", members, || {
        order.lock().expect("order").push("foreground");
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*order.lock().expect("order"), ["member"]);
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn serial_foreground_cancellation_refuses_a_candidate_after_healthy_member_work() {
    let portfolio = portfolio(
        AdaptiveConfig::test_default()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let order = Mutex::new(Vec::new());
    let members = vec![LadderMember::new("member", || {
        order.lock().expect("order").push("member");
        Some(unknown())
    })];
    let (result, _) = portfolio.race_ladder("cancel", members, || {
        order.lock().expect("order").push("foreground");
        portfolio.cancellation_token.cancel();
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*order.lock().expect("order"), ["member", "foreground"]);
}
