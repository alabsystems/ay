// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Resetting a caller starts fresh attempts, never revives an observed stop.

use super::*;
use crate::adaptive_ladder_race::witness::Offer;

#[test]
fn observed_caller_stop_refuses_late_decision_after_parent_reset() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 2, None);
    let observer = state.tokens[0].child();
    portfolio.cancellation_token.cancel();
    assert!(observer.is_cancelled());
    portfolio.cancellation_token.reset();
    assert!(!portfolio.cancellation_token.is_cancelled());
    assert!(!state.caller.open());
    assert!(matches!(
        state.submit("late", &state.tokens[1], Offer::Decide(safe())),
        Some((PortfolioResult::Unknown, _))
    ));
    assert!(!state.decided());

    let fresh = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(fresh.offer("fresh", &fresh.tokens[0], safe()).is_ok());
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn observed_outer_stop_refuses_held_outcome_after_outer_reset() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let outer = CancellationToken::new();
    let _lane = crate::smt::ScopedLaneCancellation::install(outer.clone(), None);
    let state = RaceState::new(&portfolio.cancellation_token, 2, None);
    let observer = state.tokens[0].child();
    outer.cancel();
    assert!(observer.is_cancelled());
    outer.reset();
    assert!(!outer.is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    assert!(!state.caller.open());
    // An already-classified Hold exercises admission, not witness derivation.
    let held = (
        PortfolioResult::Unsafe(crate::pdr::Counterexample::new(Vec::new())),
        ValidationEvidence::CounterexampleVerification,
    );
    assert!(matches!(
        state.submit("late", &state.tokens[1], Offer::Hold(held)),
        Some((PortfolioResult::Unknown, _))
    ));
    assert!(!state.decided());
    assert!(state.held.publish("closed").is_none());

    let fresh = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(fresh.offer("fresh", &fresh.tokens[0], safe()).is_ok());
    assert!(!outer.is_cancelled());
}

#[test]
fn participant_local_stop_does_not_poison_owner_or_siblings() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 2, None);
    let observer = state.tokens[0].child();
    state.tokens[0].cancel();
    assert!(observer.is_cancelled());
    assert!(state.caller.open());
    assert!(!state.tokens[1].is_cancelled());
    assert!(state.offer("healthy", &state.tokens[1], safe()).is_ok());
    let (result, _) = portfolio.conclude_ladder_race("healthy", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn observed_caller_stop_after_admission_refuses_cached_winner_after_reset() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(state.offer("winner", &state.tokens[0], safe()).is_ok());
    portfolio.cancellation_token.cancel();
    assert!(!state.caller.open());
    portfolio.cancellation_token.reset();
    assert!(!portfolio.cancellation_token.is_cancelled());
    let (result, _) = portfolio.conclude_ladder_race("closed", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Unknown));
}

#[test]
fn observed_outer_stop_after_admission_refuses_cached_winner_after_reset() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let outer = CancellationToken::new();
    let _lane = crate::smt::ScopedLaneCancellation::install(outer.clone(), None);
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(state.offer("winner", &state.tokens[0], safe()).is_ok());
    outer.cancel();
    assert!(!state.caller.open());
    outer.reset();
    assert!(!outer.is_cancelled());
    let (result, _) = portfolio.conclude_ladder_race("closed", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn observed_stop_in_serial_member_skips_later_callbacks_after_reset() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 2, None);
    let observer = state.tokens[0].child();
    let later = AtomicBool::new(false);
    let foreground = AtomicBool::new(false);
    let members = vec![
        LadderMember::new("first", || {
            portfolio.cancellation_token.cancel();
            assert!(observer.is_cancelled());
            portfolio.cancellation_token.reset();
            Some(unknown())
        }),
        LadderMember::new("later", || {
            later.store(true, Ordering::Relaxed);
            Some(safe())
        }),
    ];
    let (result, _) = crate::adaptive_ladder_race::admission::run_serial(&state, members, || {
        foreground.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!later.load(Ordering::Relaxed));
    assert!(!foreground.load(Ordering::Relaxed));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn observed_stop_in_empty_foreground_refuses_candidate_after_reset() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 0, None);
    let observer = state.foreground_token().child();
    let (result, _) =
        crate::adaptive_ladder_race::admission::run_serial(&state, Vec::new(), || {
            portfolio.cancellation_token.cancel();
            assert!(observer.is_cancelled());
            portfolio.cancellation_token.reset();
            safe()
        });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[test]
fn independent_original_interrupt_skips_preclosed_callback_without_poisoning_parent() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let outer = CancellationToken::new();
    let interrupt = Arc::new(AtomicBool::new(true));
    let _lane = crate::smt::ScopedLaneCancellation::install(outer.clone(), Some(interrupt.clone()));
    let ran = AtomicBool::new(false);
    let (result, _) = portfolio.race_ladder("raw-preclosed", Vec::new(), || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!ran.load(Ordering::Relaxed));
    assert!(interrupt.load(Ordering::Relaxed));
    assert!(!outer.is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    interrupt.store(false, Ordering::Relaxed);
    let (result, _) = portfolio.race_ladder("fresh", Vec::new(), safe);
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(!interrupt.load(Ordering::Relaxed));
    assert!(!outer.is_cancelled());
}

#[test]
fn observed_independent_original_interrupt_refuses_cached_winner_after_raw_reset() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let outer = CancellationToken::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    let _lane = crate::smt::ScopedLaneCancellation::install(outer.clone(), Some(interrupt.clone()));
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(state.offer("winner", &state.tokens[0], safe()).is_ok());
    interrupt.store(true, Ordering::Relaxed);
    assert!(!state.caller.open());
    interrupt.store(false, Ordering::Relaxed);
    assert!(!outer.is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    assert!(!state.caller.open());
    let (result, _) = portfolio.conclude_ladder_race("raw-reset", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!interrupt.load(Ordering::Relaxed));
    let fresh = RaceState::new(&portfolio.cancellation_token, 1, None);
    assert!(fresh.offer("fresh", &fresh.tokens[0], safe()).is_ok());
    let (result, _) = portfolio.conclude_ladder_race("healthy", Instant::now(), &fresh, None);
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(!outer.is_cancelled());
    assert!(!interrupt.load(Ordering::Relaxed));
}
