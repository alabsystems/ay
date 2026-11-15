// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Control-only tests: no PDR/SMT search and no proof acceptance.

use super::*;

mod ambient;

#[test]
fn explicit_zero_memory_is_terminal_before_optional_probe() {
    let mut base = configured().with_memory_budget(Some(0));
    let original = Instant::now() + Duration::from_secs(60);
    let mut owner = Owner::capture(&base, Some(original));
    assert_eq!(owner.memory().term_limit(), Some(0));
    assert!(!owner.open());
    assert_eq!(owner.probe_deadline(), None);
    base.memory_budget = None;
    assert!(
        !owner.open(),
        "changing configuration cannot renew this owner"
    );
    assert!(Owner::capture(&base, Some(original)).open());
}

#[test]
fn explicit_memory_intersects_ambient_scope_without_raising_it() {
    assert_eq!(
        Owner::capture(&configured(), None).memory().term_limit(),
        None
    );
    for explicit in [None, Some(128), Some(32)] {
        let base = configured().with_memory_budget(explicit);
        let owner = {
            let _ambient = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(64));
            Owner::capture(&base, None)
        };
        let expected = Some(explicit.unwrap_or(64).min(64));
        assert_eq!(owner.memory().term_limit(), expected);
        {
            let _captured = owner.memory().install();
            assert_eq!(
                crate::smt::SmtContext::current_thread_term_memory_budget(),
                expected
            );
        }
        assert_eq!(
            crate::smt::SmtContext::current_thread_term_memory_budget(),
            None
        );
    }
}

#[derive(Clone, Copy, Debug)]
enum Channel {
    Primary,
    External,
}

fn configured() -> PdrConfig {
    PdrConfig {
        strict_proofs: true,
        preserve_original_clauses: true,
        solve_timeout: Some(Duration::from_secs(60)),
        ..PdrConfig::production(false)
    }
}

fn attach(config: &mut PdrConfig, channel: Channel, token: CancellationToken) {
    match channel {
        Channel::Primary => config.cancellation_token = Some(token),
        Channel::External => config.external_cancellation_token = Some(token),
    }
}

fn token(config: &PdrConfig, channel: Channel) -> Option<&CancellationToken> {
    match channel {
        Channel::Primary => config.cancellation_token.as_ref(),
        Channel::External => config.external_cancellation_token.as_ref(),
    }
}

#[test]
fn original_deadline_is_the_minimum_of_all_three_sources() {
    let now = Instant::now();
    for (caller, solve, smt) in [(10, 20, 30), (30, 10, 20), (20, 30, 10)] {
        let caller = now + Duration::from_secs(caller);
        let solve = now + Duration::from_secs(solve);
        let smt = now + Duration::from_secs(smt);
        {
            let _solve = crate::smt::ScopedSolveDeadline::new(Some(solve));
            let _smt = crate::smt::ScopedSmtDeadline::install_until(smt);
            let mut owner = Owner::capture(&configured(), Some(caller));
            assert_eq!(owner.deadline(), Some(now + Duration::from_secs(10)));
            assert!(owner.open_at(now));
            assert_eq!(crate::smt::current_thread_solve_deadline(), Some(solve));
            assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(smt));
        }
        assert_eq!(crate::smt::current_thread_solve_deadline(), None);
        assert_eq!(crate::smt::deadline::current_smt_deadline(), None);
    }
}

#[test]
fn no_absolute_deadline_means_no_optional_probe_or_invented_default() {
    let mut owner = Owner::capture(&configured(), None);
    assert_eq!(owner.deadline(), None);
    assert!(owner.open());
    assert_eq!(owner.probe_deadline(), None);
    assert!(owner.open());
    assert_eq!(owner.probe_deadline(), None);
}

#[test]
fn original_expiry_stays_terminal_after_clock_or_scope_restoration() {
    let now = Instant::now();
    let original = now + Duration::from_secs(30);
    let mut owner = Owner::capture(&configured(), Some(original));
    assert!(owner.open_at(now));
    assert!(!owner.open_at(original));
    assert!(!owner.open_at(now));
    assert_eq!(owner.probe_deadline_at(now), None);
    let mut ambient_owner = {
        let _smt = crate::smt::ScopedSmtDeadline::install_until(now - Duration::from_secs(1));
        Owner::capture(&configured(), Some(original))
    };
    assert!(!ambient_owner.open());
    assert_eq!(ambient_owner.probe_deadline(), None);
}

#[test]
fn shorter_probe_clock_can_expire_without_poisoning_original_owner() {
    let now = Instant::now();
    let original = now + Duration::from_secs(60);
    let _original = crate::smt::ScopedSolveDeadline::new(Some(original));
    let mut owner = Owner::capture(&configured(), Some(original));
    {
        let expired = now - Duration::from_secs(1);
        let _probe = crate::smt::ScopedSolveDeadline::new(Some(expired));
        let _smt = crate::smt::ScopedSmtDeadline::install_until(expired);
        assert!(crate::smt::smt_deadline_expired());
        assert!(
            owner.open(),
            "probe expiry is not the original caller deadline"
        );
    }
    assert_eq!(crate::smt::current_thread_solve_deadline(), Some(original));
    assert_eq!(crate::smt::deadline::current_smt_deadline(), None);
    assert!(owner.open());
}

#[test]
fn probe_uses_only_remaining_quarter_capped_at_four_seconds_without_renewal() {
    let now = Instant::now();
    for (remaining, slice) in [(8, 2), (16, 4), (60, 4)] {
        let original = now + Duration::from_secs(remaining);
        let mut owner = Owner::capture(&configured(), Some(original));
        let expected = now + Duration::from_secs(slice);
        assert_eq!(owner.probe_deadline_at(now), Some(expected));
        assert_eq!(
            owner.probe_deadline_at(now + Duration::from_secs(1)),
            Some(expected),
            "a repeated request does not buy a new slice"
        );
        assert_eq!(owner.probe_deadline_at(expected), Some(expected));
        assert!(owner.open_at(expected), "original fallback time remains");
        assert_eq!(owner.deadline(), Some(original));
    }
    let original = now + Duration::from_secs(20);
    let mut owner = Owner::capture(&configured(), Some(original));
    let after_preparation = now + Duration::from_secs(12);
    assert_eq!(
        owner.probe_deadline_at(after_preparation),
        Some(after_preparation + Duration::from_secs(2)),
        "only time still remaining after preparation can be divided"
    );
}

#[test]
fn search_preserves_channel_presence_and_non_time_configuration() {
    let now = Instant::now();
    let original = now + Duration::from_secs(60);
    for channels in [
        Vec::new(),
        vec![Channel::Primary],
        vec![Channel::External],
        vec![Channel::Primary, Channel::External],
    ] {
        let mut base = configured();
        for channel in channels {
            attach(&mut base, channel, CancellationToken::new());
        }
        let owner = Owner::capture(&base, Some(original));
        let child = owner.search_config(&base, now + Duration::from_secs(4));
        for channel in [Channel::Primary, Channel::External] {
            assert_eq!(
                token(&child, channel).is_some(),
                token(&base, channel).is_some()
            );
        }
        assert!(child.solve_timeout.unwrap() <= Duration::from_secs(4));
        assert!(child.strict_proofs && child.preserve_original_clauses);
        assert_eq!(child.max_frames, base.max_frames);
        assert_eq!(child.max_iterations, base.max_iterations);
        assert_eq!(child.max_obligations, base.max_obligations);
        assert_eq!(
            child.disable_array_scalarization,
            base.disable_array_scalarization
        );
    }
}

#[test]
fn search_timeout_cannot_relax_base_probe_or_original_deadline() {
    let now = Instant::now();
    let original = now + Duration::from_secs(30);
    let base = configured();
    let owner = Owner::capture(&base, Some(original));
    assert!(
        owner
            .search_config(&base, original + Duration::from_secs(60))
            .solve_timeout
            .unwrap()
            <= Duration::from_secs(30)
    );
    let mut tighter = base.clone();
    tighter.solve_timeout = Some(Duration::from_secs(1));
    assert!(
        owner
            .search_config(&tighter, original)
            .solve_timeout
            .unwrap()
            <= Duration::from_secs(1)
    );
    assert_eq!(
        owner
            .search_config(&base, now - Duration::from_secs(1))
            .solve_timeout,
        Some(Duration::ZERO)
    );
    let mut planned = Owner::capture(&base, Some(original));
    assert_eq!(
        planned.probe_deadline_at(now),
        Some(now + Duration::from_secs(4))
    );
    assert!(
        planned
            .search_config(&base, original)
            .solve_timeout
            .unwrap()
            <= Duration::from_secs(4)
    );
}

#[test]
fn observed_search_cancellation_on_either_channel_survives_parent_reset() {
    for channel in [Channel::Primary, Channel::External] {
        let parent = CancellationToken::new();
        let mut base = configured();
        attach(&mut base, channel, parent.clone());
        let original = Instant::now() + Duration::from_secs(60);
        let mut owner = Owner::capture(&base, Some(original));
        let search = owner.search_config(&base, original);
        parent.cancel();
        assert!(token(&search, channel).unwrap().is_cancelled());
        parent.reset();
        assert!(!parent.is_cancelled());
        assert!(!owner.open());
        assert_eq!(owner.probe_deadline(), None);
        assert!(Owner::capture(&base, Some(original)).open());
    }
}

#[test]
fn validation_primary_observes_both_channels_without_writing_upstream() {
    for observed in [Channel::Primary, Channel::External] {
        let mut base = configured();
        attach(&mut base, Channel::Primary, CancellationToken::new());
        attach(&mut base, Channel::External, CancellationToken::new());
        let original = Instant::now() + Duration::from_secs(60);
        let mut owner = Owner::capture(&base, Some(original));
        let validation = owner.validation_config(&base);
        token(&base, observed).unwrap().cancel();
        assert!(validation
            .cancellation_token
            .as_ref()
            .unwrap()
            .is_cancelled());
        token(&base, observed).unwrap().reset();
        assert!(!token(&base, observed).unwrap().is_cancelled());
        assert!(
            !owner.open(),
            "the validator's observation belongs to this attempt"
        );
    }
    let mut external_only = configured();
    external_only.external_cancellation_token = Some(CancellationToken::new());
    let owner = Owner::capture(&external_only, None);
    let validation = owner.validation_config(&external_only);
    assert!(validation.cancellation_token.is_some());
    external_only
        .external_cancellation_token
        .as_ref()
        .unwrap()
        .cancel();
    assert!(validation
        .cancellation_token
        .as_ref()
        .unwrap()
        .is_cancelled());
}

#[test]
fn local_search_cancellation_does_not_poison_caller_or_other_attempts() {
    for channel in [Channel::Primary, Channel::External] {
        let mut base = configured();
        let parent = CancellationToken::new();
        attach(&mut base, channel, parent.clone());
        let original = Instant::now() + Duration::from_secs(60);
        let mut owner = Owner::capture(&base, Some(original));
        let search = owner.search_config(&base, original);
        token(&search, channel).unwrap().cancel();
        assert!(token(&search, channel).unwrap().is_cancelled());
        assert!(!parent.is_cancelled());
        assert!(owner.open());
        let fresh_search = owner.search_config(&base, original);
        assert!(!token(&fresh_search, channel).unwrap().is_cancelled());
    }
}

#[test]
fn zero_memory_is_sticky_and_captured_memory_install_never_raises_a_limit() {
    let mut captured_zero = {
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        Owner::capture(&configured(), None)
    };
    assert!(!captured_zero.open());
    let mut live = Owner::capture(&configured(), None);
    assert!(live.open());
    {
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(!live.open());
    }
    assert!(!live.open());
    let captured = {
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(128));
        Owner::capture(&configured(), None)
    };
    {
        let _current = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(64));
        let _captured = captured.memory().install();
        assert_eq!(
            crate::smt::SmtContext::current_thread_term_memory_budget(),
            Some(64)
        );
    }
    {
        let _captured = captured.memory().install();
        assert_eq!(
            crate::smt::SmtContext::current_thread_term_memory_budget(),
            Some(128)
        );
    }
    assert_eq!(
        crate::smt::SmtContext::current_thread_term_memory_budget(),
        None
    );
}

#[test]
fn ambient_lane_cancellation_is_terminal_after_binding_and_token_restore() {
    let parent = CancellationToken::new();
    let mut owner = Owner::capture(&configured(), None);
    {
        let _lane = crate::smt::deadline::ScopedLaneCancellation::install(parent.clone(), None);
        assert!(owner.open());
        parent.cancel();
        assert!(!owner.open());
        parent.reset();
    }
    assert!(!crate::smt::deadline::lane_cancelled());
    assert!(!owner.open());
}
