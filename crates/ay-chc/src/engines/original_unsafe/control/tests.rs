// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pure resource/control tests; no search or proof acceptance.

use super::*;

mod ambient;

#[test]
fn explicit_zero_memory_is_terminal_before_optional_probe() {
    let mut base = config().with_memory_budget(Some(0));
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
    assert_eq!(Owner::capture(&config(), None).memory().term_limit(), None);
    for explicit in [None, Some(128), Some(32)] {
        let base = config().with_memory_budget(explicit);
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

fn config() -> PdrConfig {
    PdrConfig::production(false)
}

#[test]
fn capture_intersects_all_absolute_clocks_without_changing_bindings() {
    let now = Instant::now();
    for (caller, solve, smt) in [(10, 20, 30), (30, 10, 20), (20, 30, 10)] {
        let caller = now + Duration::from_secs(caller);
        let solve = now + Duration::from_secs(solve);
        let smt = now + Duration::from_secs(smt);
        {
            let _solve = crate::smt::ScopedSolveDeadline::new(Some(solve));
            let _smt = crate::smt::ScopedSmtDeadline::install_until(smt);
            let mut owner = Owner::capture(&config(), Some(caller));
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
fn missing_or_expired_original_clock_never_creates_a_probe() {
    let now = Instant::now();
    let mut absent = Owner::capture(&config(), None);
    assert!(absent.open_at(now));
    assert_eq!(absent.probe_deadline_at(now), None);
    let mut expired = Owner::capture(&config(), Some(now));
    assert_eq!(expired.probe_deadline_at(now), None);
    assert!(!expired.open_at(
        now.checked_sub(Duration::from_secs(1))
            .expect("fixture instant supports a one-second offset")
    ));
}

#[test]
fn quarter_capped_probe_is_cached_and_preserves_original_fallback_time() {
    let now = Instant::now();
    for (remaining, slice) in [(8, 2), (16, 4), (60, 4)] {
        let original = now + Duration::from_secs(remaining);
        let mut owner = Owner::capture(&config(), Some(original));
        let expected = now + Duration::from_secs(slice);
        assert_eq!(owner.probe_deadline_at(now), Some(expected));
        assert_eq!(owner.probe_deadline_at(expected), Some(expected));
        assert!(owner.open_at(expected));
        assert_eq!(owner.deadline(), Some(original));
    }
    let mut owner = Owner::capture(&config(), Some(now + Duration::from_secs(20)));
    assert_eq!(
        owner.probe_deadline_at(now + Duration::from_secs(12)),
        Some(now + Duration::from_secs(14)),
        "preparation time is not refunded"
    );
}

#[test]
fn expired_local_scopes_do_not_poison_original_owner() {
    let now = Instant::now();
    let original = now + Duration::from_secs(60);
    let mut owner = Owner::capture(&config(), Some(original));
    {
        let _solve = crate::smt::ScopedSolveDeadline::new(Some(now));
        let _smt = crate::smt::ScopedSmtDeadline::install_until(now);
        assert!(crate::smt::smt_deadline_expired());
        assert!(owner.open_at(now));
    }
    assert!(owner.open());
    assert_eq!(owner.deadline(), Some(original));
}

#[test]
fn either_parent_observation_remains_sticky_but_child_cancel_is_local() {
    let primary = CancellationToken::new();
    let external = CancellationToken::new();
    let config = PdrConfig {
        cancellation_token: Some(primary.clone()),
        external_cancellation_token: Some(external.clone()),
        ..config()
    };
    for parent in [&primary, &external] {
        let mut owner = Owner::capture(&config, None);
        let child = owner.configured(&config);
        let child = child.cancellation_token.unwrap();
        parent.cancel();
        assert!(child.is_cancelled());
        parent.reset();
        assert!(!owner.open());
        assert!(!primary.is_cancelled() && !external.is_cancelled());
    }
    let mut owner = Owner::capture(&config, None);
    owner
        .configured(&config)
        .cancellation_token
        .unwrap()
        .cancel();
    assert!(owner.open());
    assert!(!primary.is_cancelled() && !external.is_cancelled());
}

#[test]
fn zero_memory_observation_survives_temporary_scope_cleanup() {
    let mut owner = Owner::capture(&config(), None);
    {
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(!owner.open());
    }
    assert!(!owner.open());
    assert!(Owner::capture(&config(), None).open());
}
