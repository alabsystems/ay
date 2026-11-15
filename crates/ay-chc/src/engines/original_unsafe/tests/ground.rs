// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual producer and unchanged original validator, not injected acceptance.

use super::*;
use crate::ground_derivation::forward::fixtures::{problem, Site};

#[test]
fn original_complete_array_candidate_passes_the_actual_strict_validator() {
    for site in [Site::Body, Site::Exit] {
        let original = problem(site, 9, 10);
        let before = format!("{original:?}");
        let until = Instant::now() + Duration::from_secs(20);
        let result = run(&original, &configured(), Some(until))
            .expect("existing original lane must confirm complete ground candidate");
        let confirmed = result
            .unsafe_counterexample()
            .expect("actual strict Unsafe");
        assert!(confirmed.counterexample().has_ground_derivation());
        assert!(matches!(
            confirmed.counterexample().ground_checks_unsafe(&original),
            Ok(true)
        ));
        assert_eq!(format!("{original:?}"), before);
        assert!(Instant::now() < until);
    }
}

#[test]
fn original_stop_between_actual_candidate_and_validation_is_terminal() {
    let original = problem(Site::Exit, 9, 10);
    let token = CancellationToken::new();
    let mut config = configured();
    config.cancellation_token = Some(token.clone());
    let result = run_owned(
        &original,
        &config,
        Some(deadline()),
        &mut |input, _, configured, owner, probe| {
            let candidate = search::original(input, configured, owner, probe);
            assert!(candidate
                .as_ref()
                .is_some_and(Counterexample::has_ground_derivation));
            token.cancel();
            assert!(!owner.open());
            token.reset();
            candidate
        },
        &mut |_, _, _| panic!("stopped owner must not reach original validator"),
        &mut |_| {},
    )
    .expect("original refusal is terminal Unknown");
    assert!(matches!(result, VerifiedChcResult::Unknown(_)));
}

#[test]
fn spent_probe_cannot_renew_search_or_poison_original_fallback() {
    let original = problem(Site::Exit, 9, 10);
    let config = configured();
    let until = deadline();
    let mut owner = Owner::capture(&config, Some(until));
    assert!(search::original(&original, &config, &mut owner, Instant::now()).is_none());
    assert!(owner.open(), "only local speculative clock expired");
    assert_eq!(owner.deadline(), Some(until));
}

#[test]
fn expired_original_owner_stays_stopped_after_the_scope_disappears() {
    let original = problem(Site::Exit, 9, 10);
    let config = configured();
    let mut owner = {
        let _scope = crate::smt::ScopedSolveDeadline::new(Some(Instant::now()));
        Owner::capture(&config, Some(deadline()))
    };
    assert!(search::original(&original, &config, &mut owner, deadline()).is_none());
    assert!(
        !owner.open(),
        "captured original absolute deadline cannot be replaced"
    );
}

#[test]
fn zero_original_memory_refusal_survives_cleanup() {
    let original = problem(Site::Exit, 9, 10);
    let config = configured();
    let mut owner = Owner::capture(&config, Some(deadline()));
    {
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(search::original(&original, &config, &mut owner, deadline()).is_none());
    }
    assert!(!owner.open());
}
