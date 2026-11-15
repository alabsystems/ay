// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::engines::ambient_cancellation::support::{stop_reset_and_replace, Observer};
use crate::smt::deadline::ScopedLaneCancellation;

#[test]
fn original_owner_retains_descendant_observation_under_healthy_replacement() {
    for (primary, external, observer) in [
        (false, false, Observer::Lane),
        (true, false, Observer::Primary),
        (false, true, Observer::Primary),
        (false, true, Observer::External),
    ] {
        let parent = CancellationToken::new();
        let _outer = ScopedLaneCancellation::install(parent.clone(), None);
        let base = PdrConfig {
            cancellation_token: primary.then(CancellationToken::new),
            external_cancellation_token: external.then(CancellationToken::new),
            ..config()
        };
        let until = Instant::now() + Duration::from_secs(60);
        let mut owner = Owner::capture(&base, Some(until));
        let _attempt = owner.install_lane();
        let configured = owner.configured(&base);
        // The old external-only validator promotion remains, but ambient
        // presence alone must never create a primary search channel.
        assert_eq!(configured.cancellation_token.is_some(), primary || external);
        assert_eq!(configured.external_cancellation_token.is_some(), external);
        stop_reset_and_replace(&parent, &configured, observer);
        {
            let _replacement = ScopedLaneCancellation::install(CancellationToken::new(), None);
            assert!(!crate::smt::deadline::lane_cancelled());
            assert!(
                !owner.open(),
                "retained original stop, not replacement status"
            );
        }
        assert!(!parent.is_cancelled());
        drop(_attempt);
        assert!(Owner::capture(&base, Some(until)).open());
    }
}

#[test]
fn original_owner_observes_new_current_lane_stop_without_poisoning_original_parent() {
    let parent = CancellationToken::new();
    let _outer = ScopedLaneCancellation::install(parent.clone(), None);
    let base = config();
    let mut owner = Owner::capture(&base, None);
    let _attempt = owner.install_lane();
    {
        let replacement = CancellationToken::new();
        let _replacement = ScopedLaneCancellation::install(replacement.clone(), None);
        replacement.cancel();
        assert!(!owner.open());
        replacement.reset();
        assert!(!owner.open());
    }
    assert!(!parent.is_cancelled());
    drop(_attempt);
    assert!(Owner::capture(&base, None).open());
}
