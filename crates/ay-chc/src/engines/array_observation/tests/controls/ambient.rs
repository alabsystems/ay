// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Simulated search and validation, not original-clause proof evidence.

use super::super::super::{run_observed, Phase};
use super::super::run::{configured, deadline, fake_safe};
use super::*;
use crate::engines::ambient_cancellation::support::{
    local_child_stop, stop_reset_and_replace, Observer,
};
use crate::smt::deadline::ScopedLaneCancellation;
use crate::{CancellationToken, PdrResult};

#[test]
fn observation_search_descendant_stop_survives_parent_reset_and_lane_replacement() {
    for primary in [false, true] {
        let original = source(9, false);
        let parent = CancellationToken::new();
        let _outer = ScopedLaneCancellation::install(parent.clone(), None);
        let mut base = configured();
        base.cancellation_token = primary.then(CancellationToken::new);
        let mut searched = false;
        let mut validated = false;
        let result = run_observed(
            &original,
            &base,
            Some(deadline()),
            &mut |reduced, configured| {
                searched = true;
                assert_eq!(configured.cancellation_token.is_some(), primary);
                stop_reset_and_replace(&parent, &configured, Observer::Lane);
                PdrResult::Safe(candidate(reduced))
            },
            &mut |lifted, _, _| {
                validated = true;
                fake_safe(lifted)
            },
            &mut |_: Phase| {},
        );
        assert!(searched && !validated);
        assert!(result.unwrap().is_unknown());
        assert!(!parent.is_cancelled());
        assert!(!crate::smt::deadline::lane_cancelled());
    }
}

#[test]
fn observation_validation_descendant_stop_refuses_late_candidate_after_reset() {
    for primary in [false, true] {
        let original = source(9, false);
        let parent = CancellationToken::new();
        let _outer = ScopedLaneCancellation::install(parent.clone(), None);
        let mut base = configured();
        base.cancellation_token = primary.then(CancellationToken::new);
        let mut validated = false;
        let result = run_observed(
            &original,
            &base,
            Some(deadline()),
            &mut |reduced, _| PdrResult::Safe(candidate(reduced)),
            &mut |lifted, configured, _| {
                validated = true;
                let observer = if primary {
                    Observer::Primary
                } else {
                    Observer::Lane
                };
                stop_reset_and_replace(&parent, configured, observer);
                fake_safe(lifted)
            },
            &mut |_: Phase| {},
        );
        assert!(validated && result.unwrap().is_unknown());
        assert!(!parent.is_cancelled());
    }
}

#[test]
fn observation_healthy_attempt_and_local_probe_stop_keep_safe_candidate_route() {
    for primary in [false, true] {
        let original = source(9, false);
        let parent = CancellationToken::new();
        let _outer = ScopedLaneCancellation::install(parent.clone(), None);
        let mut base = configured();
        base.cancellation_token = primary.then(CancellationToken::new);
        for local in [false, true] {
            let result = run_observed(
                &original,
                &base,
                Some(deadline()),
                &mut |reduced, configured| {
                    if local {
                        local_child_stop(&configured, primary);
                    }
                    PdrResult::Safe(candidate(reduced))
                },
                &mut |lifted, _, _| fake_safe(lifted),
                &mut |_: Phase| {},
            );
            assert!(result.unwrap().is_safe());
            assert!(!parent.is_cancelled());
        }
    }
}
