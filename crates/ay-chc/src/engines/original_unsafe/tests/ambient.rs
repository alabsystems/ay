// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Simulated witness/validator controls; an empty trace is not proof evidence.

use super::*;
use crate::engines::ambient_cancellation::support::{
    local_child_stop, stop_reset_and_replace, Observer,
};
use crate::smt::deadline::ScopedLaneCancellation;

#[test]
fn original_search_descendant_stop_survives_parent_reset_and_lane_replacement() {
    for primary in [false, true] {
        let original = source();
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
            &mut |_, _, configured| {
                searched = true;
                assert_eq!(configured.cancellation_token.is_some(), primary);
                stop_reset_and_replace(&parent, configured, Observer::Lane);
                Some(candidate())
            },
            &mut |cex, _, _| {
                validated = true;
                fake_unsafe(cex)
            },
            &mut |_| {},
        );
        assert!(searched && !validated);
        assert!(result.unwrap().is_unknown());
        assert!(!parent.is_cancelled());
        assert!(!crate::smt::deadline::lane_cancelled());
    }
}

#[test]
fn original_validation_descendant_stop_refuses_late_witness_after_reset() {
    for primary in [false, true] {
        let original = source();
        let parent = CancellationToken::new();
        let _outer = ScopedLaneCancellation::install(parent.clone(), None);
        let mut base = configured();
        base.cancellation_token = primary.then(CancellationToken::new);
        let mut validated = false;
        let result = run_observed(
            &original,
            &base,
            Some(deadline()),
            &mut |_, _, _| Some(candidate()),
            &mut |cex, configured, _| {
                validated = true;
                let observer = if primary {
                    Observer::Primary
                } else {
                    Observer::Lane
                };
                stop_reset_and_replace(&parent, configured, observer);
                fake_unsafe(cex)
            },
            &mut |_| {},
        );
        assert!(validated && result.unwrap().is_unknown());
        assert!(!parent.is_cancelled());
    }
}

#[test]
fn original_healthy_attempt_and_local_probe_stop_keep_original_witness_route() {
    for primary in [false, true] {
        let original = source();
        let parent = CancellationToken::new();
        let _outer = ScopedLaneCancellation::install(parent.clone(), None);
        let mut base = configured();
        base.cancellation_token = primary.then(CancellationToken::new);
        for local in [false, true] {
            let result = run_observed(
                &original,
                &base,
                Some(deadline()),
                &mut |_, _, configured| {
                    if local {
                        local_child_stop(configured, primary);
                    }
                    Some(candidate())
                },
                &mut |cex, _, _| fake_unsafe(cex),
                &mut |_| {},
            );
            assert!(result.unwrap().is_unsafe());
            assert!(!parent.is_cancelled());
        }
    }
}
