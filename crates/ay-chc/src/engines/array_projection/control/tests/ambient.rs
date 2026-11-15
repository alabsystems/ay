// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::engines::ambient_cancellation::support::{stop_reset_and_replace, Observer};
use crate::smt::deadline::{lane_interrupt_flag, ScopedLaneCancellation};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[test]
fn search_and_validation_descendants_share_captured_ambient_observation() {
    for primary in [false, true] {
        for validation in [false, true] {
            for observe_config in [false, true] {
                if observe_config && !primary {
                    continue;
                }
                let parent = CancellationToken::new();
                let _outer = ScopedLaneCancellation::install(parent.clone(), None);
                let mut base = configured();
                base.cancellation_token = primary.then(CancellationToken::new);
                let until = Instant::now() + Duration::from_secs(60);
                let mut owner = Owner::capture(&base, Some(until));
                let _attempt = owner.install_lane();
                let configured = if validation {
                    owner.validation_config(&base)
                } else {
                    owner.search_config(&base, until)
                };
                assert_eq!(configured.cancellation_token.is_some(), primary);
                assert!(configured.external_cancellation_token.is_none());
                let observed = if observe_config {
                    Observer::Primary
                } else {
                    Observer::Lane
                };
                stop_reset_and_replace(&parent, &configured, observed);
                let replacement = CancellationToken::new();
                {
                    let _replacement = ScopedLaneCancellation::install(replacement, None);
                    assert!(!crate::smt::deadline::lane_cancelled());
                    assert!(
                        !owner.open(),
                        "retained identity refuses under healthy replacement"
                    );
                }
                assert!(!parent.is_cancelled());
                assert!(!Owner::capture(&base, Some(until)).open());
                drop(_attempt);
                assert!(
                    Owner::capture(&base, Some(until)).open(),
                    "fresh original attempt"
                );
            }
        }
    }
}

#[test]
fn external_only_presence_and_descendant_observation_are_preserved() {
    let parent = CancellationToken::new();
    let _outer = ScopedLaneCancellation::install(parent.clone(), None);
    let mut base = configured();
    base.external_cancellation_token = Some(CancellationToken::new());
    let until = Instant::now() + Duration::from_secs(60);
    let mut owner = Owner::capture(&base, Some(until));
    let _attempt = owner.install_lane();
    let search = owner.search_config(&base, until);
    assert!(search.cancellation_token.is_none());
    assert!(search.external_cancellation_token.is_some());
    stop_reset_and_replace(&parent, &search, Observer::External);
    assert!(!owner.open());
    drop(_attempt);
    assert!(Owner::capture(&base, Some(until)).open());
}

#[test]
fn capture_install_preserves_exact_interrupt_and_healthy_local_child_semantics() {
    let parent = CancellationToken::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    let _outer = ScopedLaneCancellation::install(parent.clone(), Some(interrupt.clone()));
    let base = configured();
    let until = Instant::now() + Duration::from_secs(60);
    let mut owner = Owner::capture(&base, Some(until));
    {
        let _attempt = owner.install_lane();
        assert!(Arc::ptr_eq(&lane_interrupt_flag().unwrap(), &interrupt));
        let child = crate::smt::deadline::current_lane_token().unwrap().child();
        child.cancel();
        assert!(child.is_cancelled());
        assert!(owner.open());
        assert!(!parent.is_cancelled());
        assert!(!interrupt.load(Ordering::Relaxed));
    }
    assert!(Arc::ptr_eq(&lane_interrupt_flag().unwrap(), &interrupt));
    assert!(owner.open());
}

#[test]
fn a_new_current_lane_stop_remains_an_additional_refusal_boundary() {
    let original = CancellationToken::new();
    let _outer = ScopedLaneCancellation::install(original.clone(), None);
    let base = configured();
    let mut owner = Owner::capture(&base, None);
    let _attempt = owner.install_lane();
    let replacement = CancellationToken::new();
    {
        let _replacement = ScopedLaneCancellation::install(replacement.clone(), None);
        replacement.cancel();
        assert!(!owner.open());
        replacement.reset();
    }
    assert!(!original.is_cancelled());
    assert!(!owner.open(), "current replacement refusal was observed");
}
