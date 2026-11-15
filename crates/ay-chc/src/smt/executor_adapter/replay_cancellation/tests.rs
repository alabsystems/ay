// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn owned_observation_is_send_sync_and_starts_live() {
    fn require_send_sync<T: Send + Sync>() {}
    require_send_sync::<ReplayCancellation>();
    let token = CancellationToken::new();
    let control = ReplayCancellation::new(&token);
    assert!(!control.is_cancelled());
    assert!(!control.clone().is_cancelled());
    assert!(!token.is_cancelled());
}

#[test]
fn local_observation_is_sticky_across_all_clones() {
    let token = CancellationToken::new();
    let control = ReplayCancellation::new(&token);
    let worker = control.clone();
    token.cancel();
    assert!(worker.is_cancelled());
    token.reset();
    assert!(!token.is_cancelled());
    assert!(control.is_cancelled());
    assert!(worker.is_cancelled());
    assert!(control.clone().is_cancelled());
}

#[test]
fn constructor_observes_precancel_before_a_later_reset() {
    let token = CancellationToken::new();
    token.cancel();
    let control = ReplayCancellation::new(&token);
    token.reset();
    assert!(control.is_cancelled());
    assert!(!token.is_cancelled());
}

#[test]
fn inherited_parent_and_grandparent_flags_are_not_lost() {
    let parent = CancellationToken::new();
    let child = parent.child();
    let grandchild = child.child();
    let control = ReplayCancellation::new(&grandchild);
    parent.cancel();
    assert!(control.is_cancelled());
    parent.reset();
    assert!(!grandchild.is_cancelled());
    assert!(control.is_cancelled());
}

#[test]
fn every_linked_parent_can_cancel_the_attempt() {
    for selected in 0..3 {
        let parents = [
            CancellationToken::new(),
            CancellationToken::new(),
            CancellationToken::new(),
        ];
        let mut token = CancellationToken::new();
        for parent in &parents {
            token.link_upstream(parent);
        }
        let control = ReplayCancellation::new(&token);
        parents[selected].cancel();
        assert!(control.clone().is_cancelled());
        parents[selected].reset();
        assert!(control.is_cancelled());
        assert!(!token.is_cancelled());
    }
}

#[test]
fn child_cancel_and_observation_never_poison_parent_or_sibling() {
    let parent = CancellationToken::new();
    let child = parent.child();
    let sibling = parent.child();
    let control = ReplayCancellation::new(&child);
    child.cancel();
    assert!(control.is_cancelled());
    assert!(!parent.is_cancelled());
    assert!(!sibling.is_cancelled());
    child.reset();
    assert!(control.is_cancelled());
    assert!(!child.is_cancelled());
}

#[test]
fn retry_has_a_fresh_observation_after_caller_reset() {
    let token = CancellationToken::new();
    let old = ReplayCancellation::new(&token);
    token.cancel();
    assert!(old.is_cancelled());
    token.reset();
    let retry = ReplayCancellation::new(&token);
    assert!(!retry.is_cancelled());
    assert!(old.is_cancelled());
}

#[test]
fn token_links_are_captured_before_handoff_not_retroactively() {
    let parent = CancellationToken::new();
    let mut token = CancellationToken::new();
    let before_link = ReplayCancellation::new(&token);
    token.link_upstream(&parent);
    let after_link = ReplayCancellation::new(&token);
    parent.cancel();
    assert!(after_link.is_cancelled());
    assert!(!before_link.is_cancelled());
}
