// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn descendant_observation_survives_parent_and_attempt_reset() {
    let parent = CancellationToken::new();
    let attempt = parent.sticky_child();
    let child = attempt.child().child();
    let sibling = attempt.child();
    parent.cancel();
    assert!(child.is_cancelled());
    parent.reset();
    attempt.reset();
    child.reset();
    assert!(!parent.is_cancelled());
    assert!(attempt.is_cancelled());
    assert!(child.is_cancelled());
    assert!(sibling.is_cancelled());
    assert!(attempt.child().is_cancelled());
    assert!(!parent.sticky_child().is_cancelled());
}

#[test]
fn own_lane_cancellation_does_not_latch_an_upstream_refusal() {
    let parent = CancellationToken::new();
    let attempt = parent.sticky_child();
    let lane = attempt.child();
    let sibling = attempt.child();
    lane.cancel();
    assert!(lane.is_cancelled());
    assert!(!sibling.is_cancelled());
    assert!(!attempt.is_cancelled());
    assert!(!parent.is_cancelled());
    lane.reset();
    assert!(!lane.is_cancelled());
    attempt.cancel();
    assert!(lane.is_cancelled());
    attempt.reset();
    assert!(!lane.is_cancelled());
}

#[test]
fn linked_solver_observation_is_shared_without_duplicate_links() {
    let parent = CancellationToken::new();
    let attempt = parent.sticky_child();
    let mut solver = CancellationToken::new();
    let old_clone = solver.clone();
    solver.link_upstream(&attempt);
    solver.link_upstream(&attempt);
    assert_eq!(solver.sticky_upstream.len(), 1);
    assert_eq!(solver.upstream.len(), 2);
    parent.cancel();
    assert!(solver.is_cancelled());
    parent.reset();
    assert!(attempt.is_cancelled());
    assert!(solver.clone().is_cancelled());
    assert!(!old_clone.is_cancelled());
}

#[test]
fn inherited_grandparent_and_initial_cancellation_latch() {
    let upstream = CancellationToken::new();
    let parent = upstream.child();
    upstream.cancel();
    let attempt = parent.sticky_child();
    upstream.reset();
    assert!(!parent.is_cancelled());
    assert!(attempt.is_cancelled());
    assert!(attempt.clone().is_cancelled());
}

#[test]
fn nested_attempt_latches_its_parent_without_poisoning_outer_siblings() {
    let caller = CancellationToken::new();
    let batch = caller.sticky_child();
    let outer_sibling = batch.child();
    let lane = batch.child();
    let lane_attempt = lane.sticky_child();
    lane.cancel();
    assert!(lane_attempt.child().is_cancelled());
    lane.reset();
    assert!(lane_attempt.is_cancelled());
    assert!(!lane.is_cancelled());
    assert!(!batch.is_cancelled());
    assert!(!outer_sibling.is_cancelled());
}

#[test]
fn ordinary_children_keep_reusable_reset_semantics() {
    let parent = CancellationToken::new();
    let child = parent.child();
    parent.cancel();
    assert!(child.is_cancelled());
    parent.reset();
    assert!(!child.is_cancelled());
    assert!(parent.sticky_upstream.is_empty());
    assert!(child.sticky_upstream.is_empty());
}

#[test]
fn cross_thread_descendant_observation_latches_before_caller_reset() {
    let parent = CancellationToken::new();
    let attempt = parent.sticky_child();
    let child = attempt.child();
    parent.cancel();
    let observed = std::thread::spawn(move || child.is_cancelled());
    assert!(observed.join().expect("observation thread"));
    parent.reset();
    assert!(attempt.is_cancelled());
}

#[test]
fn unobserved_cancel_reset_pulse_is_not_claimed_as_observed() {
    let parent = CancellationToken::new();
    let attempt = parent.sticky_child();
    parent.cancel();
    parent.reset();
    assert!(!attempt.is_cancelled());
}
