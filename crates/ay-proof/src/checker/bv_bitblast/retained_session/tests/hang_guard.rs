// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The retained route keeps the legacy producer's per-attempt hang guard.

use super::super::super::producer_limits::PRODUCER_HANG_GUARD;
use super::*;

#[test]
fn a_far_caller_deadline_never_outlasts_the_producer_hang_guard() {
    let before = Instant::now();
    let limits = attempt_limits(before + Duration::from_secs(86_400));
    let after = Instant::now();
    let end = limits.resolution.deadline.expect("attempt deadline");
    assert!(end >= before + PRODUCER_HANG_GUARD && end <= after + PRODUCER_HANG_GUARD);
    assert_eq!(limits.resolution.validation.deadline, Some(end));
    assert_eq!(proof_replay_limits(&limits).deadline, Some(end));
    // A nearer caller deadline is kept as it is.
    let near = Instant::now() + Duration::from_secs(1);
    let limits = attempt_limits(near);
    assert_eq!(limits.resolution.deadline, Some(near));
    assert_eq!(limits.resolution.validation.deadline, Some(near));
}

#[test]
fn a_hang_guard_stop_is_a_resource_refusal_and_a_caller_stop_a_cancellation() {
    let deadline = || MeteredBridgeError::Bridge(BridgeError::Deadline);
    let pending = Instant::now() + Duration::from_secs(60);
    let passed = Instant::now() - Duration::from_secs(1);
    assert_eq!(
        bridge_error(ProofId(0), deadline(), pending),
        ProofCheckError::ResourceLimit
    );
    assert_eq!(
        bridge_error(ProofId(0), deadline(), passed),
        ProofCheckError::Cancelled
    );
    assert_eq!(
        bridge_error(
            ProofId(0),
            MeteredBridgeError::Bridge(BridgeError::Cancelled),
            pending
        ),
        ProofCheckError::Cancelled
    );
}
