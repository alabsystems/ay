// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T-c, the executor path: a stop is published as the stop it was, never as
//! `SelfCheckRejected`, even after its signal has cleared (P4a.1).

use super::*;
use crate::api::proofs::{arm_one_poll_memory_stop_for_testing, EnvelopeStop};
use crate::executor_types::UnknownOrigin;

/// A process-memory stop that ONE poll of the discharge saw, and that has
/// lapsed by the time the funnel returns (as RSS falls back), is still the
/// published outcome: `Unknown(MemoryLimit)` from `MemoryBudget`. Before the
/// latch, the lanes it ended read as declines and the verdict as
/// `SelfCheckRejected`. Negative control: the same refutation publishes
/// `unsat` when nothing stops it.
#[test]
fn a_stop_one_lane_saw_is_published_as_that_stop_never_as_a_rejection() {
    let mut live = read_over_write_executor("(not (= (select a i) v))");
    forge_trust_refutation(&mut live);
    assert!(
        live.certify_unsat_for_publication(SolveResult::unsat(), &[])
            .is_unsat(),
        "with nothing stopping it the refutation publishes"
    );

    let mut exec = read_over_write_executor("(not (= (select a i) v))");
    forge_trust_refutation(&mut exec);
    arm_one_poll_memory_stop_for_testing();
    let published = exec.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(
        !ay_sys::process_memory_exceeded(),
        "the stop has lapsed by publication time"
    );
    assert!(matches!(published, SolveResult::Unknown), "{published:?}");
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::MemoryLimit));
    assert_eq!(exec.unknown_origin(), Some(UnknownOrigin::MemoryBudget));
    assert!(exec.take_unsat_certificate().is_none());
}

/// Each envelope stop publishes its own `Unknown`, through the canonical
/// boundary, and the term-store ceiling keeps the phrase consumers read to
/// tell a count from an RSS reading.
#[test]
fn every_envelope_stop_publishes_its_own_unknown() {
    for (stop, reason, origin) in [
        (
            EnvelopeStop::Interrupt,
            UnknownReason::Interrupted,
            UnknownOrigin::InterruptFlag,
        ),
        (
            EnvelopeStop::Backstop,
            UnknownReason::Timeout,
            UnknownOrigin::SolveDeadline,
        ),
        (
            EnvelopeStop::ProcessMemory,
            UnknownReason::MemoryLimit,
            UnknownOrigin::MemoryBudget,
        ),
        (
            EnvelopeStop::LaneShare,
            UnknownReason::MemoryLimit,
            UnknownOrigin::MemoryBudget,
        ),
        (
            EnvelopeStop::TermMemory,
            UnknownReason::MemoryLimit,
            UnknownOrigin::MemoryBudget,
        ),
    ] {
        let mut exec = Executor::new();
        let published = exec.publish_envelope_stop(stop);
        assert!(matches!(published, SolveResult::Unknown));
        assert_eq!(exec.unknown_reason(), Some(reason), "{stop:?}");
        assert_eq!(exec.unknown_origin(), Some(origin), "{stop:?}");
        let detail = exec
            .statistics()
            .get_string("unknown.detail")
            .unwrap_or_default()
            .to_string();
        assert_eq!(
            detail.contains("term-store memory ceiling"),
            stop == EnvelopeStop::TermMemory,
            "{stop:?}: {detail}"
        );
    }
}

/// A stop a metered strict walk of this certification observed is published
/// after its signal has cleared: the walk reached no verdict about the proof,
/// so it is never read as a rejection.
#[test]
fn a_walk_stop_is_published_after_its_signal_clears() {
    let mut exec = Executor::new();
    assert!(exec.stop_declines_unsat_publication().is_none());
    exec.certification_stop
        .set(Some(EnvelopeStop::ProcessMemory));
    let published = exec.stop_declines_unsat_publication();
    assert!(
        matches!(published, Some(SolveResult::Unknown)),
        "{published:?}"
    );
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::MemoryLimit));
    assert_eq!(exec.unknown_origin(), Some(UnknownOrigin::MemoryBudget));
}
