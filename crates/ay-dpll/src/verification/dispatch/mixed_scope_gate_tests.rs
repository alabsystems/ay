// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The per-query scoped re-check gate on its own (#combiner-verify-scope):
//! when it admits the scoped run, when it stops, and when it probes again.

use super::ScopedRecheckGate;

/// A gate whose credit is spent (two misses in a row from a fresh query).
pub(super) fn closed_gate() -> ScopedRecheckGate {
    let mut gate = ScopedRecheckGate::default();
    for _ in 0..2 {
        assert!(gate.admits_scoped_run());
        gate.record(false);
    }
    assert_eq!(gate.credit, 0);
    gate
}

/// A query whose scoped runs keep missing switches them off after two misses,
/// then probes exactly once every `PROBE_INTERVAL` calls, and one re-proving
/// probe wins the scoped path back.
#[test]
fn the_gate_switches_the_scoped_run_off_after_misses_and_probes_it_back() {
    let mut gate = closed_gate();
    for round in 0..3 {
        let skipped = (1..ScopedRecheckGate::PROBE_INTERVAL)
            .filter(|_| !gate.admits_scoped_run())
            .count();
        assert_eq!(
            skipped,
            usize::from(ScopedRecheckGate::PROBE_INTERVAL) - 1,
            "round {round}"
        );
        assert!(gate.admits_scoped_run(), "round {round}: the probe");
        gate.record(false);
    }
    for _ in 1..ScopedRecheckGate::PROBE_INTERVAL {
        assert!(!gate.admits_scoped_run());
    }
    assert!(gate.admits_scoped_run());
    gate.record(true);
    assert!(
        gate.admits_scoped_run(),
        "a re-proving probe re-opens the gate"
    );
}

/// A query whose scoped runs keep re-proving never loses the scoped path, and
/// one miss among re-proofs does not close it.
#[test]
fn a_reproving_query_keeps_the_scoped_run() {
    let mut gate = ScopedRecheckGate::default();
    for call in 0..1000 {
        assert!(gate.admits_scoped_run(), "call {call}");
        gate.record(call % 10 != 9);
    }
    // Saturated at the cap, minus the final call's miss.
    assert_eq!(
        gate.credit,
        ScopedRecheckGate::MAX_CREDIT - ScopedRecheckGate::MISS_COST
    );
}

/// The break-even: a query re-proving three of every four scoped runs keeps
/// the scoped path; one re-proving two of every three loses it.
#[test]
fn the_gate_breaks_even_at_three_quarters_reproved() {
    let mut gate = ScopedRecheckGate::default();
    for call in 0..1000 {
        assert!(gate.admits_scoped_run(), "3 of 4: call {call}");
        gate.record(call % 4 != 3);
    }
    let mut gate = ScopedRecheckGate::default();
    let closed_after = (0..1000)
        .position(|call| {
            let admitted = gate.admits_scoped_run();
            if admitted {
                gate.record(call % 3 != 2);
            }
            !admitted
        })
        .expect("2 of 3 re-proved closes the gate");
    assert!(closed_after < 30, "closed after {closed_after} calls");
}
