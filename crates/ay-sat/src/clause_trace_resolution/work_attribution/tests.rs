// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::clause_trace_resolution::*;

mod meter;
mod seams;

fn count(snapshot: &WorkSnapshot, phase: ConversionPhase) -> u64 {
    snapshot.0.counts[phase as usize]
}

fn assert_total(snapshot: &WorkSnapshot, total: u64) {
    assert_eq!(snapshot.0.last_work, total);
    assert_eq!(
        snapshot
            .0
            .counts
            .iter()
            .map(|&n| u128::from(n))
            .sum::<u128>(),
        u128::from(total)
    );
}

#[test]
fn phases_form_an_exclusive_partition_including_other_and_pending_work() {
    let mut ledger = WorkAttribution::default();
    assert_total(&ledger.snapshot(0), 0);
    assert_eq!(
        ledger.switch(ConversionPhase::Derived, 3),
        ConversionPhase::Other
    );
    assert_eq!(
        ledger.switch(ConversionPhase::Compaction, 8),
        ConversionPhase::Derived
    );
    ledger.switch(ConversionPhase::Derived, 15);
    ledger.switch(ConversionPhase::Compaction, 17);
    ledger.switch(ConversionPhase::Derived, 28);
    ledger.switch(ConversionPhase::Other, 41);
    let snapshot = ledger.snapshot(58);
    assert_total(&snapshot, 58);
    assert!(snapshot.0.complete);
    assert_eq!(count(&snapshot, ConversionPhase::Other), 20);
    assert_eq!(count(&snapshot, ConversionPhase::Derived), 20);
    assert_eq!(count(&snapshot, ConversionPhase::Compaction), 18);
    assert_eq!(ledger.last_work, 41, "snapshot is read-only");
    assert_eq!(count(&ledger.snapshot(41), ConversionPhase::Other), 3);
}

#[test]
fn every_named_phase_has_one_stable_nonoverlapping_bin() {
    let phases = [
        ConversionPhase::Other,
        ConversionPhase::Preflight,
        ConversionPhase::Namespace,
        ConversionPhase::Originals,
        ConversionPhase::Derived,
        ConversionPhase::Compaction,
        ConversionPhase::RootSetup,
        ConversionPhase::RootedRepair,
        ConversionPhase::Synthesis,
        ConversionPhase::Finalize,
    ];
    let mut ledger = WorkAttribution::default();
    let mut total = 0;
    for (index, phase) in phases.into_iter().enumerate() {
        ledger.switch(phase, total);
        total += index as u64 + 1;
    }
    let snapshot = ledger.snapshot(total);
    assert_total(&snapshot, 55);
    assert_eq!(snapshot.0.counts, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    assert_eq!(
        snapshot.to_string(),
        "total=55 phase=finalize complete=true other=1 preflight=2 namespace=3 originals=4 derived=5 compaction=6 root_setup=7 rooted_repair=8 synthesis=9 finalize=10"
    );
}

#[test]
fn maximum_work_and_zero_delta_preserve_exact_totals() {
    let mut ledger = WorkAttribution::default();
    ledger.switch(ConversionPhase::Preflight, 0);
    ledger.switch(ConversionPhase::Derived, u64::MAX - 7);
    ledger.switch(ConversionPhase::Derived, u64::MAX - 7);
    let snapshot = ledger.snapshot(u64::MAX);
    assert_total(&snapshot, u64::MAX);
    assert!(snapshot.0.complete);
    assert_eq!(count(&snapshot, ConversionPhase::Preflight), u64::MAX - 7);
    assert_eq!(count(&snapshot, ConversionPhase::Derived), 7);
}

#[test]
fn broken_diagnostic_invariants_keep_total_and_explicitly_disclaim_partition() {
    let mut ledger = WorkAttribution::default();
    ledger.switch(ConversionPhase::Originals, 9);
    ledger.switch(ConversionPhase::Derived, 4);
    let snapshot = ledger.snapshot(7);
    assert_total(&snapshot, 7);
    assert!(!snapshot.0.complete);
    assert_eq!(count(&snapshot, ConversionPhase::Other), 4);
    assert_eq!(count(&snapshot, ConversionPhase::Derived), 3);

    // No valid meter sequence can overflow a subtotal. Inject that internal
    // defect to pin the non-panicking, non-authoritative fallback anyway.
    ledger.counts[ConversionPhase::Derived as usize] = u64::MAX;
    let snapshot = ledger.snapshot(8);
    assert_total(&snapshot, 8);
    assert!(!snapshot.0.complete);
    assert_eq!(count(&snapshot, ConversionPhase::Other), 8);
    assert_eq!(count(&snapshot, ConversionPhase::Derived), 0);
}
