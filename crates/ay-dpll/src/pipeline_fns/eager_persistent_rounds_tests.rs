// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn counts(conflicts: u64, decisions: u64, lifetime_conflicts: u64) -> SolverCounts {
    SolverCounts {
        conflicts,
        decisions,
        lifetime_conflicts,
        full_solve_may_keep_conflicts: false,
    }
}

#[test]
fn the_first_round_has_no_slice_and_later_rounds_have_calibrated_decision_slices() {
    assert_eq!(round_slice(0, RoundEntry::Full, 1), None);
    assert_eq!(
        round_slice(1, RoundEntry::Full, 1),
        Some(700 * DECISIONS_PER_MS)
    );
    assert_eq!(
        round_slice(1000, RoundEntry::Full, 1),
        Some(30_000 * DECISIONS_PER_MS),
        "the full-solve decision slice has a fixed cap"
    );
    assert_eq!(
        round_slice(3, RoundEntry::Resume, 1),
        Some(30_000 * DECISIONS_PER_MS)
    );
    assert_eq!(
        round_slice(3, RoundEntry::Continue, 1),
        Some(15_000 * DECISIONS_PER_MS)
    );
    assert_eq!(RoundEntry::of(true, true), RoundEntry::Resume);
    assert_eq!(RoundEntry::of(false, true), RoundEntry::Continue);
    assert_eq!(RoundEntry::of(false, false), RoundEntry::Full);
}

#[test]
fn a_determinism_test_can_shrink_a_slice_but_never_to_nothing() {
    assert_eq!(
        round_slice(1, RoundEntry::Full, 16),
        Some(700 * DECISIONS_PER_MS / 16)
    );
    assert_eq!(
        round_slice(1, RoundEntry::Full, 0),
        round_slice(1, RoundEntry::Full, 1)
    );
    assert_eq!(round_slice(1, RoundEntry::Full, u64::MAX), Some(1));
    assert_eq!(round_slice(0, RoundEntry::Full, 16), None);
}

#[test]
fn a_fresh_search_counts_from_where_its_full_solve_starts_its_counters() {
    let now = counts(7, 90, 1_007);
    let search = SearchAllowance::fresh(Some(500), Some(24_000), now);
    let round = arm_round(&search, None, RoundEntry::Full, now);
    // A full solve restarts `num_conflicts` and `num_decisions` at zero, so
    // both targets count from zero: the solve gets exactly its allowance.
    assert_eq!(round.conflict_target, Some(500));
    assert_eq!(round.decision_target, Some(24_000));
    // An IC3-mode solver's incremental reset keeps `num_conflicts` running,
    // so its conflict target counts from now (its decisions still restart).
    let ic3 = SolverCounts {
        full_solve_may_keep_conflicts: true,
        ..now
    };
    let round = arm_round(&search, None, RoundEntry::Full, ic3);
    assert_eq!(round.conflict_target, Some(7 + 500));
    assert_eq!(round.decision_target, Some(24_000));
    let unbounded = SearchAllowance::fresh(None, None, now);
    let round = arm_round(&unbounded, None, RoundEntry::Full, now);
    assert_eq!((round.conflict_target, round.decision_target), (None, None));
}

#[test]
fn the_slice_binds_only_when_tighter_than_what_the_search_has_left() {
    let now = counts(0, 1_000, 0);
    let search = SearchAllowance::fresh(Some(500), Some(10_000), now);
    let resume = arm_round(&search, Some(4_000), RoundEntry::Resume, now);
    assert_eq!(resume.decision_target, Some(1_000 + 4_000));
    assert!(resume.slice_binds);
    let wide = arm_round(&search, Some(40_000), RoundEntry::Resume, now);
    assert_eq!(wide.decision_target, Some(1_000 + 10_000));
    assert!(!wide.slice_binds);
    let no_decision_allowance = SearchAllowance::fresh(Some(500), None, now);
    let round = arm_round(&no_decision_allowance, Some(4_000), RoundEntry::Full, now);
    assert_eq!(round.decision_target, Some(4_000));
    assert!(round.slice_binds);
}

#[test]
fn only_the_rounds_own_slice_continues_the_search() {
    let start = counts(0, 0, 0);
    let mut search = SearchAllowance::fresh(Some(500), Some(10_000), start);
    let round = arm_round(&search, Some(4_000), RoundEntry::Full, start);
    let stop = Some(SatUnknownReason::ResourceBudget);
    assert!(
        settle_round(&mut search, &round, stop, counts(30, 4_000, 30)),
        "the slice stopped the solve"
    );
    assert_eq!(search.decisions_left, Some(6_000));

    // The next round resumes the same search: its decisions count from where
    // the last one left off, and the conflicts from the search's start.
    let now = counts(30, 4_000, 30);
    let resume = arm_round(&search, Some(4_000), RoundEntry::Resume, now);
    assert_eq!(resume.conflict_target, Some(30 + 470));
    assert_eq!(resume.decision_target, Some(8_000));
    // Conflicts ran out first: that is the search's allowance.
    let mut drained = search;
    assert!(!settle_round(
        &mut drained,
        &resume,
        stop,
        counts(500, 7_000, 500)
    ));
    // A stop that is not the budget's never continues the search.
    let mut stopped = search;
    assert!(!settle_round(
        &mut stopped,
        &resume,
        Some(SatUnknownReason::Interrupted),
        counts(40, 8_000, 40)
    ));
    // The slice was reached and the decisions are spent with it: nothing is
    // left to continue on.
    let mut spent = SearchAllowance::fresh(Some(500), Some(4_500), start);
    let round = arm_round(&spent, Some(4_000), RoundEntry::Full, start);
    assert!(!settle_round(&mut spent, &round, stop, counts(9, 4_500, 9)));
}

#[test]
fn the_search_allowance_bounds_a_chain_of_slices() {
    let start = counts(0, 0, 0);
    let mut search = SearchAllowance::fresh(None, Some(10_000), start);
    let mut decisions = 0;
    let mut rounds = 0;
    let mut entry = RoundEntry::Full;
    loop {
        let now = counts(0, decisions, 0);
        let round = arm_round(&search, Some(3_000), entry, now);
        let target = round.decision_target.unwrap_or(u64::MAX);
        decisions = target;
        rounds += 1;
        let after = counts(0, decisions, 0);
        if !settle_round(
            &mut search,
            &round,
            Some(SatUnknownReason::ResourceBudget),
            after,
        ) {
            break;
        }
        entry = RoundEntry::Resume;
    }
    assert_eq!(
        decisions, 10_000,
        "the chain stops at the search's allowance"
    );
    assert_eq!(rounds, 4, "three slices of 3,000, then the last 1,000");
}
