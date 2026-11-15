// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

#[test]
fn initial_notice_stops_at_the_first_already_pending_occurrence() {
    for (length, expected_work) in [(64, 6), (65, 8), (4097, 10), (65_537, 10)] {
        let db = vec![vec![(1, true)]; length];
        let owner = EmissionProgress::default();
        let budget = &mut 10_000_000;
        let index = Occurrences::new(&db, budget, &owner).unwrap();
        let mut sweep = index.sweep(budget, &owner).unwrap();
        assert_eq!(sweep.next(budget, &owner), Some(Some(0)));
        let before = *budget;
        sweep.assigned(&index, 1, budget, &owner).unwrap();
        // Two occurrence reads, one map lookup and one queue insertion,
        // plus two word operations per bitmap level. No tail traversal.
        assert_eq!(before - *budget, expected_work);
        for expected in 1..length {
            assert_eq!(sweep.next(budget, &owner), Some(Some(expected)));
        }
        assert_eq!(sweep.next(budget, &owner), Some(Some(0)));
        assert_eq!(sweep.next(budget, &owner), Some(None));
    }
}

#[test]
fn later_round_notices_still_schedule_the_full_affected_suffix() {
    let db = vec![vec![(1, true)]; 4];
    let owner = EmissionProgress::default();
    let budget = &mut 100_000;
    let index = Occurrences::new(&db, budget, &owner).unwrap();
    let mut sweep = index.sweep(budget, &owner).unwrap();
    assert_eq!(sweep.next(budget, &owner), Some(Some(0)));
    sweep.assigned(&index, 1, budget, &owner).unwrap();
    for expected in [1, 2, 3, 0] {
        assert_eq!(sweep.next(budget, &owner), Some(Some(expected)));
    }
    sweep.assigned(&index, 1, budget, &owner).unwrap();
    for expected in [1, 2, 3, 0] {
        assert_eq!(sweep.next(budget, &owner), Some(Some(expected)));
    }
    assert_eq!(sweep.next(budget, &owner), Some(None));
}

#[test]
fn appended_rows_require_a_fresh_sweep_even_when_in_the_implicit_suffix() {
    let owner = EmissionProgress::default();
    let budget = &mut 100_000;
    let mut index = Occurrences::new(&[vec![(1, true)]], budget, &owner).unwrap();
    let mut sweep = index.sweep(budget, &owner).unwrap();
    assert_eq!(sweep.next(budget, &owner), Some(Some(0)));
    index.append(&vec![(1, false)], budget, &owner).unwrap();
    assert_eq!(sweep.assigned(&index, 1, budget, &owner), None);
    assert_eq!(*budget, 0);
    assert_eq!(index.sweep(budget, &owner).map(|_| ()), None);
    // A separate accepting invocation includes the appended row from the start.
    let fresh_owner = EmissionProgress::default();
    let fresh_budget = &mut 100_000;
    let index = Occurrences::new(
        &[vec![(1, true)], vec![(1, false)]],
        fresh_budget,
        &fresh_owner,
    )
    .unwrap();
    let mut sweep = index.sweep(fresh_budget, &fresh_owner).unwrap();
    assert_eq!(sweep.next(fresh_budget, &fresh_owner), Some(Some(0)));
    assert_eq!(sweep.next(fresh_budget, &fresh_owner), Some(Some(1)));
}

fn notice(budget: &mut u64, owner: &EmissionProgress<'_>) -> Option<()> {
    let db = vec![vec![(1, true), (1, true)]; 4];
    let index = Occurrences::new(&db, budget, owner)?;
    let mut sweep = index.sweep(budget, owner)?;
    sweep.next(budget, owner)??;
    sweep.assigned(&index, 1, budget, owner)
}

#[test]
fn first_suffix_cut_keeps_exact_allowances_and_every_owner_refusal_terminal() {
    let calls = Cell::new(0usize);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    let mut budget = 100_000;
    assert_eq!(notice(&mut budget, &owner), Some(()));
    let used = 100_000 - budget;
    let total_calls = calls.get();
    let mut exact = used;
    assert_eq!(notice(&mut exact, &owner), Some(()));
    assert_eq!(exact, 0);
    for allowance in [0, used - 1] {
        let mut short = allowance;
        assert_eq!(notice(&mut short, &owner), None);
        assert_eq!(short, 0);
        assert_eq!(notice(&mut short, &owner), None);
    }
    for stop in 1..=total_calls {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut remaining = 100_000;
        assert_eq!(notice(&mut remaining, &owner), None);
        assert!(owner.refused());
        let before = remaining;
        assert_eq!(notice(&mut remaining, &owner), None);
        assert_eq!(remaining, before);
        assert_eq!(seen.get(), stop);
    }
}
