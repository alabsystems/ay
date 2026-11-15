// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[test]
fn sparse_initialization_visits_only_seeded_rows_including_duplicate_seeds() {
    let owner = EmissionProgress::default();
    for clauses in [0, 1, 63, 64, 65, 4095, 4096, 4097, 65_537] {
        let mut budget = 10_000_000;
        let mut queue = Queue::sparse(clauses, &mut budget, &owner).unwrap();
        assert!(!queue.implicitly_pending(0));
        assert_eq!(queue.pop(&mut budget, &owner), Some(None));
        if clauses == 0 {
            continue;
        }
        let expected: BTreeSet<_> = [0, clauses / 2, clauses - 1].into_iter().collect();
        for clause in [clauses - 1, 0, clauses / 2, 0, clauses - 1] {
            queue.insert((0, clause), &mut budget, &owner).unwrap();
        }
        for clause in expected {
            assert!(!queue.implicitly_pending(clause));
            assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, clause))));
        }
        assert_eq!(queue.pop(&mut budget, &owner), Some(None));
    }
}

#[test]
fn sparse_first_round_and_wraps_match_ordered_set_notifications() {
    let owner = EmissionProgress::default();
    for clauses in [1, 65, 4097, 65_537] {
        let mut budget = 10_000_000;
        let mut queue = Queue::sparse(clauses, &mut budget, &owner).unwrap();
        let mut expected = BTreeSet::new();
        for clause in [clauses - 1, 0, clauses / 2] {
            queue.insert((0, clause), &mut budget, &owner).unwrap();
            expected.insert((0usize, clause));
        }
        while let Some((round, clause)) = expected.pop_first() {
            assert_eq!(queue.pop(&mut budget, &owner), Some(Some((round, clause))));
            if round < 3 {
                for row in [0, clauses - 1, clause / 2, (clause + 65) % clauses, clause] {
                    let entry = (round + usize::from(row <= clause), row);
                    for _ in 0..2 {
                        queue.insert(entry, &mut budget, &owner).unwrap();
                        expected.insert(entry);
                    }
                }
            }
        }
        assert_eq!(queue.pop(&mut budget, &owner), Some(None));
    }
}

fn seeded_turn(budget: &mut u64, owner: &EmissionProgress<'_>) -> Option<()> {
    let mut queue = Queue::sparse(65, budget, owner)?;
    queue.insert((0, 1), budget, owner)?;
    queue.insert((0, 64), budget, owner)?;
    assert_eq!(queue.pop(budget, owner)?, Some((0, 1)));
    queue.insert((1, 0), budget, owner)?;
    queue.insert((0, 63), budget, owner)?;
    queue.insert((0, 63), budget, owner)?;
    for expected in [(0, 63), (0, 64), (1, 0)] {
        assert_eq!(queue.pop(budget, owner)?, Some(expected));
    }
    assert_eq!(queue.pop(budget, owner)?, None);
    Some(())
}

#[test]
fn sparse_initial_seed_and_notices_keep_exact_and_short_allowances() {
    let owner = EmissionProgress::default();
    let mut budget = 100_000;
    assert_eq!(seeded_turn(&mut budget, &owner), Some(()));
    let used = 100_000 - budget;
    let mut exact = used;
    assert_eq!(seeded_turn(&mut exact, &owner), Some(()));
    assert_eq!(exact, 0);
    for allowance in 0..used {
        let mut short = allowance;
        assert_eq!(seeded_turn(&mut short, &owner), None);
        assert_eq!(short, 0);
    }
}

#[test]
fn each_sparse_initialization_and_first_round_poll_can_refuse_terminally() {
    let calls = Cell::new(0usize);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    assert_eq!(
        seeded_turn(&mut 100_000, &EmissionProgress::with_caller(&mut accepting)),
        Some(())
    );
    for stop in 1..=calls.get() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut budget = 100_000;
        assert_eq!(seeded_turn(&mut budget, &owner), None);
        assert!(owner.refused());
        let remaining = budget;
        assert_eq!(seeded_turn(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn sparse_first_round_skips_unseeded_summary_ranges_without_a_full_scan() {
    let owner = EmissionProgress::default();
    let mut budget = 1_000_000;
    let mut queue = Queue::sparse(65_537, &mut budget, &owner).unwrap();
    queue.insert((0, 1), &mut budget, &owner).unwrap();
    queue.insert((0, 65_536), &mut budget, &owner).unwrap();
    let before = budget;
    assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, 1))));
    assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, 65_536))));
    assert_eq!(queue.pop(&mut budget, &owner), Some(None));
    assert!(before - budget < 40, "{}", before - budget);
}
