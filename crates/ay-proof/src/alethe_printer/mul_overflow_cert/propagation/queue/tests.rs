// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use std::cell::Cell;
use std::collections::BTreeSet;

mod sparse;

thread_local! {
    static BITMAP_ACCESSES: Cell<usize> = const { Cell::new(0) };
}

pub(super) fn bitmap_access() {
    BITMAP_ACCESSES.with(|accesses| accesses.set(accesses.get() + 1));
}

fn bitmap_accesses() -> usize {
    BITMAP_ACCESSES.with(Cell::get)
}

#[test]
fn implicit_first_sweep_has_constant_owner_work_and_no_bitmap_accesses() {
    for clauses in [1, 63, 64, 65, 4095, 4096, 4097, 8193] {
        let mut budget = 1_000_000;
        let mut queue = Queue::all(clauses, &mut budget, &EmissionProgress::default()).unwrap();
        assert!(queue.levels.iter().flatten().all(|&word| word == 0));
        let calls = Cell::new(0);
        let mut callback = || {
            calls.set(calls.get() + 1);
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let accesses = bitmap_accesses();
        let initial = budget;
        for clause in 0..clauses {
            let before = calls.get();
            assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, clause))));
            assert_eq!(calls.get() - before, 3, "pre/post debit and exit fences");
            assert_eq!(initial - budget, clause as u64 + 1);
            assert_eq!(bitmap_accesses(), accesses);
        }
        assert!(queue.levels.iter().flatten().all(|&word| word == 0));
        assert_eq!(queue.pop(&mut budget, &owner), Some(None));
    }
}

#[test]
fn notices_for_the_implicit_suffix_do_not_touch_pending_prefix_bits() {
    let mut budget = 100_000;
    let mut queue = Queue::all(129, &mut budget, &EmissionProgress::default()).unwrap();
    assert_eq!(
        queue.pop(&mut budget, &EmissionProgress::default()),
        Some(Some((0, 0)))
    );
    queue
        .insert((1, 0), &mut budget, &EmissionProgress::default())
        .unwrap();
    let pending = queue.levels.clone();
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut callback);
    let accesses = bitmap_accesses();
    for clause in 1..129 {
        let before = (budget, calls.get());
        queue.insert((0, clause), &mut budget, &owner).unwrap();
        assert_eq!(before.0 - budget, 1);
        assert_eq!(calls.get() - before.1, 3);
        assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, clause))));
        assert_eq!(bitmap_accesses(), accesses);
        assert_eq!(queue.levels, pending);
    }
    assert_eq!(queue.pop(&mut budget, &owner), Some(Some((1, 0))));
    assert_eq!(queue.pop(&mut budget, &owner), Some(None));
}

#[test]
fn implicit_membership_does_not_bypass_index_or_round_validation() {
    let owner = EmissionProgress::default();
    for invalid in [(0, 5), (1, 4), (0, 0)] {
        let mut budget = 100_000;
        let mut queue = Queue::all(5, &mut budget, &owner).unwrap();
        assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, 0))));
        assert_eq!(queue.insert(invalid, &mut budget, &owner), None);
        assert_eq!(budget, 0);
        assert_eq!(queue.pop(&mut budget, &owner), None);
    }
}

fn implicit_turn(queue: &mut Queue, budget: &mut u64, owner: &EmissionProgress<'_>) -> Option<()> {
    assert_eq!(queue.pop(budget, owner)?, Some((0, 0)));
    queue.insert((0, 4), budget, owner)?;
    queue.insert((1, 0), budget, owner)?;
    for clause in 1..5 {
        assert_eq!(queue.pop(budget, owner)?, Some((0, clause)));
    }
    assert_eq!(queue.pop(budget, owner)?, Some((1, 0)));
    assert_eq!(queue.pop(budget, owner)?, None);
    Some(())
}

#[test]
fn implicit_sweep_keeps_exact_allowances_and_every_refusal_terminal() {
    let fresh = || Queue::all(5, &mut 100_000, &EmissionProgress::default()).unwrap();
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    let mut budget = 100_000;
    assert_eq!(implicit_turn(&mut fresh(), &mut budget, &owner), Some(()));
    let used = 100_000 - budget;
    for (allowance, accepted) in [(used, true), (used - 1, false), (0, false)] {
        let mut budget = allowance;
        assert_eq!(
            implicit_turn(&mut fresh(), &mut budget, &EmissionProgress::default()).is_some(),
            accepted
        );
        assert_eq!(budget, 0);
    }
    for stop in 1..=calls.get() {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut queue = fresh();
        let mut budget = 100_000;
        assert_eq!(implicit_turn(&mut queue, &mut budget, &owner), None);
        assert!(owner.refused());
        assert_eq!(seen.get(), stop);
        let remaining = budget;
        assert_eq!(queue.pop(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn implicit_cursor_update_unwinds_cannot_revive_the_attempt() {
    // All three first-pop observations, including the fence after mutation.
    for stop in 1..=3 {
        let mut budget = 100_000;
        let mut queue = Queue::all(5, &mut budget, &EmissionProgress::default()).unwrap();
        let calls = Cell::new(0);
        let mut callback = || {
            calls.set(calls.get() + 1);
            assert_ne!(
                calls.get(),
                stop,
                "original implicit-sweep observer unwound"
            );
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            queue.pop(&mut budget, &owner)
        }))
        .is_err());
        assert!(owner.refused());
        let remaining = budget;
        assert_eq!(queue.pop(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(calls.get(), stop);
    }
}

fn drain_all(clauses: usize) -> u64 {
    let owner = EmissionProgress::default();
    let mut budget = 1_000_000;
    let mut queue = Queue::all(clauses, &mut budget, &owner).unwrap();
    for clause in 0..clauses {
        assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, clause))));
    }
    assert_eq!(queue.pop(&mut budget, &owner), Some(None));
    1_000_000 - budget
}

#[test]
fn full_sweeps_have_linear_work_across_word_and_summary_boundaries() {
    for clauses in [0, 1, 63, 64, 65, 4095, 4096, 4097, 8193] {
        // Includes every scratch allocation, initialized word, successor
        // examination and removal; no uncharged heap rebuild or scan.
        assert!(drain_all(clauses) < 6 * clauses as u64 + 32, "{clauses}");
    }
}

#[test]
fn sparse_rounds_match_exact_ordered_set_advice() {
    let owner = EmissionProgress::default();
    for clauses in [1, 63, 64, 65, 4095, 4096, 4097, 8193] {
        let mut budget = 10_000_000;
        let mut queue = Queue::all(clauses, &mut budget, &owner).unwrap();
        let mut expected: BTreeSet<_> = (0..clauses).map(|clause| (0, clause)).collect();
        let mut queued = vec![true; clauses];
        for _ in 0..clauses + 200 {
            let Some((round, clause)) = expected.pop_first() else {
                assert_eq!(queue.pop(&mut budget, &owner), Some(None));
                break;
            };
            assert_eq!(queue.pop(&mut budget, &owner), Some(Some((round, clause))));
            queued[clause] = false;
            // Alternate far-apart predecessors and successors, with duplicate
            // notices. This crosses both word boundaries and summary levels.
            if round < 3 {
                for row in [0, clauses - 1, clause / 2, (clause + 65) % clauses, clause] {
                    let key = (round + usize::from(row <= clause), row);
                    for _ in 0..2 {
                        queue.insert(key, &mut budget, &owner).unwrap();
                        if !queued[row] {
                            expected.insert(key);
                            queued[row] = true;
                        }
                    }
                }
            }
        }
        while let Some(key) = expected.pop_first() {
            assert_eq!(queue.pop(&mut budget, &owner), Some(Some(key)));
        }
        assert_eq!(queue.pop(&mut budget, &owner), Some(None));
    }
}

#[test]
fn sparse_successors_skip_empty_words_and_summary_levels() {
    let owner = EmissionProgress::default();
    let mut budget = 1_000_000;
    let mut queue = Queue::all(65_537, &mut budget, &owner).unwrap();
    for clause in 0..65_537 {
        assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, clause))));
    }
    queue.insert((1, 1), &mut budget, &owner).unwrap();
    queue.insert((1, 65_536), &mut budget, &owner).unwrap();
    let before = budget;
    assert_eq!(queue.pop(&mut budget, &owner), Some(Some((1, 1))));
    assert_eq!(queue.pop(&mut budget, &owner), Some(Some((1, 65_536))));
    assert_eq!(queue.pop(&mut budget, &owner), Some(None));
    assert!(before - budget < 40, "{}", before - budget);
}

fn sparse_queue() -> (Queue, u64) {
    let owner = EmissionProgress::default();
    let mut budget = 100_000;
    let mut queue = Queue::all(4097, &mut budget, &owner).unwrap();
    for clause in 0..4097 {
        assert_eq!(queue.pop(&mut budget, &owner), Some(Some((0, clause))));
    }
    queue.insert((1, 1), &mut budget, &owner).unwrap();
    queue.insert((1, 4096), &mut budget, &owner).unwrap();
    (queue, budget)
}

fn sparse_turn(queue: &mut Queue, budget: &mut u64, owner: &EmissionProgress<'_>) -> Option<()> {
    assert_eq!(queue.pop(budget, owner)?, Some((1, 1)));
    queue.insert((1, 65), budget, owner)?;
    queue.insert((1, 65), budget, owner)?;
    assert_eq!(queue.pop(budget, owner)?, Some((1, 65)));
    queue.insert((2, 0), budget, owner)?;
    assert_eq!(queue.pop(budget, owner)?, Some((1, 4096)));
    assert_eq!(queue.pop(budget, owner)?, Some((2, 0)));
    assert_eq!(queue.pop(budget, owner)?, None);
    Some(())
}

#[test]
fn summary_updates_preserve_exact_allowances_and_every_owner_refusal() {
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    let (mut queue, mut budget) = sparse_queue();
    let before = budget;
    assert_eq!(sparse_turn(&mut queue, &mut budget, &owner), Some(()));
    let used = before - budget;
    for (allowance, accepted) in [(used, true), (used - 1, false), (0, false)] {
        let (mut queue, remaining) = sparse_queue();
        assert!(allowance < remaining);
        let mut budget = allowance;
        assert_eq!(
            sparse_turn(&mut queue, &mut budget, &EmissionProgress::default()).is_some(),
            accepted
        );
        assert_eq!(budget, 0);
    }
    for stop in 1..=calls.get() {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let (mut queue, mut budget) = sparse_queue();
        assert_eq!(sparse_turn(&mut queue, &mut budget, &owner), None);
        assert!(owner.refused());
        assert_eq!(seen.get(), stop);
        let remaining = budget;
        assert_eq!(queue.pop(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn summary_update_unwinds_cannot_revive_a_partially_changed_queue() {
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    let (mut queue, mut budget) = sparse_queue();
    assert_eq!(sparse_turn(&mut queue, &mut budget, &owner), Some(()));
    for stop in [1, calls.get() / 2, calls.get()] {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            assert_ne!(seen.get(), stop, "original queue observer unwound");
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let (mut queue, mut budget) = sparse_queue();
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            sparse_turn(&mut queue, &mut budget, &owner)
        }))
        .is_err());
        assert!(owner.refused());
        let remaining = budget;
        assert_eq!(queue.pop(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop);
    }
}
