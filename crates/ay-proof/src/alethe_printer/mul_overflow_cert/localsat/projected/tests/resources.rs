// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn attempt(budget: &mut u64, owner: &EmissionProgress<'_>) -> Option<HashSet<Vec<bool>>> {
    let db = vec![vec![(1, true), (2, true)]];
    let fixed = Model::from_iter([(3, false)]);
    project(&db, &fixed, &[1, 2, 3, 2], budget, owner)
}

#[test]
fn exact_quota_and_every_smaller_cut_keep_the_same_cumulative_allowance() {
    let owner = EmissionProgress::default();
    let mut remaining = 100_000;
    let expected = attempt(&mut remaining, &owner).unwrap();
    assert_eq!(expected.len(), 3);
    let cost = 100_000 - remaining;
    assert!(cost > 0);
    let mut exact = cost;
    assert_eq!(attempt(&mut exact, &owner), Some(expected));
    assert_eq!(exact, 0);
    for allowance in 0..cost {
        let mut remaining = allowance;
        assert_eq!(
            attempt(&mut remaining, &owner),
            None,
            "allowance={allowance}"
        );
        assert_eq!(remaining, 0);
        assert_eq!(attempt(&mut remaining, &owner), None);
    }
    let mut shared = 2 * cost - 1;
    assert!(attempt(&mut shared, &owner).is_some());
    assert_eq!(attempt(&mut shared, &owner), None);
    assert_eq!(shared, 0);
}

fn observations() -> usize {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(attempt(&mut 100_000, &EmissionProgress::with_caller(&mut callback)).is_some());
    calls.get()
}

#[test]
fn every_original_owner_poll_refuses_without_partial_states_or_retry() {
    for stop in 1..=observations() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let nested = owner.clone();
        let mut remaining = 100_000;
        assert_eq!(attempt(&mut remaining, &nested), None, "poll={stop}");
        assert!(owner.refused());
        let retained = remaining;
        assert_eq!(attempt(&mut remaining, &owner), None);
        assert_eq!(remaining, retained);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn every_observer_unwind_retires_the_tree_and_poison_is_shared() {
    for stop in 1..=observations() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            assert_ne!(seen.get(), stop, "original enumeration observer unwound");
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut remaining = 100_000;
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                attempt(&mut remaining, &owner)
            }))
            .is_err(),
            "poll={stop}"
        );
        assert!(owner.refused());
        let retained = remaining;
        assert_eq!(attempt(&mut remaining, &owner.clone()), None);
        assert_eq!(remaining, retained);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn late_refusal_cannot_publish_a_completed_reachable_set() {
    let calls = observations();
    let seen = Cell::new(0usize);
    let mut callback = || {
        seen.set(seen.get() + 1);
        seen.get() < calls
    };
    let owner = EmissionProgress::with_caller(&mut callback);
    assert_eq!(attempt(&mut 100_000, &owner), None);
    assert!(owner.refused());
    assert_eq!(seen.get(), calls);
}

#[test]
fn absent_projected_values_are_not_filled_with_false() {
    let owner = EmissionProgress::default();
    let mut found = HashSet::default();
    assert_eq!(
        record(&mut found, &Model::default(), &[1], &mut 100_000, &owner),
        None
    );
    assert!(found.is_empty());
}
