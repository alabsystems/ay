// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::{CandidatePrefixes, Category, Counts};

#[test]
fn million_candidate_stream_retains_only_three_budgeted_prefixes() {
    let mut prefixes = CandidatePrefixes::new(17, 11, 7);
    for pair in 0..1_000_000usize {
        let category = match pair % 3 {
            0 => Category::Finite,
            1 => Category::SameBase,
            _ => Category::CrossBase,
        };
        prefixes.observe(category, pair);
    }
    assert_eq!(prefixes.finite.len(), 7);
    assert_eq!(prefixes.same_base.len(), 7);
    assert_eq!(prefixes.cross_base.len(), 7);
    assert_eq!(
        prefixes.counts(),
        Counts {
            finite: 333_334,
            same_base: 333_333,
            cross_base: 333_333,
        }
    );
    assert_eq!(prefixes.global_skipped(), 333_355);
    assert_eq!(
        prefixes.selected().copied().collect::<Vec<_>>(),
        [0, 3, 6, 9, 12, 15, 18]
    );
}

#[test]
fn per_category_limits_bound_retention_even_with_larger_global_allowance() {
    let mut prefixes = CandidatePrefixes::new(2, 0, 31);
    for pair in 0..10_000usize {
        prefixes.observe(Category::SameBase, pair);
        prefixes.observe(Category::CrossBase, pair);
    }
    assert_eq!(prefixes.finite.len(), 0);
    assert_eq!(prefixes.same_base.len(), 2);
    assert_eq!(prefixes.cross_base.len(), 0);
    assert_eq!(prefixes.cross_base.capacity(), 0);
    assert_eq!(prefixes.selected().copied().collect::<Vec<_>>(), [0, 1]);
    assert_eq!(prefixes.global_skipped(), 0);
    assert_eq!(prefixes.counts().same_base, 10_000);
    assert_eq!(prefixes.counts().cross_base, 10_000);
}

#[test]
fn counted_prefixes_do_not_clone_retained_or_discarded_values() {
    use std::cell::Cell;

    struct NoClone<'a>(&'a Cell<usize>);
    impl Drop for NoClone<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let drops = Cell::new(0);
    let mut prefixes = CandidatePrefixes::new(3, 0, 2);
    for _ in 0..100 {
        prefixes.observe(Category::SameBase, NoClone(&drops));
    }
    assert_eq!(drops.get(), 98);
    assert_eq!(prefixes.selected().count(), 2);
    assert_eq!(prefixes.global_skipped(), 1);
    drop(prefixes);
    assert_eq!(drops.get(), 100);
}

#[test]
fn diagnostic_counts_are_not_truncated_to_pointer_width() {
    // Seed only counters to exercise arithmetic beyond a narrow target's usize
    // without allocating or iterating a pointer-width-sized candidate stream.
    let mut prefixes = CandidatePrefixes::<usize>::new(2, 3, 7);
    let wide = (usize::MAX as u128) + 1;
    prefixes.counts = Counts {
        finite: wide,
        same_base: wide,
        cross_base: wide,
    };
    assert_eq!(prefixes.same_base_limit(), 2);
    assert_eq!(prefixes.global_skipped(), wide - 2);
}
