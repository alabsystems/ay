// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::{CandidatePrefixes, Category, Counts};

mod oracle;
mod storage;

fn collect(
    candidates: &[(Category, usize)],
    same: usize,
    cross: usize,
    global: usize,
) -> CandidatePrefixes<usize> {
    let mut prefixes = CandidatePrefixes::new(same, cross, global);
    for &(category, value) in candidates {
        prefixes.observe(category, value);
    }
    prefixes
}

#[test]
fn category_priority_overrides_arrival_order() {
    let prefixes = collect(
        &[
            (Category::CrossBase, 0),
            (Category::SameBase, 1),
            (Category::Finite, 2),
            (Category::CrossBase, 3),
            (Category::Finite, 4),
            (Category::SameBase, 5),
        ],
        2,
        2,
        5,
    );
    assert_eq!(
        prefixes.selected().copied().collect::<Vec<_>>(),
        [2, 4, 1, 5, 0]
    );
    assert_eq!(prefixes.global_skipped(), 1);
    assert_eq!(
        prefixes.counts(),
        Counts {
            finite: 2,
            same_base: 2,
            cross_base: 2
        }
    );
}

#[test]
fn zero_global_retains_nothing_but_counts_eligible_skips() {
    let prefixes = collect(
        &[
            (Category::Finite, 0),
            (Category::SameBase, 1),
            (Category::CrossBase, 2),
        ],
        0,
        1,
        0,
    );
    assert_eq!(prefixes.selected().count(), 0);
    assert_eq!(prefixes.global_skipped(), 2);
    assert_eq!(prefixes.same_base_limit(), 0);
    assert_eq!(
        prefixes.counts(),
        Counts {
            finite: 1,
            same_base: 1,
            cross_base: 1
        }
    );
    assert_eq!(prefixes.finite.capacity(), 0);
    assert_eq!(prefixes.same_base.capacity(), 0);
    assert_eq!(prefixes.cross_base.capacity(), 0);
}

#[test]
fn finite_candidates_ignore_category_caps_but_not_global_cap() {
    let prefixes = collect(
        &[
            (Category::SameBase, 0),
            (Category::Finite, 1),
            (Category::CrossBase, 2),
            (Category::Finite, 3),
            (Category::Finite, 4),
        ],
        0,
        0,
        2,
    );
    assert_eq!(prefixes.selected().copied().collect::<Vec<_>>(), [1, 3]);
    assert_eq!(prefixes.global_skipped(), 1);
    assert_eq!(prefixes.same_base, [] as [usize; 0]);
    assert_eq!(prefixes.cross_base, [] as [usize; 0]);
}

#[test]
fn category_truncation_does_not_count_as_global_skipping() {
    let prefixes = collect(
        &[
            (Category::SameBase, 0),
            (Category::SameBase, 1),
            (Category::SameBase, 2),
            (Category::CrossBase, 3),
            (Category::CrossBase, 4),
        ],
        1,
        1,
        10,
    );
    assert_eq!(prefixes.selected().copied().collect::<Vec<_>>(), [0, 3]);
    assert_eq!(prefixes.same_base_limit(), 1);
    assert_eq!(prefixes.global_skipped(), 0);
    assert_eq!(
        prefixes.counts(),
        Counts {
            finite: 0,
            same_base: 3,
            cross_base: 2
        }
    );
}

#[test]
fn post_selection_pruning_still_consumes_global_allowance_across_arrays() {
    let budget = 3usize;
    let mut emitted = 0usize;
    let mut skipped = 0u128;
    let mut clauses = Vec::new();
    for candidates in [
        vec![(Category::SameBase, 0), (Category::SameBase, 1)],
        vec![(Category::Finite, 2), (Category::Finite, 3)],
    ] {
        let prefixes = collect(&candidates, 10, 10, budget - emitted);
        skipped += prefixes.global_skipped();
        for &pair in prefixes.selected() {
            emitted += 1;
            // Stand-in for the existing missing-bits / known-distinct pruning.
            if pair < 2 {
                continue;
            }
            clauses.push(pair);
        }
    }
    assert_eq!(emitted, 3);
    assert_eq!(skipped, 1);
    assert_eq!(clauses, [2]);
}

#[test]
fn empty_input_and_maximum_allowances_allocate_nothing() {
    let prefixes = collect(&[], usize::MAX, usize::MAX, usize::MAX);
    assert_eq!(prefixes.counts(), Counts::default());
    assert_eq!(prefixes.same_base_limit(), 0);
    assert_eq!(prefixes.global_skipped(), 0);
    assert_eq!(prefixes.selected().count(), 0);
    assert_eq!(prefixes.finite.capacity(), 0);
    assert_eq!(prefixes.same_base.capacity(), 0);
    assert_eq!(prefixes.cross_base.capacity(), 0);
}
