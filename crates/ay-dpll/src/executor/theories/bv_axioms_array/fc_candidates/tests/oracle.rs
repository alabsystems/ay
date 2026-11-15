// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::{collect, CandidatePrefixes, Category, Counts};
use std::collections::BTreeSet;

/// The old exhaustive three-vector sequence and post-category global cap.
fn exhaustive<T: Copy>(
    candidates: &[(Category, T)],
    same: usize,
    cross: usize,
    global: usize,
) -> (Vec<T>, Counts, u128, u128) {
    let mut finite_pairs = Vec::new();
    let mut same_pairs = Vec::new();
    let mut cross_pairs = Vec::new();
    for &(category, pair) in candidates {
        match category {
            Category::Finite => finite_pairs.push(pair),
            Category::SameBase => same_pairs.push(pair),
            Category::CrossBase => cross_pairs.push(pair),
        }
    }
    let counts = Counts {
        finite: finite_pairs.len() as u128,
        same_base: same_pairs.len() as u128,
        cross_base: cross_pairs.len() as u128,
    };
    let same_limit = same.min(same_pairs.len());
    let cross_limit = cross.min(cross_pairs.len());
    let mut selected = Vec::new();
    let mut skipped = 0u128;
    for &pair in finite_pairs
        .iter()
        .chain(same_pairs[..same_limit].iter())
        .chain(cross_pairs[..cross_limit].iter())
    {
        if selected.len() >= global {
            skipped += 1;
        } else {
            selected.push(pair);
        }
    }
    (selected, counts, same_limit as u128, skipped)
}

fn assert_matches_oracle(
    candidates: &[(Category, usize)],
    same: usize,
    cross: usize,
    global: usize,
) {
    let prefixes = collect(candidates, same, cross, global);
    let (selected, counts, same_limit, skipped) = exhaustive(candidates, same, cross, global);
    assert_eq!(prefixes.selected().copied().collect::<Vec<_>>(), selected);
    assert_eq!(prefixes.counts(), counts);
    assert_eq!(prefixes.same_base_limit(), same_limit);
    assert_eq!(prefixes.global_skipped(), skipped);
    assert!(prefixes.finite.len() <= global);
    assert!(prefixes.same_base.len() <= same.min(global));
    assert!(prefixes.cross_base.len() <= cross.min(global));
}

#[test]
fn exhaustive_category_orders_and_cap_boundaries_match_old_vectors() {
    let caps = [0, 1, 3, 8];
    for len in 0..=6u32 {
        for mut encoded in 0..3usize.pow(len) {
            let mut candidates = Vec::new();
            for index in 0..len as usize {
                let category = match encoded % 3 {
                    0 => Category::Finite,
                    1 => Category::SameBase,
                    _ => Category::CrossBase,
                };
                candidates.push((category, index));
                encoded /= 3;
            }
            for same in caps {
                for cross in caps {
                    for global in caps {
                        assert_matches_oracle(&candidates, same, cross, global);
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
struct Index {
    id: u8,
    constant: bool,
    base: Option<u8>,
}

fn shares_base(left: Index, right: Index) -> bool {
    left.base.zip(right.base).is_some_and(|(a, b)| a == b)
}

/// Original two scans, including the old finite-pair membership set.
fn original_pair_classes(indices: &[Index], finite: bool) -> Vec<(Category, (usize, usize))> {
    let mut classes = Vec::new();
    let mut finite_pair_seen = BTreeSet::new();
    if finite {
        for i in 0..indices.len() {
            for j in (i + 1)..indices.len() {
                if indices[i].id != indices[j].id && (indices[i].constant ^ indices[j].constant) {
                    finite_pair_seen.insert((i, j));
                    classes.push((Category::Finite, (i, j)));
                }
            }
        }
    }
    for i in 0..indices.len() {
        for j in (i + 1)..indices.len() {
            if indices[i].id == indices[j].id || finite_pair_seen.contains(&(i, j)) {
                continue;
            }
            let category = if shares_base(indices[i], indices[j]) {
                Category::SameBase
            } else {
                Category::CrossBase
            };
            classes.push((category, (i, j)));
        }
    }
    classes
}

/// Mirror the thin production classification seam over scalar index metadata.
fn bounded_pair_classes(
    indices: &[Index],
    finite: bool,
    caps: [usize; 3],
) -> CandidatePrefixes<(usize, usize)> {
    let mut prefixes = CandidatePrefixes::new(caps[0], caps[1], caps[2]);
    for i in 0..indices.len() {
        for j in (i + 1)..indices.len() {
            if indices[i].id == indices[j].id {
                continue;
            }
            let category = if finite && (indices[i].constant ^ indices[j].constant) {
                Category::Finite
            } else if shares_base(indices[i], indices[j]) {
                Category::SameBase
            } else {
                Category::CrossBase
            };
            prefixes.observe(category, (i, j));
        }
    }
    prefixes
}

fn check_index_fixture(indices: &[Index], finite: bool, caps: [usize; 3]) {
    let classes = original_pair_classes(indices, finite);
    let expected = exhaustive(&classes, caps[0], caps[1], caps[2]);
    let actual = bounded_pair_classes(indices, finite, caps);
    assert_eq!(actual.selected().copied().collect::<Vec<_>>(), expected.0);
    assert_eq!(actual.counts(), expected.1);
    assert_eq!(actual.same_base_limit(), expected.2);
    assert_eq!(actual.global_skipped(), expected.3);
}

#[test]
fn finite_xor_precedes_shared_base_and_duplicate_indices_are_absent() {
    let indices = [
        Index {
            id: 0,
            constant: true,
            base: Some(0),
        },
        Index {
            id: 1,
            constant: false,
            base: Some(0),
        },
        Index {
            id: 0,
            constant: true,
            base: Some(0),
        },
        Index {
            id: 2,
            constant: true,
            base: None,
        },
        Index {
            id: 3,
            constant: false,
            base: None,
        },
    ];
    for finite in [false, true] {
        for same in [0, 1, 20] {
            for cross in [0, 1, 20] {
                for global in [0, 1, 2, 5, 20] {
                    check_index_fixture(&indices, finite, [same, cross, global]);
                }
            }
        }
    }
    let selected = bounded_pair_classes(&indices, true, [0, 0, 1]);
    assert_eq!(selected.selected().copied().collect::<Vec<_>>(), [(0, 1)]);
    assert_eq!(
        selected.counts(),
        Counts {
            finite: 6,
            same_base: 0,
            cross_base: 3
        }
    );
}

fn random(state: &mut u64) -> u64 {
    // Fixed seed and explicit wrapping keep the oracle reproducible everywhere.
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state
}

#[test]
fn randomized_index_classes_match_old_lexicographic_pair_selection() {
    let mut state = 0x8a69_dca2_48ce_9b17u64;
    for _ in 0..2_000 {
        let len = (random(&mut state) % 29) as usize;
        let mut indices = Vec::new();
        for _ in 0..len {
            let id = (random(&mut state) % 11) as u8;
            indices.push(Index {
                id,
                constant: id < 3,
                base: (id % 4 != 0).then_some(id % 3),
            });
        }
        let caps = [
            (random(&mut state) % 17) as usize,
            (random(&mut state) % 13) as usize,
            (random(&mut state) % 41) as usize,
        ];
        for finite in [false, true] {
            check_index_fixture(&indices, finite, caps);
        }
    }
}

#[test]
fn maximum_allowances_preserve_all_small_candidates() {
    let candidates = [
        (Category::CrossBase, 0),
        (Category::Finite, 1),
        (Category::SameBase, 2),
        (Category::Finite, 3),
    ];
    assert_matches_oracle(&candidates, usize::MAX, usize::MAX, usize::MAX);
}
