// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::theories::bv_axioms_array::fc_candidates::{
    CandidatePrefixes, Category, Counts,
};
use ay_core::Symbol;

fn array(terms: &mut TermStore, index: Sort) -> TermId {
    terms.mk_var("array", Sort::array(index, Sort::bitvec(129)))
}

fn raw_literal(terms: &mut TermStore, value: BigInt, width: u32, sort: Sort) -> TermId {
    let mut entries = terms.entries_snapshot();
    let index = TermId::new(entries.len() as u32);
    entries.push((TermData::Const(Constant::BitVec { value, width }), sort));
    *terms = TermStore::from_entries(
        entries,
        Some(terms.true_term()),
        Some(terms.false_term()),
        terms.var_counter(),
    );
    index
}

#[test]
fn literal_filter_matches_the_complete_small_domain_disequality_table() {
    for width in 1..=4 {
        let mut terms = TermStore::new();
        let array = array(&mut terms, Sort::bitvec(width));
        let indices: Vec<_> = (0..(1u32 << width))
            .map(|value| terms.mk_bitvec(BigInt::from(value), width))
            .collect();
        for (left_value, &left) in indices.iter().enumerate() {
            for (right_value, &right) in indices.iter().enumerate() {
                assert_eq!(
                    provably_distinct_literal_indices(&terms, array, left, right),
                    left_value != right_value
                );
            }
        }
    }
}

#[test]
fn wide_literal_comparison_retains_all_high_bits() {
    let mut terms = TermStore::new();
    let array = array(&mut terms, Sort::bitvec(129));
    let zero = terms.mk_bitvec(BigInt::from(0), 129);
    let high = terms.mk_bitvec(BigInt::from(1) << 128usize, 129);
    let next = terms.mk_bitvec((BigInt::from(1) << 128usize) + 1, 129);
    for (left, right) in [(zero, high), (high, zero), (high, next)] {
        assert!(provably_distinct_literal_indices(
            &terms, array, left, right
        ));
    }
    assert!(!provably_distinct_literal_indices(
        &terms, array, high, high
    ));
}

#[test]
fn noncanonical_payloads_never_establish_a_distinct_index() {
    for (raw, canonical) in [(-1, 255), (256, 0), (257, 1)] {
        let mut terms = TermStore::new();
        let array = array(&mut terms, Sort::bitvec(8));
        let right = terms.mk_bitvec(BigInt::from(canonical), 8);
        let left = raw_literal(&mut terms, BigInt::from(raw), 8, Sort::bitvec(8));
        assert_ne!(left, right);
        assert!(!provably_distinct_literal_indices(
            &terms, array, left, right
        ));
        assert!(!provably_distinct_literal_indices(
            &terms, array, right, left
        ));
    }
}

#[test]
fn malformed_or_non_bitvector_metadata_keeps_pairs_in_the_budget() {
    let cases = [
        (Sort::bitvec(8), 8, Sort::bitvec(7)),
        (Sort::bitvec(8), 7, Sort::bitvec(8)),
        (Sort::bitvec(8), 8, Sort::Bool),
        (Sort::bitvec(7), 8, Sort::bitvec(8)),
        (Sort::bitvec(0), 0, Sort::bitvec(0)),
        (Sort::Bool, 8, Sort::bitvec(8)),
        (Sort::Int, 8, Sort::bitvec(8)),
    ];
    for (index_sort, width, literal_sort) in cases {
        let mut terms = TermStore::new();
        let array = array(&mut terms, index_sort);
        let right = terms.mk_bitvec(BigInt::from(1), 8);
        let left = raw_literal(&mut terms, BigInt::from(0), width, literal_sort);
        assert!(!provably_distinct_literal_indices(
            &terms, array, left, right
        ));
        assert!(!provably_distinct_literal_indices(
            &terms, array, right, left
        ));
    }
    let mut terms = TermStore::new();
    let not_array = terms.mk_var("scalar", Sort::bitvec(8));
    let zero = terms.mk_bitvec(BigInt::from(0), 8);
    let one = terms.mk_bitvec(BigInt::from(1), 8);
    assert!(!provably_distinct_literal_indices(
        &terms, not_array, zero, one
    ));
}

#[test]
fn symbolic_and_computed_indices_preserve_existing_candidate_semantics() {
    let mut terms = TermStore::new();
    let array = array(&mut terms, Sort::bitvec(8));
    let zero = terms.mk_bitvec(BigInt::from(0), 8);
    let one = terms.mk_bitvec(BigInt::from(1), 8);
    let symbol = terms.mk_var("index", Sort::bitvec(8));
    let equal = terms.mk_app(Symbol::named("bvadd"), [zero, zero], Sort::bitvec(8));
    let unequal = terms.mk_app(Symbol::named("bvadd"), [zero, one], Sort::bitvec(8));
    for (left, right) in [
        (zero, symbol),
        (symbol, one),
        (zero, equal),
        (zero, unequal),
    ] {
        assert!(!provably_distinct_literal_indices(
            &terms, array, left, right
        ));
        assert!(!provably_distinct_literal_indices(
            &terms, array, right, left
        ));
    }
}

#[test]
fn dense_constant_pairs_leave_the_tiny_global_prefix_for_real_candidates() {
    let mut terms = TermStore::new();
    let array = array(&mut terms, Sort::bitvec(8));
    let indices: Vec<_> = (0..256)
        .map(|value| terms.mk_bitvec(BigInt::from(value), 8))
        .collect();
    let mut prefixes = CandidatePrefixes::new(1, 1, 2);
    let mut excluded = 0;
    for left in 0..indices.len() {
        for right in (left + 1)..indices.len() {
            let pair = (indices[left], indices[right]);
            if provably_distinct_literal_indices(&terms, array, pair.0, pair.1) {
                excluded += 1;
            } else {
                prefixes.observe(Category::SameBase, pair);
            }
        }
    }
    assert_eq!(excluded, 32_640);
    assert_eq!(prefixes.counts(), Counts::default());
    assert_eq!(prefixes.selected().count(), 0);

    let left = terms.mk_var("left", Sort::bitvec(8));
    let right = terms.mk_var("right", Sort::bitvec(8));
    let later = terms.mk_var("later", Sort::bitvec(8));
    let cross = (left, right);
    let same = (left, indices[0]);
    for (category, pair) in [
        (Category::CrossBase, cross),
        (Category::SameBase, same),
        (Category::CrossBase, (left, later)),
    ] {
        assert!(!provably_distinct_literal_indices(
            &terms, array, pair.0, pair.1
        ));
        prefixes.observe(category, pair);
    }
    assert_eq!(
        prefixes.selected().copied().collect::<Vec<_>>(),
        [same, cross]
    );
    assert_eq!(
        prefixes.counts(),
        Counts {
            finite: 0,
            same_base: 1,
            cross_base: 2
        }
    );
    assert_eq!(prefixes.global_skipped(), 0);
}
