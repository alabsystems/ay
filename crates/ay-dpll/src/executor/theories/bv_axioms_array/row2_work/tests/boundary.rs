// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn every_small_cap_preserves_legacy_post_add_prefix_and_new_arena_ids() {
    for factory in [fixtures::ordered, fixtures::folded] {
        let (full, complete) = compare(factory(), MAX_LATE_ARRAY_READS);
        for limit in 0..=complete.added_roots() + 1 {
            let initial = factory().roots.len();
            let (prefix, reads) = compare(factory(), limit);
            let count = limit.max(1).min(complete.added_roots());
            assert_eq!(reads.added_roots(), count);
            assert_eq!(prefix.roots, full.roots[..initial + count]);
        }
    }
}

#[test]
fn empty_and_already_known_closures_do_not_preemptively_apply_the_root_cap() {
    let (empty, reads) = compare(Fixture::empty(), 0);
    assert_eq!(reads.added_roots(), 0);
    assert!(empty.roots.is_empty());
    let (full, _) = compare(fixtures::folded(), MAX_LATE_ARRAY_READS);
    let roots = full.roots.clone();
    let (again, reads) = compare(full, 0);
    assert_eq!(reads.added_roots(), 0);
    assert_eq!(again.roots, roots);
}

#[test]
fn folded_association_limit_is_independent_of_added_root_limit_and_keeps_later_roots() {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let index_sort = Sort::bitvec(16);
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let value = terms.mk_var("value", Sort::bitvec(1));
    let write_index = terms.mk_bitvec(BigInt::from(65_535), 16);
    let base = terms.mk_const_array(index_sort.clone(), zero);
    let second_base = terms.mk_const_array(index_sort, one);
    let store = terms.mk_store(base, write_index, value);
    let second_store = terms.mk_store(second_base, write_index, value);
    let mut indices = Vec::new();
    for index in 0..=MAX_LATE_ARRAY_READS {
        let index = terms.mk_bitvec(BigInt::from(index), 16);
        indices.push(index);
        fixture.roots.push(raw_select(terms, store, index));
        fixture.probes.push((base, index));
    }
    fixture
        .roots
        .push(raw_select(terms, second_store, indices[0]));
    fixture.probes.push((second_base, indices[0]));
    let initial = fixture.roots.len();
    let (fixture, reads) = compare(fixture, 2);
    assert_eq!(reads.added_roots(), 2);
    assert_eq!(&fixture.roots[initial..], &[zero, one]);
    assert_eq!(
        reads.get(base, indices[MAX_LATE_ARRAY_READS - 1]),
        Some(zero)
    );
    assert_eq!(reads.get(base, indices[MAX_LATE_ARRAY_READS]), None);
    assert_eq!(reads.get(second_base, indices[0]), None);
}
