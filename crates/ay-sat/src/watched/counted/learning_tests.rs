// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::counted_storage::test_owner;
use crate::literal::Variable;

fn lit(i: u32) -> Literal {
    Literal::positive(Variable(i))
}
fn fixture(count: usize) -> WatchedLists {
    let mut lists = WatchedLists::new(4);
    for i in 0..count {
        lists.watch_clause(ClauseRef(i as u32), lit(1), lit(0), i % 3 == 0);
    }
    lists.buf_entries.shrink_to_fit();
    lists
}
fn metadata(s: &WatchedLists) -> Vec<(u32, u32, u32, u32)> {
    s.meta
        .iter()
        .map(|m| (m.offset, m.len, m.capacity, m.binary_count))
        .collect()
}

#[test]
fn learned_pair_reservation_preserves_binary_growth_shift_and_fast_rotation_exactly() {
    for count in 0..12 {
        for binary in [false, true] {
            let mut actual = fixture(count);
            let mut expected = fixture(count);
            let before_meta = metadata(&actual);
            let before_words = actual.buf_entries.clone();
            actual
                .reserve_counted_learned_pair(lit(1), lit(0), &test_owner(1_000_000, 1_000_000))
                .unwrap();
            assert_eq!(
                metadata(&actual),
                before_meta,
                "reservation may not force the fast path"
            );
            assert_eq!(actual.buf_entries, before_words);
            actual.watch_clause(ClauseRef(77), lit(1), lit(0), binary);
            expected.watch_clause(ClauseRef(77), lit(1), lit(0), binary);
            assert_eq!(metadata(&actual), metadata(&expected));
            assert_eq!(actual.buf_entries, expected.buf_entries);
            assert_eq!(
                actual.buf_entries.capacity(),
                expected.buf_entries.capacity()
            );
            assert_eq!(actual.dead_slots, expected.dead_slots);
        }
    }
}

#[test]
fn every_watch_pair_work_and_storage_cut_retains_exact_logical_layout() {
    let mut base = fixture(4);
    let owner = test_owner(1_000_000, 1_000_000);
    base.reserve_counted_learned_pair(lit(1), lit(0), &owner)
        .unwrap();
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 16 && used.storage_admitted > 0);
    for (work, storage) in (0..used.work_admitted)
        .map(|w| (w, 1_000_000))
        .chain((0..used.storage_admitted).map(|s| (1_000_000, s)))
    {
        let mut actual = fixture(4);
        let before_meta = metadata(&actual);
        let before_words = actual.buf_entries.clone();
        let owner = test_owner(work, storage);
        assert!(actual
            .reserve_counted_learned_pair(lit(1), lit(0), &owner)
            .is_err());
        assert_eq!(metadata(&actual), before_meta);
        assert_eq!(actual.buf_entries, before_words);
    }
}
