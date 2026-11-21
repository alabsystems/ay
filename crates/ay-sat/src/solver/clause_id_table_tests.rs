// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The table answers exactly what the old one-entry-per-word vector answered
/// for every offset, on a layout of clause starts at least `STRIDE` apart.
#[test]
fn clause_id_table_matches_per_word_vector() {
    // Clause starts as an arena lays them out: header (3) + literals.
    let lens = [2usize, 3, 1, 7, 2, 2, 5, 1, 1, 4];
    let mut starts = Vec::new();
    let mut offset = 0;
    for len in lens {
        starts.push(offset);
        offset += HEADER_WORDS + len;
    }
    let mut table = ClauseIdTable::new();
    let mut reference: Vec<u64> = Vec::new();
    for (i, &start) in starts.iter().enumerate() {
        table.grow_to(start + 1);
        if start >= reference.len() {
            reference.resize(start + 1, 0);
        }
        let id = 100 + i as u64;
        table.set(start, id);
        reference[start] = id;
    }
    assert_eq!(table.len(), reference.len());
    for word in 0..reference.len() + 4 {
        assert_eq!(
            table.get(word).copied(),
            reference.get(word).copied(),
            "offset {word}"
        );
    }
    let recorded: Vec<(usize, u64)> = table.iter_recorded().collect();
    let expected: Vec<(usize, u64)> = reference
        .iter()
        .enumerate()
        .filter(|&(_, &id)| id != 0)
        .map(|(offset, &id)| (offset, id))
        .collect();
    assert_eq!(recorded, expected);
    assert!(table.contains(&105));
    assert!(!table.contains(&99));
}

/// A non-start offset never reads another clause's id, and cannot update it.
#[test]
fn clause_id_table_non_owner_reads_zero() {
    let mut table = ClauseIdTable::with_len(9);
    table.set(4, 7);
    // 3 and 5 share slot 1 with 4.
    assert_eq!(table[4], 7);
    assert_eq!(table[3], 0);
    assert_eq!(table[5], 0);
    assert!(table.get_mut(5).is_none());
    assert_eq!(table.get_mut(4).map(std::mem::take), Some(7));
    assert_eq!(table[4], 0);
    assert_eq!(table.get(9), None);
}

/// The table holds about 3 bytes per arena word where the vector held 8.
#[test]
fn clause_id_table_is_smaller_than_per_word_vector() {
    let words = 3_000_000;
    let mut table = ClauseIdTable::new();
    table.reserve_exact_len(words);
    table.grow_to(words);
    let vector_bytes = words * size_of::<u64>();
    assert!(table.heap_bytes() * 2 < vector_bytes);
    assert_eq!(table.heap_bytes(), ClauseIdTable::bytes_for_len(words));
}

#[test]
#[should_panic(expected = "past table length")]
fn clause_id_table_index_past_len_panics() {
    let table = ClauseIdTable::with_len(3);
    let _id: u64 = table[3];
}

#[test]
fn clause_id_table_clear_keeps_nothing() {
    let mut table = ClauseIdTable::with_len(30);
    table.set(6, 1);
    table.clear();
    assert!(table.is_empty());
    assert_eq!(table.get(6), None);
    table.grow_to(7);
    assert_eq!(table[6], 0);
}

/// A write at an offset sharing a slot with a clause start that still holds
/// an id would erase that id: it is a `BUG` panic, not a silent loss.
#[test]
#[should_panic(expected = "would erase id 7 of clause start 4")]
fn clause_id_table_set_refuses_to_erase_a_live_id() {
    let mut table = ClauseIdTable::with_len(9);
    table.set(4, 7);
    table.set(5, 8);
}

/// A slot whose owner holds 0 (a rolled-back rung, a deleted clause's id
/// taken) may change owner; the old owner then reads 0, as before.
#[test]
fn clause_id_table_set_takes_a_slot_whose_owner_holds_zero() {
    let mut table = ClauseIdTable::with_len(9);
    table.set(4, 7);
    assert_eq!(table.get_mut(4).map(std::mem::take), Some(7));
    table.set(3, 11);
    assert_eq!(table[3], 11);
    assert_eq!(table[4], 0);
    // Rewriting the owner's own id is always allowed.
    table.set(3, 12);
    assert_eq!(table[3], 12);
}

/// Equality and `starts_with` compare what every offset reads, as the
/// per-word vector did: an owned slot holding 0 equals an unowned one.
#[test]
fn clause_id_table_equality_and_starts_with_compare_reads() {
    let mut owned_zero = ClauseIdTable::with_len(9);
    owned_zero.set(4, 0);
    let unowned = ClauseIdTable::with_len(9);
    assert_eq!(owned_zero, unowned);

    let mut prefix = ClauseIdTable::with_len(6);
    prefix.set(0, 1);
    prefix.set(3, 2);
    let mut longer = prefix.clone();
    longer.grow_to(12);
    longer.set(9, 3);
    assert!(longer.starts_with(&prefix));
    assert_ne!(longer, prefix);
    longer.set(3, 5);
    assert!(!longer.starts_with(&prefix));
    assert!(!prefix.starts_with(&longer));
}
