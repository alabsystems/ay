// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Property tests for packed AoS watched list operations (#8465, #9773).

use super::*;
use crate::literal::Variable;
use proptest::prelude::*;

#[test]
fn pack_entry_roundtrip() {
    // Blockers span the full supported 31-bit range (bit 31 is the entry
    // binary flag); clause words span the full u32 offset range with and
    // without the bit-32 clause-word flag.
    for blocker in [0u32, 1, 42, 0x7FFF_FFFE, 0x7FFF_FFFF] {
        for clause in [
            0u64,
            1,
            42,
            BINARY_FLAG,
            BINARY_FLAG | u64::from(u32::MAX),
            u64::from(u32::MAX),
        ] {
            let entry = pack_entry(blocker, clause);
            assert_eq!(entry_blocker_raw(entry), blocker);
            assert_eq!(entry_clause_raw(entry), clause);
            assert_eq!(entry_is_binary(entry), clause & BINARY_FLAG != 0);
            assert_eq!(u64::from(entry_clause_off(entry)), clause & !BINARY_FLAG);
        }
    }
}

#[test]
fn entry_with_blocker_preserves_flag_and_offset() {
    for clause in [0u64, 7, BINARY_FLAG | 5, u64::from(u32::MAX), BINARY_FLAG] {
        let entry = pack_entry(11, clause);
        let updated = entry_with_blocker(entry, 0x7FFF_FFFF);
        assert_eq!(entry_blocker_raw(updated), 0x7FFF_FFFF);
        assert_eq!(entry_clause_raw(updated), clause);
    }
}

#[test]
#[should_panic(expected = "bit 31 set")]
fn pack_entry_rejects_bit31_blocker() {
    // The packed layout stores the binary flag at bit 31 of the blocker
    // half, so a literal raw with bit 31 set (variable index >= 2^30) must
    // be rejected loudly at entry-construction time (#9773).
    let _ = pack_entry(0x8000_0000, 0);
}

#[test]
fn sort_binary_first_moves_binary_to_front() {
    let mut list = WatchList::new();
    // Add: non-binary(0), binary(1), non-binary(2), binary(3), non-binary(4)
    list.push(10, 0); // non-binary clause 0
    list.push(11, 1 | BINARY_FLAG); // binary clause 1
    list.push(12, 2); // non-binary clause 2
    list.push(13, 3 | BINARY_FLAG); // binary clause 3
    list.push(14, 4); // non-binary clause 4

    assert_eq!(list.len(), 5);
    list.sort_binary_first();
    assert_eq!(list.len(), 5);

    // First two entries should be binary (in original order)
    assert!(list.is_binary(0));
    assert_eq!(list.blocker_raw(0), 11);
    assert!(list.is_binary(1));
    assert_eq!(list.blocker_raw(1), 13);

    // Last three should be non-binary (in original order)
    assert!(!list.is_binary(2));
    assert_eq!(list.blocker_raw(2), 10);
    assert!(!list.is_binary(3));
    assert_eq!(list.blocker_raw(3), 12);
    assert!(!list.is_binary(4));
    assert_eq!(list.blocker_raw(4), 14);
}

#[test]
fn sort_binary_first_all_binary_noop() {
    let mut list = WatchList::new();
    list.push(10, BINARY_FLAG);
    list.push(11, 1 | BINARY_FLAG);
    list.sort_binary_first();
    assert_eq!(list.len(), 2);
    assert_eq!(list.blocker_raw(0), 10);
    assert_eq!(list.blocker_raw(1), 11);
}

#[test]
fn sort_binary_first_no_binary_noop() {
    let mut list = WatchList::new();
    list.push(10, 0);
    list.push(11, 1);
    list.sort_binary_first();
    assert_eq!(list.len(), 2);
    assert_eq!(list.blocker_raw(0), 10);
    assert_eq!(list.blocker_raw(1), 11);
}

#[test]
fn sort_binary_first_empty_noop() {
    let mut list = WatchList::new();
    list.sort_binary_first();
    assert_eq!(list.len(), 0);
}

#[test]
fn extend_range_from_copies_only_requested_slice() {
    let mut src = WatchList::new();
    for i in 0..8u32 {
        src.push(i + 10, u64::from(i) + 100);
    }

    let mut dst = WatchList::new();
    dst.extend_range_from(&src, 2, 6);

    assert_eq!(dst.len(), 4);
    for j in 0..dst.len() {
        assert_eq!(dst.blocker_raw(j), (j as u32) + 12);
        assert_eq!(dst.clause_raw(j), (j as u64) + 102);
    }
}

// ── remap_clause_refs tests ─────────────────────────────────────────

#[test]
fn test_remap_clause_refs_basic() {
    let mut list = WatchList::new();
    // Non-binary entry: clause offset 10, blocker 42
    list.push(42, 10);
    // Binary entry: clause offset 20, blocker 99
    list.push(99, 0x14 | BINARY_FLAG);
    // Non-binary entry: clause offset 30, blocker 7
    list.push(7, 30);

    // Build remap table: 10->100, 20->200, 30->300
    let mut remap = vec![u32::MAX; 50];
    remap[10] = 100;
    remap[20] = 200;
    remap[30] = 300;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 3);

    // First entry: non-binary, offset remapped 10->100, blocker preserved
    assert!(!list.is_binary(0));
    assert_eq!(list.clause_ref(0), ClauseRef(100));
    assert_eq!(list.blocker_raw(0), 42);

    // Second entry: binary flag preserved, offset remapped 20->200
    assert!(list.is_binary(1));
    assert_eq!(list.clause_ref(1), ClauseRef(200));
    assert_eq!(list.blocker_raw(1), 99);

    // Third entry: non-binary, offset remapped 30->300
    assert!(!list.is_binary(2));
    assert_eq!(list.clause_ref(2), ClauseRef(300));
    assert_eq!(list.blocker_raw(2), 7);
}

#[test]
fn test_remap_clause_refs_binary_preserved() {
    let mut list = WatchList::new();
    // Binary entry: clause offset 5, blocker 77
    list.push(77, 5 | BINARY_FLAG);
    // Binary entry: clause offset 15, blocker 88
    list.push(88, 15 | BINARY_FLAG);

    let mut remap = vec![u32::MAX; 20];
    remap[5] = 50;
    remap[15] = 150;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 2);
    // Binary flag must be preserved on both entries
    assert!(list.is_binary(0));
    assert_eq!(list.clause_ref(0), ClauseRef(50));
    assert!(list.is_binary(1));
    assert_eq!(list.clause_ref(1), ClauseRef(150));
}

#[test]
fn test_remap_clause_refs_deleted_dropped() {
    let mut list = WatchList::new();
    list.push(42, 10); // survives
    list.push(99, 20); // remap[20] == u32::MAX → dropped
    list.push(7, 30); // survives

    let mut remap = vec![u32::MAX; 50];
    remap[10] = 5;
    // remap[20] left as u32::MAX — deleted clause
    remap[30] = 15;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 2);
    assert_eq!(list.clause_ref(0), ClauseRef(5));
    assert_eq!(list.blocker_raw(0), 42);
    assert_eq!(list.clause_ref(1), ClauseRef(15));
    assert_eq!(list.blocker_raw(1), 7);
}

#[test]
fn test_remap_clause_refs_out_of_range_dropped() {
    let mut list = WatchList::new();
    list.push(42, 10); // survives (offset 10 < remap.len())
    list.push(99, 100); // offset 100 >= remap.len() → dropped

    let mut remap = vec![u32::MAX; 50];
    remap[10] = 5;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 1);
    assert_eq!(list.clause_ref(0), ClauseRef(5));
    assert_eq!(list.blocker_raw(0), 42);
}

#[test]
fn test_remap_clause_refs_blocker_preserved() {
    let mut list = WatchList::new();
    // Use distinct blocker values to verify they are not touched
    list.push(111, 0);
    list.push(222, 5);
    list.push(333, 0x0A | BINARY_FLAG);

    let mut remap = vec![u32::MAX; 20];
    remap[0] = 50;
    remap[5] = 55;
    remap[10] = 60;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 3);
    assert_eq!(list.blocker_raw(0), 111);
    assert_eq!(list.blocker_raw(1), 222);
    assert_eq!(list.blocker_raw(2), 333);
}

#[test]
fn test_remap_clause_refs_order_preserved() {
    let mut list = WatchList::new();
    // Interleave binary and non-binary with some deletions
    list.push(10, 0); // survives
    list.push(20, 5 | BINARY_FLAG); // deleted
    list.push(30, 10); // survives
    list.push(40, 15 | BINARY_FLAG); // survives
    list.push(50, 20); // survives

    let mut remap = vec![u32::MAX; 30];
    remap[0] = 100;
    // remap[5] = u32::MAX — deleted
    remap[10] = 110;
    remap[15] = 115;
    remap[20] = 120;

    list.remap_clause_refs(&remap);

    // 4 survivors in original order
    assert_eq!(list.len(), 4);
    assert_eq!(list.blocker_raw(0), 10);
    assert_eq!(list.blocker_raw(1), 30);
    assert_eq!(list.blocker_raw(2), 40);
    assert_eq!(list.blocker_raw(3), 50);
}

#[test]
fn test_remap_clause_refs_empty_noop() {
    let mut list = WatchList::new();
    let remap = vec![0u32; 10];

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 0);
}

#[test]
fn test_remap_clause_refs_all_deleted() {
    let mut list = WatchList::new();
    list.push(10, 0);
    list.push(20, 5 | BINARY_FLAG);
    list.push(30, 10);

    // All entries map to u32::MAX (deleted)
    let remap = vec![u32::MAX; 20];

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 0);
}

// ── shrink_capacity tests ───────────────────────────────────────────

#[test]
fn test_shrink_capacity_shrinks_oversized() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));

    // Add many entries to one watch list.
    for i in 0..100u32 {
        watches.add_watch(
            lit,
            Watcher::new(ClauseRef(i), Literal::positive(Variable(1))),
        );
    }

    let cap_before = watches.get_watches(lit).capacity();
    assert!(cap_before >= 100);

    // Clear most entries (keep only 2).
    let mut wl = watches.get_watches_mut(lit);
    wl.truncate(2);

    // capacity >> 2*len+16, so shrink should reclaim.
    watches.shrink_capacity();

    let cap_after = watches.get_watches(lit).capacity();
    assert!(
        cap_after < cap_before,
        "capacity should decrease: before={cap_before}, after={cap_after}"
    );
}

#[test]
fn test_shrink_capacity_preserves_small_lists() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));

    // Add a few entries.
    for i in 0..3u32 {
        watches.add_watch(
            lit,
            Watcher::new(ClauseRef(i), Literal::positive(Variable(1))),
        );
    }

    let len_before = watches.len_of(lit);
    watches.shrink_capacity();
    let len_after = watches.len_of(lit);

    // Entries must be preserved regardless of whether the unified buffer
    // defragments (small dead regions from doubling may trigger compaction).
    assert_eq!(len_after, len_before);
    // Verify data integrity after potential defragmentation.
    for i in 0..3 {
        assert_eq!(watches.clause_ref(lit, i), ClauseRef(i as u32));
    }
}

#[test]
fn test_shrink_capacity_defragments_at_one_eighth_dead_slots() {
    let mut watches = WatchedLists::new(4);
    let lit0 = Literal::positive(Variable(0));
    let lit1 = Literal::positive(Variable(1));
    let blocker = Literal::negative(Variable(2));

    for i in 0..16u32 {
        watches.add_watch(lit0, Watcher::new(ClauseRef(i), blocker));
        watches.add_watch(lit1, Watcher::new(ClauseRef(100 + i), blocker));
    }
    watches.defragment();
    assert_eq!(watches.dead_slots, 0);
    assert_eq!(watches.buf_entries.len(), 32);

    watches.truncate_lit(lit0, 11);
    assert_eq!(watches.dead_slots, 5);
    assert!(
        watches.dead_slots > watches.buf_entries.len() / WATCH_DEFRAG_DEAD_SLOT_DIVISOR,
        "test setup must exceed the 1/8 defrag trigger"
    );
    assert!(
        watches.dead_slots <= watches.buf_entries.len() / 4,
        "test setup must stay below the previous 1/4 trigger"
    );

    watches.shrink_capacity();

    assert_eq!(watches.dead_slots, 0);
    assert_eq!(watches.buf_entries.len(), 27);
    assert_eq!(watches.len_of(lit0), 11);
    assert_eq!(watches.len_of(lit1), 16);
    for i in 0..11 {
        assert_eq!(watches.clause_ref(lit0, i), ClauseRef(i as u32));
    }
    for i in 0..16 {
        assert_eq!(watches.clause_ref(lit1, i), ClauseRef(100 + i as u32));
    }
}

#[test]
#[cfg(feature = "raw-pointer-bcp")]
#[allow(unsafe_code)]
fn test_bcp_compaction_len_does_not_count_dead_slots() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    for i in 0..4u32 {
        watches.add_watch(lit, Watcher::new(ClauseRef(i), blocker));
    }
    watches.defragment();

    let dead_before = watches.dead_slots;
    let cap_before = watches.capacity_of(lit);

    {
        let mut view = watches.get_watches_mut(lit);
        unsafe {
            view.set_len_after_bcp_compaction(2);
        }
    }

    assert_eq!(watches.len_of(lit), 2);
    assert_eq!(watches.capacity_of(lit), cap_before);
    assert_eq!(watches.dead_slots, dead_before);

    watches.swap_remove(lit, 0);
    assert_eq!(watches.dead_slots, dead_before + 1);
}

proptest! {
    /// Adding a watch increases the count by one
    #[test]
    fn prop_add_watch_increases_count(var_idx in 0u32..10) {
        let mut watches = WatchedLists::new(10);
        let lit = Literal::positive(Variable(var_idx));
        let blocker = Literal::negative(Variable(var_idx));
        let clause_ref = ClauseRef(0);

        let before = watches.get_watches(lit).len();
        watches.add_watch(lit, Watcher::new(clause_ref, blocker));
        let after = watches.get_watches(lit).len();

        prop_assert_eq!(after, before + 1);
    }

    /// Watches are empty after initialization
    #[test]
    fn prop_watches_initially_empty(num_vars in 1usize..20, var_idx in 0u32..20) {
        prop_assume!(var_idx < num_vars as u32);
        let watches = WatchedLists::new(num_vars);
        let pos = Literal::positive(Variable(var_idx));
        let neg = Literal::negative(Variable(var_idx));

        prop_assert_eq!(watches.get_watches(pos).len(), 0);
        prop_assert_eq!(watches.get_watches(neg).len(), 0);
    }

    /// Blocker and clause are preserved when adding a watch
    #[test]
    fn prop_watcher_preserved(
        var1 in 0u32..10,
        var2 in 0u32..10,
        clause_id in 0u32..100
    ) {
        let mut watches = WatchedLists::new(10);
        let lit = Literal::positive(Variable(var1));
        let blocker = Literal::negative(Variable(var2));
        let clause_ref = ClauseRef(clause_id);

        watches.add_watch(lit, Watcher::new(clause_ref, blocker));

        let list = watches.get_watches(lit);
        prop_assert_eq!(list.len(), 1);
        prop_assert_eq!(list.clause_ref(0), clause_ref);
        prop_assert_eq!(list.blocker(0), blocker);
    }

    /// Multiple watches can be added to the same literal
    #[test]
    fn prop_multiple_watches(
        var_idx in 0u32..10,
        num_watches in 1usize..10
    ) {
        let mut watches = WatchedLists::new(10);
        let lit = Literal::positive(Variable(var_idx));

        for i in 0..num_watches {
            watches.add_watch(lit, Watcher::new(
                ClauseRef(i as u32),
                Literal::positive(Variable(0)),
            ));
        }

        prop_assert_eq!(watches.get_watches(lit).len(), num_watches);
    }

    /// Clear empties all watch lists
    #[test]
    fn prop_clear_empties_all(
        num_vars in 1usize..20,
        var_idx in 0u32..20
    ) {
        prop_assume!(var_idx < num_vars as u32);
        let mut watches = WatchedLists::new(num_vars);
        let pos = Literal::positive(Variable(var_idx));
        let neg = Literal::negative(Variable(var_idx));

        // Add some watches
        watches.add_watch(pos, Watcher::new(ClauseRef(0), neg));
        watches.add_watch(neg, Watcher::new(ClauseRef(1), pos));

        // Verify they were added
        prop_assert_eq!(watches.get_watches(pos).len(), 1);
        prop_assert_eq!(watches.get_watches(neg).len(), 1);

        // Clear and verify empty
        watches.clear();
        prop_assert_eq!(watches.get_watches(pos).len(), 0);
        prop_assert_eq!(watches.get_watches(neg).len(), 0);
    }

    /// AoS extend_from copies tail correctly
    #[test]
    fn prop_extend_from(
        n in 2usize..20,
        start in 0usize..20
    ) {
        prop_assume!(start < n);
        let mut src = WatchList::new();
        for i in 0..n {
            src.push(i as u32, (i as u64) * 10);
        }

        let mut dst = WatchList::new();
        dst.extend_from(&src, start);

        prop_assert_eq!(dst.len(), n - start);
        for j in 0..dst.len() {
            prop_assert_eq!(dst.blocker_raw(j), (start + j) as u32);
            prop_assert_eq!(dst.clause_raw(j), ((start + j) as u64) * 10);
        }
    }
}

// ── binary_count invariant tests ─────────────────────────────────────

#[test]
fn test_binary_first_maintained_on_push() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add long, binary, long, binary pattern.
    watches.add_watch(lit, Watcher::new(ClauseRef(0), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(2), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(3), blocker));

    assert_eq!(watches.len_of(lit), 4);
    // First two should be binary, last two should be long.
    assert!(watches.is_binary(lit, 0));
    assert!(watches.is_binary(lit, 1));
    assert!(!watches.is_binary(lit, 2));
    assert!(!watches.is_binary(lit, 3));

    // Verify debug assert passes.
    watches.debug_assert_binary_first();
}

#[test]
fn test_grow_and_push_preserves_binary_partition() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Fill the current region, then force a growth by inserting a binary
    // watcher. The growth path must bulk-copy the binary prefix and long
    // suffix without mixing the partitions.
    watches.add_watch(lit, Watcher::new(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(11), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(20), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(21), blocker));
    assert_eq!(watches.len_of(lit), 4);
    assert_eq!(watches.capacity_of(lit), 4);

    watches.add_watch(lit, Watcher::binary(ClauseRef(22), blocker));

    assert_eq!(watches.len_of(lit), 5);
    assert_eq!(watches.capacity_of(lit), 8);
    watches.debug_assert_binary_first();
    assert_eq!(watches.clause_ref(lit, 0), ClauseRef(20));
    assert_eq!(watches.clause_ref(lit, 1), ClauseRef(21));
    assert_eq!(watches.clause_ref(lit, 2), ClauseRef(22));
    assert_eq!(watches.clause_ref(lit, 3), ClauseRef(11));
    assert_eq!(watches.clause_ref(lit, 4), ClauseRef(10));

    // Force one more growth with a long watcher; the existing partition should
    // be copied as-is, with the new long entry appended to the suffix.
    watches.add_watch(lit, Watcher::new(ClauseRef(12), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(13), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(14), blocker));
    assert_eq!(watches.len_of(lit), 8);
    assert_eq!(watches.capacity_of(lit), 8);

    watches.add_watch(lit, Watcher::new(ClauseRef(15), blocker));

    assert_eq!(watches.len_of(lit), 9);
    assert_eq!(watches.capacity_of(lit), 16);
    watches.debug_assert_binary_first();
    assert_eq!(watches.clause_ref(lit, 0), ClauseRef(20));
    assert_eq!(watches.clause_ref(lit, 1), ClauseRef(21));
    assert_eq!(watches.clause_ref(lit, 2), ClauseRef(22));
    assert_eq!(watches.clause_ref(lit, 3), ClauseRef(11));
    assert_eq!(watches.clause_ref(lit, 4), ClauseRef(10));
    assert_eq!(watches.clause_ref(lit, 5), ClauseRef(12));
    assert_eq!(watches.clause_ref(lit, 6), ClauseRef(13));
    assert_eq!(watches.clause_ref(lit, 7), ClauseRef(14));
    assert_eq!(watches.clause_ref(lit, 8), ClauseRef(15));
}

#[test]
fn test_binary_first_maintained_on_swap_remove_binary() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add binary, binary, long, long.
    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(11), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(21), blocker));

    watches.debug_assert_binary_first();

    // Remove first binary entry.
    watches.swap_remove(lit, 0);
    assert_eq!(watches.len_of(lit), 3);
    // Should still have binary-first invariant: 1 binary, 2 long.
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(!watches.is_binary(lit, 1));
    assert!(!watches.is_binary(lit, 2));
}

#[test]
fn test_binary_first_maintained_on_swap_remove_long() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add binary, long, long.
    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(21), blocker));

    watches.debug_assert_binary_first();

    // Remove first long entry (index 1).
    watches.swap_remove(lit, 1);
    assert_eq!(watches.len_of(lit), 2);
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(!watches.is_binary(lit, 1));
}

#[test]
fn test_binary_first_maintained_on_clear() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.clear_lit(lit);
    assert_eq!(watches.len_of(lit), 0);
    watches.debug_assert_binary_first();
}

#[test]
fn test_binary_first_maintained_through_defragment() {
    let mut watches = WatchedLists::new(4);
    let lit0 = Literal::positive(Variable(0));
    let lit1 = Literal::negative(Variable(0));
    let blocker = Literal::positive(Variable(1));

    // Add entries to two literals.
    watches.add_watch(lit0, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit0, Watcher::new(ClauseRef(2), blocker));
    watches.add_watch(lit1, Watcher::binary(ClauseRef(3), blocker));
    watches.add_watch(lit1, Watcher::new(ClauseRef(4), blocker));

    watches.debug_assert_binary_first();

    // Force defragmentation.
    watches.defragment();
    watches.debug_assert_binary_first();

    // Verify data integrity.
    assert_eq!(watches.len_of(lit0), 2);
    assert_eq!(watches.len_of(lit1), 2);
    assert!(watches.is_binary(lit0, 0));
    assert!(!watches.is_binary(lit0, 1));
    assert!(watches.is_binary(lit1, 0));
    assert!(!watches.is_binary(lit1, 1));
}

#[test]
fn test_binary_first_maintained_through_remap() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add binary(10), binary(11), long(20), long(21).
    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(11), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(21), blocker));

    watches.debug_assert_binary_first();

    // Remap: delete binary(11) and long(21).
    let mut remap = vec![u32::MAX; 30];
    remap[10] = 100;
    // remap[11] = u32::MAX — deleted
    remap[20] = 200;
    // remap[21] = u32::MAX — deleted

    watches.remap_clause_refs(&remap);

    assert_eq!(watches.len_of(lit), 2);
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(!watches.is_binary(lit, 1));
}

#[test]
fn test_binary_first_maintained_through_deferred_copy_restore() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    watches.add_watch(lit, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(2), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(3), blocker));

    watches.debug_assert_binary_first();

    let mut deferred = WatchList::new();
    let (len, bc) = watches.copy_to_deferred(lit, &mut deferred);
    assert_eq!(len, 3);
    assert_eq!(bc, 2);
    assert_eq!(watches.len_of(lit), 0);
    assert_eq!(deferred.len(), 3);

    watches.restore_from_deferred(lit, &mut deferred);
    assert_eq!(watches.len_of(lit), 3);
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(watches.is_binary(lit, 1));
    assert!(!watches.is_binary(lit, 2));
}

#[test]
fn test_restore_from_deferred_counts_compacted_binary_prefix() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    watches.add_watch(lit, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(2), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(11), blocker));

    let mut deferred = WatchList::new();
    let (len, bc) = watches.copy_to_deferred(lit, &mut deferred);
    assert_eq!(len, 4);
    assert_eq!(bc, 2);

    // Stable compaction that drops one binary and one long entry must leave a
    // shorter binary prefix followed by a long suffix.
    deferred.set_entry(0, deferred.blocker_raw(0), deferred.clause_raw(0));
    deferred.set_entry(1, deferred.blocker_raw(3), deferred.clause_raw(3));
    deferred.truncate(2);

    watches.restore_from_deferred(lit, &mut deferred);

    assert_eq!(watches.len_of(lit), 2);
    assert_eq!(watches.meta[lit.index()].binary_count, 1);
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(!watches.is_binary(lit, 1));
    assert_eq!(watches.clause_ref(lit, 0), ClauseRef(1));
    assert_eq!(watches.clause_ref(lit, 1), ClauseRef(11));
}

#[test]
fn test_restore_from_deferred_overflow_preserves_binary_and_long_partitions() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    watches.add_watch(lit, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(2), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(11), blocker));
    assert_eq!(watches.capacity_of(lit), 4);

    let mut deferred = WatchList::new();
    let (len, bc) = watches.copy_to_deferred(lit, &mut deferred);
    assert_eq!(len, 4);
    assert_eq!(bc, 2);

    // Simulate HBR overflow targeting the same literal while its original
    // watchers live in the deferred buffer. Binary inserts maintain a prefix
    // but can move the first long overflow watcher to the suffix tail.
    watches.add_watch(lit, Watcher::new(ClauseRef(30), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(40), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(31), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(41), blocker));
    assert_eq!(watches.meta[lit.index()].binary_count, 2);
    watches.debug_assert_binary_first();

    watches.restore_from_deferred(lit, &mut deferred);

    assert_eq!(watches.len_of(lit), 8);
    assert_eq!(watches.meta[lit.index()].binary_count, 4);
    watches.debug_assert_binary_first();

    let expected = [
        ClauseRef(1),
        ClauseRef(2),
        ClauseRef(40),
        ClauseRef(41),
        ClauseRef(10),
        ClauseRef(11),
        ClauseRef(31),
        ClauseRef(30),
    ];
    for (i, &clause_ref) in expected.iter().enumerate() {
        assert_eq!(watches.clause_ref(lit, i), clause_ref);
        assert_eq!(watches.is_binary(lit, i), i < 4);
    }
}

// ── shrink_watch_lists tests (#8031) ────────────────────────────────

#[test]
fn test_shrink_watch_lists_reduces_overprovisioned() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add many entries to grow capacity.
    for i in 0..64u32 {
        watches.add_watch(lit, Watcher::new(ClauseRef(i), blocker));
    }

    let cap_before = watches.capacity_of(lit);
    assert!(cap_before >= 64);

    // Remove most entries (keep only 4).
    watches.truncate_lit(lit, 4);
    assert_eq!(watches.len_of(lit), 4);

    // len=4, capacity>=64 => len < capacity/2, so shrink should fire.
    let shrunk = watches.shrink_watch_lists();
    assert!(
        shrunk > 0,
        "expected at least one list to be shrunk, got {shrunk}"
    );

    // After shrinking + defragmentation, capacity should be much smaller.
    let cap_after = watches.capacity_of(lit);
    assert!(
        cap_after < cap_before,
        "capacity should decrease: before={cap_before}, after={cap_after}"
    );

    // Data integrity: all 4 remaining entries should be readable.
    for i in 0..4 {
        assert_eq!(watches.clause_ref(lit, i), ClauseRef(i as u32));
    }
}

#[test]
fn test_shrink_watch_lists_skips_small_lists() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add 2 entries (capacity will be small, likely 2-4).
    watches.add_watch(lit, Watcher::new(ClauseRef(0), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(1), blocker));

    // Small lists (capacity < 4) should not be touched.
    let shrunk = watches.shrink_watch_lists();
    assert_eq!(shrunk, 0, "small lists should not be shrunk");
}

#[test]
fn test_shrink_watch_lists_preserves_binary_first() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Build up a large list with mixed binary/long entries.
    for i in 0..32u32 {
        if i % 3 == 0 {
            watches.add_watch(lit, Watcher::binary(ClauseRef(i), blocker));
        } else {
            watches.add_watch(lit, Watcher::new(ClauseRef(i), blocker));
        }
    }

    // Truncate to a few entries.
    watches.truncate_lit(lit, 6);

    watches.shrink_watch_lists();

    // Binary-first invariant must hold after shrink + defragment.
    watches.debug_assert_binary_first();
    assert_eq!(watches.len_of(lit), 6);
}

#[test]
fn test_shrink_watch_lists_no_op_when_balanced() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add exactly enough to fill capacity without over-provisioning.
    for i in 0..8u32 {
        watches.add_watch(lit, Watcher::new(ClauseRef(i), blocker));
    }

    // len==8, capacity likely 8 after growth. len >= capacity/2, so no shrink.
    let shrunk = watches.shrink_watch_lists();
    assert_eq!(shrunk, 0);
}

proptest! {
    /// Binary-first invariant maintained through arbitrary insert sequences.
    #[test]
    fn prop_binary_first_invariant_on_mixed_insert(
        num_binary in 0usize..10,
        num_long in 0usize..10,
        interleave_seed in 0u64..1000
    ) {
        let mut watches = WatchedLists::new(4);
        let lit = Literal::positive(Variable(0));
        let blocker = Literal::negative(Variable(1));

        // Interleave binary and long inserts pseudo-randomly.
        let mut b_remaining = num_binary;
        let mut l_remaining = num_long;
        let mut seed = interleave_seed;
        let mut clause_id = 0u32;
        while b_remaining > 0 || l_remaining > 0 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let pick_binary = if b_remaining == 0 {
                false
            } else if l_remaining == 0 {
                true
            } else {
                seed % 2 == 0
            };
            if pick_binary {
                watches.add_watch(lit, Watcher::binary(ClauseRef(clause_id), blocker));
                b_remaining -= 1;
            } else {
                watches.add_watch(lit, Watcher::new(ClauseRef(clause_id), blocker));
                l_remaining -= 1;
            }
            clause_id += 1;
        }

        prop_assert_eq!(watches.len_of(lit), num_binary + num_long);
        // Verify invariant.
        watches.debug_assert_binary_first();
        // Count binaries.
        let mut bc = 0;
        for i in 0..watches.len_of(lit) {
            if watches.is_binary(lit, i) {
                bc += 1;
            }
        }
        prop_assert_eq!(bc, num_binary);
    }
}

// ── #9670: clause-arena overflow regression (binary flag no longer aliases
//    the clause word offset) ──────────────────────────────────────────────

/// Boundary clause word offsets that the OLD `u32`-flag scheme could not encode
/// without corruption. Under the old design any offset `>= 2^31` aliased the
/// high-bit binary flag, so a long clause at such an offset was misread as
/// binary, corrupting BCP and producing spurious UNSAT. The flag now lives at
/// bit 32 of a `u64` clause word, so every `u32` offset (right up to the
/// `u32::MAX` dead-sentinel reservation) is encoded losslessly for BOTH binary
/// and long clauses.
const BOUNDARY_OFFSETS: [u32; 8] = [
    0,
    1,
    0x4000_0000, // mid-range
    0x7FFF_FFFE, // just below the old 2^31 limit
    0x7FFF_FFFF, // old MAX_ARENA_WORDS - 1
    0x8000_0000, // == old BINARY_FLAG: the first offset that aliased
    0x8000_0001, // just past the old limit
    0xFFFF_FFFE, // largest representable live clause word offset
];

#[test]
fn clauseref_encoding_roundtrips_across_old_2pow31_boundary() {
    // The binary flag must occupy a bit strictly above every u32 offset, so a
    // long-clause word equals its offset exactly and a binary-clause word is
    // offset | flag with the flag recoverable.
    assert_eq!(BINARY_FLAG, 1u64 << 32);
    assert_eq!(
        BINARY_FLAG - 1,
        u64::from(u32::MAX),
        "flag must sit immediately above the 32-bit offset range",
    );
    for off in BOUNDARY_OFFSETS {
        let cref = ClauseRef::new(off);

        // Long watcher: clause word == offset, no flag bit, decodes back.
        let long = Watcher::new(cref, Literal::positive(Variable(7)));
        assert_eq!(
            long.clause_raw & BINARY_FLAG,
            0,
            "long watcher at offset {off:#x} must not set the binary flag",
        );
        assert_eq!(
            (long.clause_raw & !BINARY_FLAG) as u32,
            off,
            "long watcher offset must round-trip at {off:#x}",
        );
        assert_eq!(long.clause_raw as u32, off, "long path `as u32` lossless");

        // Binary watcher: same offset, flag set, decodes back.
        let bin = Watcher::binary(cref, Literal::positive(Variable(7)));
        assert_ne!(
            bin.clause_raw & BINARY_FLAG,
            0,
            "binary watcher at offset {off:#x} must set the binary flag",
        );
        assert_eq!(
            (bin.clause_raw & !BINARY_FLAG) as u32,
            off,
            "binary watcher offset must round-trip at {off:#x}",
        );

        // The two encodings differ only by the flag bit — proving that a long
        // clause at a boundary offset can never be mistaken for binary (the old
        // bug) and vice-versa.
        assert_eq!(bin.clause_raw, long.clause_raw | BINARY_FLAG);
        assert_ne!(bin.clause_raw, long.clause_raw);
    }
}

#[test]
fn watch_dispatch_distinguishes_binary_and_long_at_boundary_offsets() {
    // Build a watch list whose entries reference clauses at offsets that the old
    // scheme could not represent, mixing binary and long watchers, then confirm
    // `is_binary` / `clause_ref` dispatch correctly for every entry.
    let mut watches = WatchedLists::new(2);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(0));

    // Push an alternating binary/long sequence at boundary offsets. The
    // binary-first invariant reorders them, so we verify by clause ref, not
    // position.
    let mut expected_binary: Vec<u32> = Vec::new();
    let mut expected_long: Vec<u32> = Vec::new();
    for (k, off) in BOUNDARY_OFFSETS.into_iter().enumerate() {
        let cref = ClauseRef::new(off);
        if k % 2 == 0 {
            watches.add_watch(lit, Watcher::binary(cref, blocker));
            expected_binary.push(off);
        } else {
            watches.add_watch(lit, Watcher::new(cref, blocker));
            expected_long.push(off);
        }
    }

    watches.debug_assert_binary_first();
    assert_eq!(watches.len_of(lit), BOUNDARY_OFFSETS.len());

    let mut got_binary: Vec<u32> = Vec::new();
    let mut got_long: Vec<u32> = Vec::new();
    for i in 0..watches.len_of(lit) {
        let off = watches.clause_ref(lit, i).id();
        if watches.is_binary(lit, i) {
            // A binary dispatch at a boundary offset is exactly what the old
            // scheme got WRONG for long clauses >= 2^31.
            got_binary.push(off);
        } else {
            got_long.push(off);
        }
    }
    got_binary.sort_unstable();
    got_long.sort_unstable();
    expected_binary.sort_unstable();
    expected_long.sort_unstable();
    assert_eq!(got_binary, expected_binary, "binary watchers misdispatched");
    assert_eq!(got_long, expected_long, "long watchers misdispatched");
}

#[test]
fn remap_preserves_binary_long_distinction_at_boundary_offsets() {
    // The clause-relocation remap (arena GC) must keep a long clause long and a
    // binary clause binary even when the NEW offset lands above the old 2^31
    // boundary. Construct a standalone list and remap two clauses to boundary
    // offsets, one binary and one long.
    let mut list = WatchList::new();
    // clause 0 -> long, clause 1 -> binary (originals at small offsets).
    list.push(10, 0); // long, old offset 0
    list.push(11, 1 | BINARY_FLAG); // binary, old offset 1
    list.sort_binary_first();

    // remap[old] = new. Send long clause 0 to 0x8000_0005 (past old limit) and
    // binary clause 1 to 0xFFFF_FFFE (largest live offset).
    let remap = vec![0x8000_0005u32, 0xFFFF_FFFEu32];
    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 2);
    let mut seen_long = false;
    let mut seen_binary = false;
    for i in 0..list.len() {
        let off = list.clause_ref(i).id();
        if list.is_binary(i) {
            assert_eq!(off, 0xFFFF_FFFE, "binary clause must remap to its offset");
            seen_binary = true;
        } else {
            assert_eq!(off, 0x8000_0005, "long clause must remap to its offset");
            seen_long = true;
        }
    }
    assert!(seen_long && seen_binary, "both clauses must survive remap");
}
