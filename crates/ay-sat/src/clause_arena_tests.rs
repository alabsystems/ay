// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `ClauseArena` unified inline-literal clause storage.

use super::*;
use crate::clause::{
    clause_signature_may_subsume, clause_signatures_may_resolve_tautologically,
    compute_clause_signature,
};

/// Test helper: create a Literal from a signed integer.
fn lit(v: i32) -> Literal {
    if v > 0 {
        Literal::positive(crate::literal::Variable(v as u32 - 1))
    } else {
        Literal::negative(crate::literal::Variable((-v) as u32 - 1))
    }
}

fn assert_clause_counters(
    arena: &ClauseArena,
    active: usize,
    irredundant: usize,
    redundant: usize,
) {
    let scanned_active = arena.active_indices().count();
    let scanned_irredundant = arena
        .active_indices()
        .filter(|&idx| !arena.is_learned(idx))
        .count();
    assert_eq!(arena.active_clause_count(), active);
    assert_eq!(arena.irredundant_count(), irredundant);
    assert_eq!(arena.redundant_count, redundant);
    assert_eq!(scanned_active, active);
    assert_eq!(scanned_irredundant, irredundant);
    assert_eq!(scanned_active, scanned_irredundant + redundant);
}

#[test]
fn test_header_word_count() {
    assert_eq!(HEADER_WORDS, 3);
}

#[test]
fn test_add_and_access() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2), lit(3)], false);
    let off1 = arena.add(&[lit(-1), lit(4)], true);

    assert_eq!(off0, 0);
    assert_eq!(off1, 6); // 3 header + 3 lits = 6 words
    assert_eq!(arena.num_clauses(), 2);

    assert_eq!(arena.literal(off0, 0), lit(1));
    assert_eq!(arena.literal(off0, 1), lit(2));
    assert_eq!(arena.literal(off0, 2), lit(3));
    assert_eq!(arena.literal(off1, 0), lit(-1));
    assert_eq!(arena.literal(off1, 1), lit(4));

    assert_eq!(arena.len_of(off0), 3);
    assert_eq!(arena.len_of(off1), 2);

    assert!(!arena.is_learned(off0));
    assert!(arena.is_learned(off1));
}

#[test]
fn test_watched_literals() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    let (w0, w1) = arena.watched_literals(off);
    assert_eq!(w0, lit(1));
    assert_eq!(w1, lit(2));
}

#[test]
fn test_swap_literals() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    arena.swap_literals(off, 0, 2);
    assert_eq!(arena.literal(off, 0), lit(3));
    assert_eq!(arena.literal(off, 1), lit(2));
    assert_eq!(arena.literal(off, 2), lit(1));
}

#[test]
fn test_lbd() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2)], true);
    assert_eq!(arena.lbd(off), 0);
    arena.set_lbd(off, 5);
    assert_eq!(arena.lbd(off), 5);
    assert_eq!(arena.len_of(off), 2); // lit_len preserved
    arena.set_lbd(off, 70000);
    assert_eq!(arena.lbd(off), u32::from(u16::MAX));
}

#[test]
fn test_signature() {
    let mut arena = ClauseArena::new();
    let lits = [lit(1), lit(-2), lit(3)];
    let off = arena.add(&lits, false);
    assert_eq!(arena.signature(off), compute_clause_signature(&lits));

    let new_lits = [lit(-1), lit(4)];
    arena.replace(off, &new_lits);
    assert_eq!(arena.signature(off), compute_clause_signature(&new_lits));
}

#[test]
fn test_signature_polarity_overlap_filter() {
    let pos = compute_clause_signature(&[lit(1), lit(2)]);
    let same_polarity = compute_clause_signature(&[lit(1), lit(3)]);
    let opposite_polarity = compute_clause_signature(&[lit(-1), lit(4)]);

    assert!(
        !clause_signatures_may_resolve_tautologically(pos, same_polarity),
        "same-polarity shared variables must not look tautological"
    );
    assert!(
        clause_signatures_may_resolve_tautologically(pos, opposite_polarity),
        "opposite-polarity shared variables should trigger the filter"
    );
}

#[test]
fn test_signature_subsumption_filter() {
    let subsuming = compute_clause_signature(&[lit(1), lit(-2)]);
    let subsumed = compute_clause_signature(&[lit(1), lit(-2), lit(3)]);
    let incompatible = compute_clause_signature(&[lit(1), lit(3)]);

    assert!(
        clause_signature_may_subsume(subsuming, subsumed),
        "matching literal bits should pass the subsumption prefilter"
    );
    assert!(
        !clause_signature_may_subsume(subsuming, incompatible),
        "missing literal bits must fail the subsumption prefilter"
    );
}

#[test]
fn test_activity() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2)], false);
    assert_eq!(arena.activity(off), 0.0);
    arena.set_activity(off, 1.5);
    assert!((arena.activity(off) - 1.5).abs() < f32::EPSILON);
}

#[test]
fn test_saved_pos() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3), lit(4)], false);
    assert_eq!(arena.saved_pos(off), 2);
    arena.set_saved_pos(off, 5);
    assert_eq!(arena.saved_pos(off), 5);
    assert!(!arena.is_learned(off)); // flags preserved
}

#[test]
fn test_flags_independence() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2)], true);

    assert!(arena.is_learned(off));
    assert_eq!(arena.used(off), 0);
    assert!(!arena.is_garbage(off));
    assert!(!arena.is_vivify_skipped(off));
    assert!(!arena.is_pending_garbage(off));

    arena.set_used(off, 20);
    assert_eq!(arena.used(off), 20);
    assert!(arena.is_learned(off));

    arena.set_garbage(off, true);
    assert!(arena.is_garbage(off));
    assert!(arena.is_learned(off));
    assert_eq!(arena.used(off), 20);

    arena.set_vivify_skip(off, true);
    assert!(arena.is_vivify_skipped(off));
    assert!(arena.is_garbage(off));

    arena.set_pending_garbage(off, true);
    assert!(arena.is_pending_garbage(off));
    assert!(arena.is_vivify_skipped(off));

    // Clear all
    arena.set_garbage(off, false);
    assert!(!arena.is_garbage(off));
    arena.set_vivify_skip(off, false);
    assert!(!arena.is_vivify_skipped(off));
    arena.set_pending_garbage(off, false);
    assert!(!arena.is_pending_garbage(off));
    assert_eq!(arena.saved_pos(off), 2);
}

#[test]
fn test_used_counter() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2)], true);

    arena.set_used(off, 15);
    assert_eq!(arena.used(off), 15);
    arena.set_used(off, MAX_USED);
    assert_eq!(arena.used(off), 31);
    arena.set_used(off, 255); // clamped
    assert_eq!(arena.used(off), 31);
    arena.decay_used(off);
    assert_eq!(arena.used(off), 30);
    arena.set_used(off, 0);
    arena.decay_used(off);
    assert_eq!(arena.used(off), 0); // saturates at 0
}

#[test]
fn test_set_learned() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2)], false);
    assert!(!arena.is_learned(off));
    arena.set_learned(off, true);
    assert!(arena.is_learned(off));
    arena.set_learned(off, false);
    assert!(!arena.is_learned(off));
}

#[test]
fn test_delete() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    assert!(arena.is_active(off));
    arena.delete(off);
    assert!(!arena.is_active(off));
    assert!(arena.is_empty_clause(off));
    assert!(arena.is_garbage(off));
    assert!(!arena.is_pending_garbage(off));
}

#[test]
fn test_delete_clears_pending_garbage() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    arena.set_pending_garbage(off, true);
    arena.delete(off);
    assert!(arena.is_empty_clause(off));
    assert!(!arena.is_pending_garbage(off));
}

#[test]
fn test_incremental_clause_counters_track_lifecycle() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2), lit(3)], false);
    let off1 = arena.add(&[lit(-1), lit(4)], true);
    let off2 = arena.add(&[lit(5), lit(6)], false);
    assert_clause_counters(&arena, 3, 2, 1);

    arena.set_learned(off2, true);
    assert_clause_counters(&arena, 3, 1, 2);

    arena.replace(off0, &[lit(1), lit(2)]);
    assert_clause_counters(&arena, 3, 1, 2);

    arena.delete(off1);
    assert_clause_counters(&arena, 2, 1, 1);

    arena.set_learned(off0, true);
    assert_clause_counters(&arena, 2, 0, 2);

    arena.set_learned(off0, false);
    assert_clause_counters(&arena, 2, 1, 1);
}

#[test]
fn test_replace_shrink() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    arena.replace(off, &[lit(1), lit(2)]);
    assert_eq!(arena.len_of(off), 2);
    assert_eq!(arena.literal(off, 0), lit(1));
    assert_eq!(arena.literal(off, 1), lit(2));
    assert_eq!(arena.saved_pos(off), 2);
}

#[test]
fn test_replace_same_size() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    arena.replace(off, &[lit(4), lit(5), lit(6)]);
    assert_eq!(arena.len_of(off), 3);
    assert_eq!(arena.literal(off, 0), lit(4));
    assert_eq!(arena.literal(off, 1), lit(5));
    assert_eq!(arena.literal(off, 2), lit(6));
}

#[test]
fn test_replace_clears_flags() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    arena.set_pending_garbage(off, true);
    arena.set_garbage(off, true);
    arena.replace(off, &[lit(1), lit(2)]);
    assert!(!arena.is_pending_garbage(off));
    assert!(!arena.is_garbage(off));
}

#[test]
fn test_compact_removes_deleted() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let _off1 = arena.add(&[lit(3), lit(4)], false);
    let off2 = arena.add(&[lit(5), lit(6)], false);
    arena.delete(_off1);

    let remapping = arena.compact();
    assert_eq!(arena.num_clauses(), 2);
    assert_eq!(arena.active_literals(), 4);
    assert_eq!(remapping.len(), 2);
    assert_eq!(remapping[0].0, off0);
    assert_eq!(remapping[1].0, off2);

    let new_off0 = remapping[0].1;
    let new_off2 = remapping[1].1;
    assert_eq!(arena.literal(new_off0, 0), lit(1));
    assert_eq!(arena.literal(new_off0, 1), lit(2));
    assert_eq!(arena.literal(new_off2, 0), lit(5));
    assert_eq!(arena.literal(new_off2, 1), lit(6));
}

#[test]
fn test_compact_reclaims_dead_tail() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3), lit(4), lit(5)], false);
    assert_eq!(arena.total_words(), 8); // 3 header + 5 lits

    arena.replace(off, &[lit(1), lit(2), lit(3)]);
    assert_eq!(arena.total_words(), 8); // dead space still present

    let remapping = arena.compact();
    assert_eq!(remapping.len(), 1);
    assert_eq!(arena.total_words(), 6); // 3 header + 3 lits
}

#[test]
fn test_compact_preserves_incremental_clause_counters() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2), lit(3)], false);
    let off1 = arena.add(&[lit(4), lit(5)], true);
    let off2 = arena.add(&[lit(6), lit(7), lit(8)], false);

    arena.set_learned(off2, true);
    arena.delete(off1);
    arena.replace(off0, &[lit(1), lit(2)]);
    assert_clause_counters(&arena, 2, 1, 1);

    let remapping = arena.compact();
    assert_eq!(remapping.len(), 2);
    assert_clause_counters(&arena, 2, 1, 1);
}

#[test]
fn test_active_offsets() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4)], false);
    let off2 = arena.add(&[lit(5), lit(6)], false);
    arena.delete(off1);
    let active: Vec<usize> = arena.active_indices().collect();
    assert_eq!(active, vec![off0, off2]);
}

#[test]
fn test_literals_slice() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    assert_eq!(arena.literals(off), &[lit(1), lit(2), lit(3)]);
}

#[test]
fn test_set_literal() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    arena.set_literal(off, 1, lit(7));
    assert_eq!(arena.literal(off, 1), lit(7));
    assert_eq!(arena.literal(off, 0), lit(1));
    assert_eq!(arena.literal(off, 2), lit(3));
}

#[test]
fn test_multiple_clauses_non_overlapping() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4), lit(5)], true);
    let off2 = arena.add(&[lit(6), lit(7)], false);

    assert_eq!(off0, 0);
    assert_eq!(off1, 5);
    assert_eq!(off2, 11);

    arena.set_activity(off1, 1.5);
    arena.set_lbd(off1, 7);
    arena.set_used(off1, 10);

    assert_eq!(arena.len_of(off0), 2);
    assert_eq!(arena.literal(off0, 0), lit(1));
    assert_eq!(arena.activity(off0), 0.0);
    assert_eq!(arena.lbd(off0), 0);
    assert_eq!(arena.len_of(off2), 2);
    assert_eq!(arena.literal(off2, 0), lit(6));
}

#[test]
fn test_memory_bytes() {
    let arena = ClauseArena::new();
    assert!(arena.memory_bytes() > 0);
}

#[test]
fn test_with_capacity() {
    let arena = ClauseArena::with_capacity(100, 500);
    assert_eq!(arena.num_clauses(), 0);
    assert!(arena.is_empty());
    assert!(arena.memory_bytes() > 48);
}

#[test]
fn test_compact_empty_arena() {
    let mut arena = ClauseArena::new();
    let remapping = arena.compact();
    assert!(remapping.is_empty());
    assert_eq!(arena.num_clauses(), 0);
}

#[test]
fn test_compact_all_deleted() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4)], false);
    arena.delete(off0);
    arena.delete(off1);
    let remapping = arena.compact();
    assert!(remapping.is_empty());
    assert_eq!(arena.num_clauses(), 0);
    assert_eq!(arena.total_words(), 0);
}

#[test]
fn test_compact_preserves_header_fields() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], true);
    arena.set_lbd(off, 3);
    arena.set_activity(off, 2.5);
    arena.set_saved_pos(off, 4);
    arena.set_used(off, 7);
    arena.set_vivify_skip(off, true);

    let remapping = arena.compact();
    let new_off = remapping[0].1;
    assert!(arena.is_learned(new_off));
    assert_eq!(arena.lbd(new_off), 3);
    assert!((arena.activity(new_off) - 2.5).abs() < f32::EPSILON);
    assert_eq!(arena.saved_pos(new_off), 4);
    assert_eq!(arena.used(new_off), 7);
    assert!(arena.is_vivify_skipped(new_off));
}

#[test]
fn test_large_clause() {
    let mut arena = ClauseArena::new();
    let lits: Vec<Literal> = (1..=100).map(lit).collect();
    let off = arena.add(&lits, false);
    assert_eq!(arena.len_of(off), 100);
    assert_eq!(arena.total_words(), 103);
    for i in 0..100 {
        assert_eq!(arena.literal(off, i), lit(i as i32 + 1));
    }
}

#[test]
fn test_cache_line_fit() {
    let mut arena = ClauseArena::new();
    // 3-literal clause: 3 header + 3 lits = 6 words = 24 bytes
    let off3 = arena.add(&[lit(1), lit(2), lit(3)], false);
    assert_eq!((HEADER_WORDS + arena.len_of(off3)) * 4, 24);

    // 10-literal clause: 3 + 10 = 13 words = 52 bytes
    let lits10: Vec<Literal> = (1..=10).map(lit).collect();
    let off10 = arena.add(&lits10, false);
    assert!((HEADER_WORDS + arena.len_of(off10)) * 4 <= 64);

    // 13-literal clause: 3 + 13 = 16 words = 64 bytes (exactly 1 cache line)
    let lits13: Vec<Literal> = (1..=13).map(lit).collect();
    let off13 = arena.add(&lits13, false);
    assert_eq!((HEADER_WORDS + arena.len_of(off13)) * 4, 64);
}

#[test]
fn test_literals_or_deleted_live_clause() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    assert_eq!(arena.literals_or_deleted(off), arena.literals(off));
}

#[test]
fn test_literals_or_deleted_after_delete() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3)], false);
    arena.delete(off);
    assert_eq!(arena.literals_or_deleted(off), &[lit(1), lit(2), lit(3)]);
}

#[test]
fn test_literals_or_deleted_shrunk_then_deleted() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3), lit(4), lit(5)], false);
    arena.replace(off, &[lit(10), lit(20), lit(30)]);
    arena.delete(off);
    let recovered = arena.literals_or_deleted(off);
    assert_eq!(recovered, &[lit(10), lit(20), lit(30)]);
}

#[test]
fn test_literals_or_deleted_arena_walk_after_shrink_delete() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2), lit(3), lit(4), lit(5)], false);
    let off1 = arena.add(&[lit(6), lit(7)], false);
    arena.replace(off0, &[lit(10), lit(20), lit(30)]);
    arena.delete(off0);
    let offsets: Vec<usize> = arena.indices().collect();
    assert_eq!(offsets, vec![off0, off1]);
    assert_eq!(arena.literals(off1), &[lit(6), lit(7)]);
}

// ── compact_reorder tests ──────────────────────────────────────────

#[test]
fn test_compact_reorder_basic() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4)], false);
    let off2 = arena.add(&[lit(5), lit(6)], false);
    arena.delete(off1);

    let remap = arena.compact_reorder(&[off0 as u32, off2 as u32]);

    // Remap table maps old offsets to new offsets.
    assert_ne!(remap[off0], u32::MAX);
    assert_ne!(remap[off2], u32::MAX);
    // Deleted clause's offset should remain u32::MAX (not in order list).
    assert_eq!(remap[off1], u32::MAX);

    // Arena now has exactly 2 clauses.
    assert_eq!(arena.num_clauses(), 2);
    assert_eq!(arena.active_clause_count(), 2);

    // Verify literals are correct at new offsets.
    let new0 = remap[off0] as usize;
    let new2 = remap[off2] as usize;
    assert_eq!(arena.literals(new0), &[lit(1), lit(2)]);
    assert_eq!(arena.literals(new2), &[lit(5), lit(6)]);
}

#[test]
fn test_compact_reorder_reverses_order() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4), lit(5)], true);
    let off2 = arena.add(&[lit(6), lit(7)], false);

    // Reverse order: clause2, clause1, clause0
    let remap = arena.compact_reorder(&[off2 as u32, off1 as u32, off0 as u32]);

    let new0 = remap[off0] as usize;
    let new1 = remap[off1] as usize;
    let new2 = remap[off2] as usize;

    // In the new arena, clause2 should be first (lowest offset).
    assert!(new2 < new1, "clause2 should precede clause1");
    assert!(new1 < new0, "clause1 should precede clause0");

    // Verify literal contents are preserved.
    assert_eq!(arena.literals(new0), &[lit(1), lit(2)]);
    assert_eq!(arena.literals(new1), &[lit(3), lit(4), lit(5)]);
    assert_eq!(arena.literals(new2), &[lit(6), lit(7)]);

    // Verify learned flags preserved.
    assert!(!arena.is_learned(new0));
    assert!(arena.is_learned(new1));
    assert!(!arena.is_learned(new2));
}

#[test]
fn test_compact_reorder_shrunk_clause() {
    let mut arena = ClauseArena::new();
    let off = arena.add(&[lit(1), lit(2), lit(3), lit(4), lit(5)], false);
    assert_eq!(arena.total_words(), 8); // 3 header + 5 lits

    // Shrink from 5 to 2 literals.
    arena.replace(off, &[lit(10), lit(20)]);
    assert_eq!(arena.len_of(off), 2);
    assert_eq!(arena.total_words(), 8); // dead tail still present

    let remap = arena.compact_reorder(&[off as u32]);

    let new_off = remap[off] as usize;
    assert_eq!(arena.len_of(new_off), 2);
    assert_eq!(arena.literals(new_off), &[lit(10), lit(20)]);
    // Compacted arena should have only header + 2 lits = 5 words.
    assert_eq!(arena.total_words(), 5);
}

#[test]
fn test_compact_reorder_dead_clause_in_order_list() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4)], false);
    arena.delete(off0);

    // Pass deleted clause offset in the order list — it should be skipped.
    let remap = arena.compact_reorder(&[off0 as u32, off1 as u32]);

    assert_eq!(remap[off0], u32::MAX);
    assert_ne!(remap[off1], u32::MAX);

    // Only 1 clause should survive.
    assert_eq!(arena.num_clauses(), 1);
    assert_eq!(arena.active_clause_count(), 1);

    let new1 = remap[off1] as usize;
    assert_eq!(arena.literals(new1), &[lit(3), lit(4)]);
}

#[test]
fn test_compact_reorder_counter_accuracy() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false); // irredundant
    let off1 = arena.add(&[lit(3), lit(4)], true); // redundant
    let off2 = arena.add(&[lit(5), lit(6)], false); // irredundant
    let off3 = arena.add(&[lit(7), lit(8)], true); // redundant
    let off4 = arena.add(&[lit(9), lit(10)], false); // irredundant

    // Delete one irredundant and one redundant.
    arena.delete(off0);
    arena.delete(off1);

    // Compact with remaining 3 (off2=irredundant, off3=redundant, off4=irredundant).
    let _remap = arena.compact_reorder(&[off2 as u32, off3 as u32, off4 as u32]);

    assert_eq!(arena.num_clauses(), 3);
    assert_eq!(arena.active_clause_count(), 3);
    assert_eq!(arena.irredundant_count(), 2);
    assert_eq!(arena.redundant_count, 1);
    assert_clause_counters(&arena, 3, 2, 1);
}

#[test]
fn test_compact_reorder_dead_words_reset() {
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4)], false);
    arena.delete(off0);

    // After deletion, dead_words should be > 0.
    assert!(
        arena.dead_words() > 0,
        "dead_words should be positive after delete"
    );
    let dead_before = arena.dead_words();
    assert_eq!(dead_before, HEADER_WORDS + 2); // header + 2 lits

    let _remap = arena.compact_reorder(&[off1 as u32]);

    // After compaction, dead_words must be reset to 0.
    assert_eq!(arena.dead_words(), 0);
}

#[test]
fn test_live_indices_excludes_garbage_kept_husks() {
    // Husk adjudication: `active_indices()` deliberately includes clauses
    // marked via mark_garbage_keep_data() (husks: logically deleted, data
    // kept for reason-pointer windows). `live_indices()` must exclude them
    // and both pending-garbage and fully deleted clauses.
    let mut arena = ClauseArena::new();
    let off0 = arena.add(&[lit(1), lit(2)], false);
    let off1 = arena.add(&[lit(3), lit(4)], false);
    let off2 = arena.add(&[lit(5), lit(6)], false);
    let off3 = arena.add(&[lit(7), lit(8)], false);

    arena.mark_garbage_keep_data(off1); // husk
    arena.set_pending_garbage(off2, true); // pending husk
    arena.delete(off3); // fully deleted

    let active: Vec<usize> = arena.active_indices().collect();
    let live: Vec<usize> = arena.live_indices().collect();

    // active_indices passes husks (data still allocated).
    assert_eq!(active, vec![off0, off1, off2]);
    // live_indices excludes garbage-kept and pending-garbage husks.
    assert_eq!(live, vec![off0]);

    // Husk literal data is intact (reason-pointer contract).
    assert_eq!(arena.literals(off1), &[lit(3), lit(4)]);
}

/// The clause-DB byte heuristic must not notice the growth policy.
///
/// `memory_bytes()` bills `accounted_words`, which is maintained on `Vec`'s
/// own amortized rule (`max(2*cap, len+extra)`, floored at
/// `MIN_NON_ZERO_CAP`) rather than on what the arena really reserves. Below
/// `BOUNDED_GROWTH_THRESHOLD_WORDS` the arena still grows through
/// `Vec::reserve`, so the two must agree EXACTLY — which is the check that
/// pins the model to the real ladder. Above the threshold, and after an
/// explicit `reserve_clauses`, the real capacity diverges by design and the
/// accounting stays where the heuristic has always been.
#[test]
fn test_accounted_words_tracks_vec_growth_ladder_exactly() {
    let mut arena = ClauseArena::new();
    assert_eq!(arena.accounted_words, arena.words.capacity());
    for i in 0..2000u32 {
        let a = lit(i as i32 + 1);
        let b = lit(-((i as i32 % 97) + 1));
        let c = lit((i as i32 % 31) + 1);
        arena.add(&[a, b, c], i % 3 == 0);
        assert!(
            arena.words.capacity() < BOUNDED_GROWTH_THRESHOLD_WORDS,
            "test must stay in the Vec-growth regime"
        );
        assert_eq!(
            arena.accounted_words,
            arena.words.capacity(),
            "accounting ladder diverged from Vec's capacity after {i} clauses"
        );
    }
}

/// An explicit reservation buys real capacity without moving the heuristic.
#[test]
fn large_arena_growth_is_bounded_not_doubled() {
    // THE BARRIER REVIEW FOUND MISSING. Deleting the bounded-growth branch in
    // `ClauseArena::reserve_words` and falling back to `Vec::reserve` was
    // undetected by the entire suite (3090 passed either way), even though on
    // vlsat3_b99 that is the difference between reserving ~1.65 GB and ~1.0 GB.
    //
    // A capacity assertion is the only thing that can catch it: `Vec::reserve`
    // doubles (cap -> 2*cap) while the bounded path grows by a quarter
    // (cap -> cap + cap/4). Past BOUNDED_GROWTH_THRESHOLD_WORDS those differ by
    // hundreds of megabytes, which is exactly the regime this fix exists for.
    let mut arena = ClauseArena::new();
    let threshold = BOUNDED_GROWTH_THRESHOLD_WORDS;
    arena.words.reserve_exact(threshold + 1024);
    arena.words.resize(threshold + 1024, 0);
    let cap_before = arena.words.capacity();
    assert!(
        cap_before >= threshold,
        "precondition: the arena must be past the bounded-growth threshold"
    );

    // Ask for one word more than the spare capacity, forcing a grow.
    let spare = cap_before - arena.words.len();
    arena.reserve_words(spare + 1);

    let cap_after = arena.words.capacity();
    assert!(
        cap_after >= arena.words.len() + spare + 1,
        "the reservation must actually cover the request"
    );
    assert!(
        cap_after < cap_before * 2,
        "large-arena growth must be bounded (cap + cap/4), not doubled: \
         {cap_before} -> {cap_after}. Falling back to `Vec::reserve` here costs \
         ~650 MB on a 51.9M-clause instance and no other test notices."
    );
}

#[test]
fn test_reserve_clauses_does_not_move_the_memory_heuristic() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(1), lit(-2)], false);
    let billed_before = arena.memory_bytes();
    let accounted_before = arena.accounted_words;

    arena.reserve_clauses(100_000, 300_000);
    assert!(
        arena.words.capacity() >= 100_000 * HEADER_WORDS + 300_000,
        "reservation must actually be made"
    );
    assert_eq!(arena.accounted_words, accounted_before);
    assert_eq!(arena.memory_bytes(), billed_before);
}
