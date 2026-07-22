// Copyright 2026 Andrew Yates
// Performance property tests for the LRAT proof checker.
//
// These tests verify that key operations scale correctly and document
// known performance characteristics (arena fragmentation, HashMap overhead).
//
// Findings from P1:595 performance audit:
//   #1: CRITICAL — check_blocked() scans entire clause database O(C*L)
//   #2: MEDIUM — RAT completeness check scans entire database O(C*L)
//   #3: MEDIUM — Arena fragmentation (append-only, no slot reuse)
//   #4: LOW — Redundant ensure_mark_capacity in resolution hot path
//   #6: LOW — SipHash on sequential integer keys (HashMap<u64, ClauseEntry>)
//   #8: INFO — u32 arena offset, silent truncation on overflow

use super::*;

// -- Finding #3: Arena fragmentation (append-only growth) --

#[test]
fn test_arena_compaction_after_deletions() {
    // Variables 1..200 (var_ids 0..199) fit within num_vars=200.
    let mut checker = LratChecker::new(200);
    let n = 100;

    // Add N original binary clauses using variables 1..200.
    for i in 0..n {
        let a = (i * 2 + 1) as i32;
        let b = (i * 2 + 2) as i32;
        checker.add_original((i + 1) as u64, &[lit(a), lit(b)]);
    }
    let arena_after_add = checker.clause_arena.len();
    assert_eq!(arena_after_add, n * 2, "2 literals per clause");

    // Delete all clauses. Compaction triggers progressively during deletion
    // whenever arena > 2x live data (#8624). By the time all clauses are
    // deleted the arena has already been compacted to a small residual size.
    for i in 0..n {
        checker.delete((i + 1) as u64);
    }
    assert!(
        checker.clause_index.is_empty(),
        "all clauses deleted from index"
    );
    // Arena was compacted during deletion cascade. The final compaction
    // fires when live_size > 0 and arena > 2x live. Once live_size reaches
    // 0, no more compactions fire (division by zero guard).
    assert!(
        checker.clause_arena.len() < arena_after_add,
        "arena should have been compacted during deletion cascade"
    );

    // Re-add N clauses with new IDs but same variables (within num_vars).
    let arena_before_readd = checker.clause_arena.len();
    for i in 0..n {
        let a = (i * 2 + 1) as i32;
        let b = (i * 2 + 2) as i32;
        checker.add_original((n + i + 1) as u64, &[lit(a), lit(b)]);
    }
    // Arena grows by exactly N*2 new literals on top of residual dead space
    // (add_original does not trigger compaction — only delete does).
    assert_eq!(
        checker.clause_arena.len(),
        arena_before_readd + n * 2,
        "arena grows by new literals on top of residual dead space"
    );
}

#[test]
fn test_arena_compaction_triggers_when_fragmented() {
    // Verify that compaction triggers when arena > 2x live data.
    let mut checker = LratChecker::new(200);

    // Add 100 binary clauses (200 arena slots).
    for i in 0..100usize {
        let a = (i * 2 + 1) as i32;
        let b = (i * 2 + 2) as i32;
        checker.add_original((i + 1) as u64, &[lit(a), lit(b)]);
    }
    assert_eq!(checker.clause_arena.len(), 200);

    // Delete 90 of 100 → 10 remaining (live=20 literals).
    // Compaction triggers progressively during deletion when arena > 2x live.
    for i in 0..90usize {
        checker.delete((i + 1) as u64);
    }
    assert_eq!(checker.clause_index.len(), 10);

    // The live data is 10 clauses * 2 literals = 20 literals.
    let live_size: usize = checker.clause_index.values().map(|e| e.len as usize).sum();
    assert_eq!(live_size, 20, "live data should be 20 literals");

    // Arena was compacted during the deletion cascade. It may be slightly
    // larger than live_size because the last compaction fired before the
    // final few deletions brought live_size down to exactly 20.
    assert!(
        checker.clause_arena.len() <= live_size * 2,
        "arena ({}) should be at most 2x live data ({})",
        checker.clause_arena.len(),
        live_size
    );
    assert!(
        checker.stats.compactions > 0,
        "compaction should have been triggered"
    );

    // Verify the remaining clauses are still accessible and correct.
    for i in 90..100usize {
        let entry = checker
            .clause_index
            .get(&((i + 1) as u64))
            .expect("clause exists");
        let lits = checker.clause_lits(*entry);
        assert_eq!(lits.len(), 2);
    }
}

// -- Finding #6: HashMap lookup on sequential integer keys --

#[test]
fn test_clause_lookup_scales_with_database_size() {
    // Verify clause operations at various database sizes.
    // num_vars must be large enough for all variables used.
    for n in [10, 100, 500] {
        let num_vars = n * 2 + 4;
        let mut checker = LratChecker::new(num_vars);

        // Add N original binary clauses. Variables: (2i+1, 2i+2) for i in 0..n.
        // Max DIMACS var = 2*(n-1)+2 = 2n. var_id = 2n-1. Needs num_vars >= 2n.
        for i in 0..n {
            let a = (i * 2 + 1) as i32;
            let b = (i * 2 + 2) as i32;
            checker.add_original((i + 1) as u64, &[lit(a), lit(b)]);
        }
        assert_eq!(checker.clause_index.len(), n, "n={n}: all clauses indexed");

        // Add RUP-derivable clause to exercise hint lookup.
        let ref_a = (n * 2 + 1) as i32;
        let ref_b = (n * 2 + 2) as i32;
        checker.add_original((n + 1) as u64, &[lit(ref_a), lit(ref_b)]);
        checker.add_original((n + 2) as u64, &[lit(-ref_a), lit(ref_b)]);

        let ok = checker.add_derived(
            (n + 3) as u64,
            &[lit(ref_b)],
            &[(n + 1) as i64, (n + 2) as i64],
        );
        assert!(
            ok,
            "n={n}: RUP derivation should succeed with {n} background clauses"
        );
        assert_eq!(checker.stats.failures, 0, "n={n}: no failures");
    }
}

// -- Finding #4: Resolution check overhead --

#[test]
fn test_resolution_chain_depth() {
    // Test resolution checking with chains of increasing depth.
    for depth in [2, 5, 10] {
        let mut checker = LratChecker::new(depth + 2);
        let mut cid: u64 = 1;

        // Unit clause (v1).
        checker.add_original(cid, &[lit(1)]);
        cid += 1;
        // Implication chain: (~v_i v v_{i+1}) for i in 1..depth.
        for i in 0..(depth - 1) {
            let neg_vi = -(i as i32 + 1);
            let vi_plus1 = i as i32 + 2;
            checker.add_original(cid, &[lit(neg_vi), lit(vi_plus1)]);
            cid += 1;
        }

        // Derive (v_depth) with hints referencing the chain.
        let hints: Vec<i64> = (1..=depth as i64).collect();
        let ok = checker.add_derived(cid, &[lit(depth as i32)], &hints);
        assert!(ok, "depth={depth}: RUP derivation should succeed");
        assert_eq!(checker.stats.failures, 0, "depth={depth}: no failures");
    }
}

// -- Finding #8: u32 arena offset boundary --

#[test]
fn test_clause_entry_start_within_u32_range() {
    // With num_vars=20, DIMACS variables 1..20 are valid (var_ids 0..19).
    let mut checker = LratChecker::new_lenient(20);

    // Add 10000 binary clauses reusing variables cyclically.
    for i in 0..10_000u64 {
        let a = ((i * 2) % 20 + 1) as i32;
        let b = ((i * 2 + 1) % 20 + 1) as i32;
        checker.add_original(i + 1, &[lit(a), lit(b)]);
    }

    // Arena should have 20000 literals.
    assert_eq!(checker.clause_arena.len(), 20_000);

    // All entries should have start < u32::MAX.
    for (id, entry) in &checker.clause_index {
        assert!(
            u64::from(entry.start) < u64::from(u32::MAX),
            "clause {id}: arena offset {} exceeds u32 range",
            entry.start,
        );
    }
}

// -- Verify deletion correctness at scale --

#[test]
fn test_bulk_deletion_maintains_integrity() {
    // Use lenient mode to avoid cascade failure from any tautological clauses.
    let mut checker = LratChecker::new_lenient(100);
    let n = 200;

    // Add N clauses reusing variables cyclically.
    for i in 0..n {
        let a = (i % 50 + 1) as i32;
        let b = (i % 50 + 51) as i32; // Separate range to avoid tautologies
        checker.add_original((i + 1) as u64, &[lit(a), lit(b)]);
    }
    assert_eq!(checker.clause_index.len(), n);

    // Delete even-numbered clauses.
    let even_ids: Vec<u64> = (1..=n as u64).filter(|id| id % 2 == 0).collect();
    for &id in &even_ids {
        checker.delete(id);
    }
    assert_eq!(checker.clause_index.len(), n / 2, "half should remain");

    // Verify remaining clauses are accessible.
    for id in (1..=n as u64).filter(|id| id % 2 != 0) {
        assert!(
            checker.clause_index.contains_key(&id),
            "odd clause {id} should still be present"
        );
    }

    // Verify deleted clauses are gone.
    for &id in &even_ids {
        assert!(
            !checker.clause_index.contains_key(&id),
            "even clause {id} should be deleted"
        );
    }
}

// -- Verify stats tracking at scale --

#[test]
fn test_stats_accumulation_linear() {
    for n in [10, 50, 100] {
        let num_vars = n * 2 + 4;
        let mut checker = LratChecker::new(num_vars);

        // Add N binary originals.
        for i in 0..n {
            let a = (i * 2 + 1) as i32;
            let b = (i * 2 + 2) as i32;
            checker.add_original((i + 1) as u64, &[lit(a), lit(b)]);
        }
        assert_eq!(checker.stats.originals as usize, n, "n={n}: original count");

        // Add a derivation.
        let ref_a = (n * 2 + 1) as i32;
        let ref_b = (n * 2 + 2) as i32;
        checker.add_original((n + 1) as u64, &[lit(ref_a), lit(ref_b)]);
        checker.add_original((n + 2) as u64, &[lit(-ref_a), lit(ref_b)]);
        let ok = checker.add_derived(
            (n + 3) as u64,
            &[lit(ref_b)],
            &[(n + 1) as i64, (n + 2) as i64],
        );
        assert!(ok, "n={n}: derivation should succeed");
        assert_eq!(checker.stats.derived, 1, "n={n}: one derivation");
    }
}
