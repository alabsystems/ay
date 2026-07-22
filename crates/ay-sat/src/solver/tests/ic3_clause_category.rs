// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 clause category management tests (#8662 Gap 6).
//!
//! Tests for IC3 lemma marking, reduction protection, and constrained
//! clause cleanup. GipSAT uses 4 clause kinds (Trans/Lemma/Learnt/Temporary);
//! ay-sat implements this via the IC3_LEMMA_BIT flag in clause headers.

use super::*;

fn var(i: u32) -> Variable {
    Variable::new(i)
}
fn pos(i: u32) -> Literal {
    Literal::positive(var(i))
}
fn neg(i: u32) -> Literal {
    Literal::negative(var(i))
}

// ════════════════════════════════════════════════════════════════════════════
// Test: IC3_LEMMA_BIT flag round-trip
// ════════════════════════════════════════════════════════════════════════════

/// Verify that the IC3 lemma flag can be set and queried on arena clauses.
#[test]
fn test_ic3_lemma_flag_roundtrip() {
    let mut arena = ClauseArena::new();
    let lits = [pos(0), pos(1), neg(2)];
    let offset = arena.add(&lits, true);

    // Initially not an IC3 lemma.
    assert!(!arena.is_ic3_lemma(offset));

    // Set the flag.
    arena.set_ic3_lemma(offset, true);
    assert!(arena.is_ic3_lemma(offset));

    // Other flags are preserved.
    assert!(arena.is_learned(offset));
    assert!(!arena.is_garbage(offset));
    assert!(!arena.is_hyper(offset));

    // Clear the flag.
    arena.set_ic3_lemma(offset, false);
    assert!(!arena.is_ic3_lemma(offset));
}

/// Verify IC3 lemma flag does not interfere with other flags.
#[test]
fn test_ic3_lemma_flag_orthogonal_to_other_flags() {
    let mut arena = ClauseArena::new();
    let lits = [pos(0), neg(1), pos(2)];
    let offset = arena.add(&lits, true);

    // Set multiple flags simultaneously.
    arena.set_ic3_lemma(offset, true);
    arena.set_hyper(offset, true);
    arena.set_vivify_skip(offset, true);

    assert!(arena.is_ic3_lemma(offset));
    assert!(arena.is_hyper(offset));
    assert!(arena.is_vivify_skipped(offset));
    assert!(arena.is_learned(offset));

    // Clear IC3 lemma, others preserved.
    arena.set_ic3_lemma(offset, false);
    assert!(!arena.is_ic3_lemma(offset));
    assert!(arena.is_hyper(offset));
    assert!(arena.is_vivify_skipped(offset));
}

// ════════════════════════════════════════════════════════════════════════════
// Test: add_ic3_lemma marks clause correctly
// ════════════════════════════════════════════════════════════════════════════

/// Verify that add_ic3_lemma adds a clause and marks it as an IC3 lemma.
#[test]
fn test_add_ic3_lemma_marks_clause() {
    let mut solver = Solver::new(10);
    solver.set_ic3_mode();

    // Add a base formula clause (not a lemma).
    solver.add_clause(vec![pos(0), pos(1)]);

    // Add an IC3 lemma.
    let added = solver.add_ic3_lemma(vec![neg(0), pos(2), neg(3)]);
    assert!(added, "add_ic3_lemma should succeed");

    // Find the IC3 lemma in the arena. It should have the IC3_LEMMA_BIT set.
    let mut found_ic3_lemma = false;
    for offset in solver.arena.active_indices() {
        if solver.arena.is_ic3_lemma(offset) {
            found_ic3_lemma = true;
            // Verify it contains the expected literals.
            let lits = solver.arena.literals(offset);
            assert!(
                lits.len() >= 3,
                "IC3 lemma should have 3+ literals, got {}",
                lits.len()
            );
        }
    }
    assert!(found_ic3_lemma, "should find at least one IC3 lemma clause");
}

// ════════════════════════════════════════════════════════════════════════════
// Test: IC3 lemmas protected from reduce_db
// ════════════════════════════════════════════════════════════════════════════

/// Verify that IC3 lemma clauses survive reduce_db.
///
/// Creates a solver with IC3 lemma clauses and regular learned clauses,
/// then forces reduce_db and checks that IC3 lemmas are retained while
/// regular learned clauses may be deleted.
#[test]
fn test_ic3_lemma_protected_from_reduce_db() {
    let num_vars = 64u32;
    let mut solver = Solver::new(num_vars as usize);
    solver.set_ic3_mode();

    // Add base formula: simple implication chain.
    for i in 0..num_vars - 1 {
        solver.add_clause(vec![neg(i), pos(i + 1)]);
    }

    // Add some IC3 lemmas (learned=false, marked as IC3 lemma).
    let mut ic3_lemma_count = 0;
    for i in 0..20u32 {
        let v1 = i % num_vars;
        let v2 = (i + 3) % num_vars;
        let v3 = (i + 7) % num_vars;
        let added = solver.add_ic3_lemma(vec![neg(v1), pos(v2), neg(v3)]);
        if added {
            ic3_lemma_count += 1;
        }
    }
    assert!(ic3_lemma_count > 0, "should have added some IC3 lemmas");

    // Also add many high-LBD learned clauses that should be eligible for deletion.
    for i in 0..200u32 {
        let v1 = i % num_vars;
        let v2 = (i + 1) % num_vars;
        let v3 = (i + 2) % num_vars;
        let idx = solver.add_clause_db(&[neg(v1), pos(v2), neg(v3)], true);
        // Set high LBD so reduce_db will target these.
        solver.arena.set_lbd(idx, 20);
    }

    // Count IC3 lemmas before reduce.
    let lemmas_before: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();

    // Force reduce_db by setting conflicts high.
    solver.num_conflicts = 10_000;
    solver.cold.next_reduce_db = 0;
    solver.reduce_db();

    // Count IC3 lemmas after reduce.
    let lemmas_after: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();

    // IC3 lemmas must all survive.
    assert_eq!(
        lemmas_before, lemmas_after,
        "IC3 lemma count must not decrease after reduce_db: {lemmas_before} before, {lemmas_after} after"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test: cleanup_constrained_clauses
// ════════════════════════════════════════════════════════════════════════════

/// Verify that cleanup_constrained_clauses removes constrained clauses
/// but preserves IC3 lemmas and regular clauses.
#[test]
fn test_cleanup_constrained_clauses() {
    let num_vars = 20u32;
    let mut solver = Solver::new(num_vars as usize);
    solver.set_ic3_mode();

    // Set up the constraint activation variable.
    let act_var = var(num_vars - 1);
    solver.set_constrain_activation(act_var);

    // Add some base formula clauses.
    solver.add_clause(vec![pos(0), pos(1)]);
    solver.add_clause(vec![neg(1), pos(2)]);

    // Add IC3 lemmas (should be preserved).
    solver.add_ic3_lemma(vec![neg(0), pos(3), neg(4)]);

    // Add constrained clauses (should be cleaned up).
    solver.add_constrained_clause(vec![pos(5), neg(6)]);
    solver.add_constrained_clause(vec![neg(7), pos(8)]);
    solver.add_constrained_clause(vec![pos(9), neg(10), pos(11)]);

    // Count clause categories before cleanup.
    let total_before = solver.arena.active_clause_count();
    let constrained_before = count_constrained_clauses(&solver, act_var);
    assert!(
        constrained_before >= 3,
        "should have at least 3 constrained clauses, got {constrained_before}"
    );

    // Run cleanup (trail must be empty, level 0).
    let deleted = solver.cleanup_constrained_clauses();
    assert!(
        deleted >= 3,
        "should have cleaned up at least 3 constrained clauses, got {deleted}"
    );

    // Verify: no constrained clauses remain.
    let constrained_after = count_constrained_clauses(&solver, act_var);
    assert_eq!(
        constrained_after, 0,
        "all constrained clauses should be cleaned up"
    );

    // Verify: IC3 lemmas are preserved.
    let lemmas_after: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();
    assert!(
        lemmas_after >= 1,
        "IC3 lemmas should survive cleanup_constrained_clauses"
    );

    // Verify: total clause count decreased by the number of constrained clauses deleted.
    let total_after = solver.arena.active_clause_count();
    assert!(
        total_after < total_before,
        "total clause count should decrease after cleanup"
    );
}

/// Verify cleanup_constrained_clauses is a no-op without activation variable.
#[test]
fn test_cleanup_constrained_clauses_noop_without_activation() {
    let mut solver = Solver::new(10);
    solver.set_ic3_mode();

    solver.add_clause(vec![pos(0), pos(1)]);

    let deleted = solver.cleanup_constrained_clauses();
    assert_eq!(
        deleted, 0,
        "cleanup should be no-op without activation variable"
    );
}

/// Verify cleanup_constrained_clauses preserves IC3 lemmas that happen to
/// contain the activation guard literal (edge case: IC3 lemma with guard).
#[test]
fn test_cleanup_preserves_ic3_lemma_with_guard() {
    let num_vars = 20u32;
    let mut solver = Solver::new(num_vars as usize);
    solver.set_ic3_mode();

    let act_var = var(num_vars - 1);
    solver.set_constrain_activation(act_var);

    // Add an IC3 lemma that coincidentally contains the guard literal.
    // This should NOT be cleaned up because it has the IC3_LEMMA_BIT set.
    let guard = Literal::negative(act_var);

    // Use add_ic3_lemma to add and mark as IC3 lemma.
    // The guard literal is part of the lemma, so it will be added.
    solver.add_ic3_lemma(vec![guard, pos(0), neg(1)]);

    let lemmas_before: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();

    let deleted = solver.cleanup_constrained_clauses();
    assert_eq!(deleted, 0, "IC3 lemma with guard should not be cleaned up");

    let lemmas_after: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();
    assert_eq!(lemmas_before, lemmas_after);
}

// ════════════════════════════════════════════════════════════════════════════
// Test: IC3 lemma survives flush path
// ════════════════════════════════════════════════════════════════════════════

/// Verify IC3 lemmas survive the aggressive flush path in reduce_db.
#[test]
fn test_ic3_lemma_protected_from_flush() {
    let num_vars = 32u32;
    let mut solver = Solver::new(num_vars as usize);
    solver.set_ic3_mode();

    // Base formula.
    for i in 0..num_vars - 1 {
        solver.add_clause(vec![neg(i), pos(i + 1)]);
    }

    // Add IC3 lemmas (marked).
    for i in 0..10u32 {
        solver.add_ic3_lemma(vec![
            neg(i % num_vars),
            pos((i + 5) % num_vars),
            neg((i + 10) % num_vars),
        ]);
    }

    // Add regular learned clauses for flush targets.
    for i in 0..100u32 {
        let idx = solver.add_clause_db(
            &[
                neg(i % num_vars),
                pos((i + 1) % num_vars),
                neg((i + 2) % num_vars),
            ],
            true,
        );
        solver.arena.set_lbd(idx, 15);
    }

    let lemmas_before: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();

    // Force a flush by setting next_flush to a past conflict count.
    solver.num_conflicts = 200_000;
    solver.cold.next_flush = 0;
    solver.cold.next_reduce_db = 0;
    solver.reduce_db();

    let lemmas_after: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();

    assert_eq!(
        lemmas_before, lemmas_after,
        "IC3 lemmas must survive flush: {lemmas_before} before, {lemmas_after} after"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test: between_solve_reduce skips IC3 lemmas
// ════════════════════════════════════════════════════════════════════════════

/// Verify that between_solve_reduce (non-IC3 mode) skips IC3 lemma clauses.
///
/// This tests the edge case where IC3 lemmas exist in a non-IC3 solver
/// (e.g., if add_ic3_lemma is called without set_ic3_mode). The lemmas
/// should still be protected from between-solve reduction.
#[test]
fn test_between_solve_reduce_skips_ic3_lemmas() {
    let mut solver = Solver::new(64);
    // Note: NOT setting IC3 mode, so between_solve_reduce will run.

    // Add base formula.
    for i in 0..30u32 {
        solver.add_clause(vec![neg(i), pos(i + 1)]);
    }

    // Manually add learned clauses and mark some as IC3 lemmas.
    let mut _lemma_offsets = Vec::new();
    for i in 0..10u32 {
        let idx = solver.add_clause_db(&[neg(i), pos(i + 5), neg(i + 10)], true);
        solver.arena.set_lbd(idx, 8);
        solver.arena.set_ic3_lemma(idx, true);
        _lemma_offsets.push(idx);
    }

    // Add many more non-lemma learned clauses (reduction candidates).
    for i in 0..200u32 {
        let idx = solver.add_clause_db(&[neg(i % 64), pos((i + 1) % 64), neg((i + 2) % 64)], true);
        solver.arena.set_lbd(idx, 20);
    }

    let lemmas_before: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();
    assert_eq!(lemmas_before, 10);

    // Force between_solve_reduce to fire.
    solver.num_conflicts = BETWEEN_SOLVE_REDUCE_CONFLICT_INTERVAL * 2;
    solver.cold.incremental_solve_count = 100;
    solver.between_solve_reduce();

    let lemmas_after: usize = solver
        .arena
        .active_indices()
        .filter(|&idx| solver.arena.is_ic3_lemma(idx))
        .count();

    assert_eq!(
        lemmas_before, lemmas_after,
        "IC3 lemma count must not change after between_solve_reduce: {lemmas_before} before, {lemmas_after} after"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Count active clauses that contain the negative activation literal (constrained clauses).
fn count_constrained_clauses(solver: &Solver, act_var: Variable) -> usize {
    let guard_lit = Literal::negative(act_var);
    solver
        .arena
        .active_indices()
        .filter(|&idx| {
            let lits = solver.arena.literals(idx);
            lits.contains(&guard_lit)
        })
        .count()
}
