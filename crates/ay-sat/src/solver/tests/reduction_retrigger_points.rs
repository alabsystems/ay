// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The clause-DB triggers' retrigger points (`learned_cap_retrigger_floor`,
//! `clause_db_bytes_after_reduction`) follow the DB down when it shrinks
//! outside `reduce_db`: a deferred compaction, `clear_learned_clauses`, a
//! popped scope's clauses, a between-solve reduction, the #8399 flush of
//! `continue_solving_with_extension`, an incremental arena rebuild.

use super::*;

/// `count` learned ternary clauses of glue 10 over variables 1..64.
fn add_learned_ternaries(solver: &mut Solver, count: u32) {
    for k in 0..count {
        let idx = solver.add_clause_db(
            &[
                Literal::positive(Variable(1 + k % 21)),
                Literal::negative(Variable(22 + (k / 21) % 21)),
                Literal::positive(Variable(43 + (k / 441) % 21)),
            ],
            true,
        );
        solver.arena.set_lbd(idx, 10);
    }
}

/// `reduce_db` records the byte reference before the compaction it has to
/// defer (BCP still has work), and the deferred compaction then lowers it
/// to the bytes it left. Before, the reference kept the pre-compaction
/// bytes, dead clauses included, so the byte growth arm let the DB fill the
/// space the compaction gave back before it counted any growth.
#[test]
fn a_deferred_compaction_lowers_the_byte_reference() {
    let mut solver = Solver::new(64);
    add_learned_ternaries(&mut solver, 4_000);
    solver.cold.next_reduce_db = u64::MAX;
    solver.set_max_clause_db_bytes(Some(0));
    // An unpropagated root literal: compaction is not quiescent.
    solver.enqueue(Literal::positive(Variable(0)), None);
    solver.reduce_db();
    assert!(
        solver.cold.arena_compaction_pending,
        "the compaction was deferred"
    );
    let recorded = solver.cold.clause_db_bytes_after_reduction;
    assert_eq!(recorded, solver.clause_db_memory_bytes());

    assert!(solver.propagate().is_none());
    let compactions = solver.cold.num_arena_compactions;
    solver.run_deferred_arena_compaction();
    assert_eq!(solver.cold.num_arena_compactions, compactions + 1);
    let bytes = solver.clause_db_memory_bytes();
    assert!(
        bytes < recorded,
        "the compaction shrank the DB: {bytes} vs {recorded}"
    );
    assert_eq!(solver.cold.clause_db_bytes_after_reduction, bytes);
}

/// The reference only ever moves down, and only with a byte limit set.
#[test]
fn a_compaction_never_raises_the_byte_reference() {
    let mut limited = Solver::new(64);
    add_learned_ternaries(&mut limited, 2_000);
    limited.set_max_clause_db_bytes(Some(0));
    limited.cold.clause_db_bytes_after_reduction = 1;
    limited.compact_arena_locality();
    assert_eq!(limited.cold.clause_db_bytes_after_reduction, 1);

    let mut unlimited = Solver::new(64);
    add_learned_ternaries(&mut unlimited, 2_000);
    unlimited.cold.clause_db_bytes_after_reduction = usize::MAX;
    unlimited.compact_arena_locality();
    assert_eq!(unlimited.cold.clause_db_bytes_after_reduction, usize::MAX);
}

/// After `clear_learned_clauses` the learned cap fires again once the count
/// is over the cap and past the minimum growth. Before, it waited for the
/// count to regrow past the floor the last reduction left, here 10,000
/// clauses, 2,500 times the cap.
#[test]
fn clearing_learned_clauses_re_arms_the_learned_cap() {
    let mut solver = Solver::new(64);
    solver.cold.next_reduce_db = u64::MAX;
    solver.set_max_learned_clauses(Some(4));
    add_learned_ternaries(&mut solver, 300);
    solver.cold.learned_cap_retrigger_floor = 10_000;
    assert!(!solver.should_reduce_db(), "below the stale floor");
    solver.clear_learned_clauses();
    assert_eq!(solver.arena.redundant_count(), 0);
    assert_eq!(solver.cold.learned_cap_retrigger_floor, 256);
    add_learned_ternaries(&mut solver, 300);
    assert!(
        solver.should_reduce_db(),
        "300 learned clauses against a cap of 4"
    );

    let mut fresh = Solver::new(64);
    add_learned_ternaries(&mut fresh, 10);
    fresh.clear_learned_clauses();
    assert_eq!(
        fresh.cold.learned_cap_retrigger_floor, 0,
        "a floor is never raised"
    );
}

/// Popping a scope deletes the learned clauses that carry its selector,
/// and lowers the floor to what is left.
#[test]
fn popping_a_scope_lowers_the_learned_cap_floor() {
    let mut solver = Solver::new(64);
    add_learned_ternaries(&mut solver, 100);
    solver.push();
    let selector = *solver.cold.scope_selectors.last().expect("a scope");
    for k in 0..500_u32 {
        solver.add_clause_db(
            &[
                Literal::positive(Variable(1 + k % 21)),
                Literal::negative(Variable(22 + (k / 21) % 21)),
                Literal::positive(selector),
            ],
            true,
        );
    }
    solver.cold.learned_cap_retrigger_floor = 10_000;
    assert!(solver.pop());
    let remaining = solver.arena.redundant_count();
    assert_eq!(remaining, 100, "the scope's learned clauses went with it");
    assert_eq!(solver.cold.learned_cap_retrigger_floor, remaining + 256);
}

/// A between-solve reduction lowers the in-search floor to what it left.
#[test]
fn a_between_solve_reduction_lowers_the_learned_cap_floor() {
    let mut solver = Solver::new(256);
    solver.set_ic3_mode();
    for i in 0..50_u32 {
        solver.add_clause_db(
            &[
                Literal::positive(Variable(i)),
                Literal::negative(Variable(i + 1)),
            ],
            false,
        );
    }
    for i in 0..3_000_u32 {
        let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
        solver.arena.set_lbd(idx, 10 + (i % 5));
        while solver.arena.used(idx) > 0 {
            solver.arena.decay_used(idx);
        }
    }
    solver.cold.learned_cap_retrigger_floor = 100_000;
    solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL;
    solver.ic3_enforce_learned_cap();
    let remaining = solver.arena.redundant_count();
    assert!(remaining < 3_000, "the cap deleted learned clauses");
    assert_eq!(
        solver.cold.learned_cap_retrigger_floor,
        remaining + (remaining / 10).max(256)
    );
}

/// A theory extension that propagates nothing.
struct NoTheory;

impl Extension for NoTheory {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }
}

/// `continue_solving_with_extension` flushes every non-core learned clause
/// (#8399) and lowers the floor to what is left. Before, the floor stayed
/// at what the last reduction left, here 10,000 against a cap of 4.
#[test]
fn the_continue_solving_flush_lowers_the_learned_cap_floor() {
    let mut solver = Solver::new(64);
    solver.set_max_learned_clauses(Some(4));
    add_learned_ternaries(&mut solver, 300);
    solver.initialize_watches();
    solver.cold.learned_cap_retrigger_floor = 10_000;
    let _ = solver.continue_solving_with_extension(&mut NoTheory, || false);
    assert_eq!(solver.arena.redundant_count(), 0, "the flush took them all");
    assert_eq!(solver.cold.learned_cap_retrigger_floor, 256);
}

/// The incremental rebuild after destructive inprocessing replaces the arena
/// and drops every learned clause, and lowers the floor to what is left.
#[test]
fn a_destructive_rebuild_lowers_the_learned_cap_floor() {
    let mut solver = Solver::new(64);
    solver.set_max_learned_clauses(Some(4));
    for k in 0..40_u32 {
        solver.add_clause(vec![
            Literal::positive(Variable(k % 64)),
            Literal::negative(Variable((k + 7) % 64)),
            Literal::positive(Variable((k + 19) % 64)),
        ]);
    }
    add_learned_ternaries(&mut solver, 300);
    solver.cold.learned_cap_retrigger_floor = 10_000;
    solver.cold.inprocessing_modified_clause_db = true;
    solver.reset_search_state();
    assert_eq!(solver.arena.redundant_count(), 0, "the rebuild kept none");
    assert_eq!(solver.cold.learned_cap_retrigger_floor, 256);
}
