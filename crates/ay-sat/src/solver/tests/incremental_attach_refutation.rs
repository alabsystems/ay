// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `attach_new_clauses_incremental` when a new clause refutes the clause
//! database.
//!
//! The attach sets `incremental_original_boundary` past every ledger clause it
//! was handed, which tells every later reset that those clauses are in the
//! arena. A clause falsified at level 0 used to stop the attach there, so the
//! clauses after it (and a refuting unit itself) were recorded as attached but
//! never added; only a later full reset whose clause census happened to count
//! the difference rebuilt the arena from the ledger.

use super::*;

fn lit(var: u32) -> Literal {
    Literal::positive(Variable(var))
}

/// The incremental QF_LRA engine lane's SAT profile (ay-dpll
/// `solve_lra_inc_engine`): new original clauses stay ledger-only until the
/// next incremental reset attaches them.
fn inc_engine_solver(num_vars: usize) -> Solver {
    let mut solver = Solver::new(num_vars);
    solver.set_ic3_mode();
    solver.set_bve_enabled(false);
    solver.set_inc_engine_reset_mode(true);
    solver
}

/// The lane's solve entries (`solve_with_assumptions_impl`,
/// `init_extension_loop`): re-validate the assumption cache, then take the
/// state-preserving reset only where `can_use_incremental_reset` allows it.
fn lane_incremental_reset(solver: &mut Solver) {
    solver.cold.assumption_cache_valid = true;
    assert!(
        solver.can_use_incremental_reset(),
        "the lane takes the state-preserving reset in this state"
    );
    solver.reset_search_state_incremental();
}

fn arena_original_count(solver: &Solver) -> usize {
    solver
        .arena
        .live_indices()
        .filter(|&idx| !solver.arena.is_learned(idx))
        .count()
}

fn assert_every_attached_clause_is_in_the_arena(solver: &Solver) {
    assert!(
        solver.has_empty_clause,
        "the attach must record the refutation"
    );
    assert_eq!(
        solver.cold.incremental_original_boundary,
        solver.cold.original_ledger.num_clauses(),
        "the attach consumed every pending ledger clause"
    );
    assert_eq!(
        arena_original_count(solver),
        solver.cold.incremental_original_boundary,
        "every ledger clause below the boundary must be in the arena"
    );
}

#[test]
fn attach_keeps_the_clauses_after_a_refuting_unit() {
    let (x, a, b) = (lit(0), lit(1), lit(2));
    let mut solver = inc_engine_solver(3);
    solver.add_clause(vec![x]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    // `!x` contradicts the level-0 `x`; two more clauses follow it.
    solver.add_clause(vec![x.negated()]);
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![a.negated()]);
    lane_incremental_reset(&mut solver);

    assert_every_attached_clause_is_in_the_arena(&solver);
}

#[test]
fn attach_keeps_the_clauses_after_a_falsified_clause() {
    let (x, y, a, b) = (lit(0), lit(1), lit(2), lit(3));
    let mut solver = inc_engine_solver(4);
    solver.add_clause(vec![x]);
    solver.add_clause(vec![y]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    // `!x | !y` is falsified by the level-0 `x` and `y`.
    solver.add_clause(vec![x.negated(), y.negated()]);
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![a.negated()]);
    lane_incremental_reset(&mut solver);

    assert_every_attached_clause_is_in_the_arena(&solver);
}
