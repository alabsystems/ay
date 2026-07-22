// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for oversized-clause splitting (#oversized).
//!
//! A clause with more than `u16::MAX` literals cannot be stored in the arena's
//! 16-bit length field. By default the solver splits such a clause into an
//! equisatisfiable chain of sub-clauses using fresh auxiliary variables. These
//! tests verify the split preserves satisfiability exactly and never sets the
//! truncation poison flag.

use super::*;
use crate::solver::clause_add::OVERSIZED_CLAUSE_SPLIT_THRESHOLD;

/// Build a single clause over `n` fresh positive literals and add it.
fn add_big_positive_clause(solver: &mut Solver, n: usize) {
    let lits: Vec<Literal> = (0..n)
        .map(|i| Literal::positive(Variable(i as u32)))
        .collect();
    solver.add_clause(lits);
}

#[test]
fn oversized_clause_split_solves_sat() {
    // One huge positive clause `(x_0 ∨ … ∨ x_{N-1})` is trivially SAT (set any
    // literal true). After splitting it must still solve as SAT and the poison
    // flag must stay clear.
    let n = OVERSIZED_CLAUSE_SPLIT_THRESHOLD + 1000;
    let mut solver = Solver::new(n);
    add_big_positive_clause(&mut solver, n);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "oversized positive clause must be SAT after splitting, got {result:?}"
    );
    assert!(
        !solver.cold.oversized_clause_poison,
        "splitting must not set the truncation poison flag"
    );
}

#[test]
fn oversized_clause_split_solves_unsat() {
    // `(x_0 ∨ … ∨ x_{N-1})` together with the unit clauses `(¬x_i)` for every
    // i is UNSAT. With splitting enabled the solver must derive UNSAT exactly
    // (no truncation poison ⇒ no downgrade to Unknown).
    let n = OVERSIZED_CLAUSE_SPLIT_THRESHOLD + 50;
    let mut solver = Solver::new(n);
    add_big_positive_clause(&mut solver, n);
    for i in 0..n {
        solver.add_clause(vec![Literal::negative(Variable(i as u32))]);
    }

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "oversized clause + all-negated units must be UNSAT after splitting, got {result:?}"
    );
    assert!(
        !solver.cold.oversized_clause_poison,
        "splitting must not set the truncation poison flag"
    );
}

#[test]
fn oversized_split_allocates_auxiliary_vars() {
    // Splitting introduces fresh auxiliary variables and must advance both
    // num_vars and user_num_vars (the latter so theory layers computing the
    // next free SAT variable from user_num_vars do not alias the auxiliaries).
    let n = OVERSIZED_CLAUSE_SPLIT_THRESHOLD + 1;
    let mut solver = Solver::new(n);
    let before_total = solver.total_num_vars();
    let before_user = solver.user_num_vars();
    add_big_positive_clause(&mut solver, n);
    assert!(
        solver.total_num_vars() > before_total,
        "split must allocate auxiliary variables (num_vars must grow)"
    );
    assert!(
        solver.user_num_vars() > before_user,
        "split auxiliaries must advance user_num_vars so theory layers do not alias them"
    );
}

#[test]
fn under_threshold_clause_not_split() {
    // A clause at exactly the threshold is stored intact: no auxiliary
    // variables, no poison.
    let n = OVERSIZED_CLAUSE_SPLIT_THRESHOLD;
    let mut solver = Solver::new(n);
    let before_total = solver.total_num_vars();
    add_big_positive_clause(&mut solver, n);
    assert_eq!(
        solver.total_num_vars(),
        before_total,
        "a clause at the threshold must not allocate auxiliary variables"
    );
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "expected SAT, got {result:?}"
    );
    assert!(!solver.cold.oversized_clause_poison);
}

#[test]
fn oversized_split_inside_scope_disabled_by_pop() {
    // An oversized clause added inside a push() scope must be split with the
    // scope selector replicated into EVERY chain link, so that pop() (which
    // satisfies the selector) fully disables the whole chain. We make the
    // scoped clause force UNSAT, confirm UNSAT inside the scope, then pop and
    // confirm SAT — proving the chain was genuinely scoped, not leaked.
    let n = OVERSIZED_CLAUSE_SPLIT_THRESHOLD + 30;
    let mut solver = Solver::new(n);
    // Base (global) facts: every x_i is false. SAT on its own.
    for i in 0..n {
        solver.add_clause(vec![Literal::negative(Variable(i as u32))]);
    }
    assert!(
        solver.solve().into_inner().is_sat(),
        "base formula (all x_i false) must be SAT"
    );

    // Scoped oversized clause `(x_0 ∨ … ∨ x_{N-1})` contradicts the base facts.
    solver.push();
    add_big_positive_clause(&mut solver, n);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "scoped oversized clause must make the formula UNSAT inside the scope"
    );

    // Popping the scope must release the entire split chain.
    assert!(solver.pop(), "a scope must be active here");
    assert!(
        solver.solve().into_inner().is_sat(),
        "after pop the scoped oversized chain must be fully disabled (SAT again)"
    );
    assert!(
        !solver.cold.oversized_clause_poison,
        "splitting must not set the truncation poison flag"
    );
}
