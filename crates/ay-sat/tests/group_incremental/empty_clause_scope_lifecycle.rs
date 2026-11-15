// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lifecycle of `has_empty_clause` across push/pop.
//!
//! `pop()` retracts a refutation exactly when the scope depth recorded for it
//! exceeds the depth being popped to; a base-level (depth 0) refutation is
//! permanent. That contract was broken three ways:
//!
//! * The proof-free level-0 conflict path (`--competition`, `--no-proof`)
//!   tested `empty_clause_scope_depth == 0` for "first occurrence", and
//!   `pop()` never reset that field after a retraction. A later refutation
//!   therefore inherited the depth of an earlier, already-retracted one: a
//!   refutation derived under two scopes was recorded at depth 1 and survived
//!   the pop of its own scope (the incremental QF_NIA split loop's
//!   "has_empty_clause=true BEFORE solve()" assertion), and a base-level
//!   refutation was recorded at depth 1 and retracted by an unrelated pop.
//! * `clone_for_incremental` copied the flag but reset its depth to 0, so a
//!   clone never retracted a scoped refutation. With proof production on, an
//!   assumption-level UNSAT under the scope selectors marks the empty clause,
//!   and such a clone answered `unsat` for a satisfiable formula after the pop.
//! * A retraction relied on the next solve deriving the refutation again, but
//!   the state-preserving incremental reset (the incremental QF_LRA engine
//!   lane: `set_ic3_mode` + `set_inc_engine_reset_mode`) resumed from the
//!   level-0 trail whose conflict had already been consumed, and its clause
//!   attach stopped at the first falsified clause while recording every new
//!   clause as attached. The next search returned an assignment violating an
//!   original clause, which the finalize check turned into `unknown`.
//!
//! Every assertion here is on a verdict or the public flag, so every test
//! also runs in `--release`.

use ay_sat::{
    ExtCheckResult, ExtPropagateResult, Extension, Literal, ProofOutput, SatResult, Solver,
    SolverContext, Variable,
};
use ntest::timeout;

struct NoopExtension;

impl Extension for NoopExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }
}

fn lit(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}

fn verdict(result: SatResult) -> &'static str {
    match result {
        SatResult::Sat(_) => "sat",
        SatResult::Unsat(_) => "unsat",
        _ => "unknown",
    }
}

fn solve(solver: &mut Solver) -> &'static str {
    verdict(solver.solve().into_inner())
}

/// The incremental QF_LRA engine lane's SAT profile (ay-dpll `solve_lra_inc_engine`).
fn inc_engine_solver(num_vars: usize) -> Solver {
    let mut solver = Solver::new(num_vars);
    solver.set_ic3_mode();
    solver.set_bve_enabled(false);
    solver.set_inc_engine_reset_mode(true);
    solver
}

/// A refutation derived under two scopes is retracted by popping one of them,
/// even after an earlier refutation derived under one scope was retracted.
#[test]
#[timeout(10_000)]
fn refutation_derived_in_a_scope_is_retracted_when_that_scope_is_popped() {
    let x = lit(0);
    let mut solver = Solver::new(1);
    solver.add_clause(vec![x]);
    solver.add_clause(vec![x.negated()]);

    solver.push();
    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.pop());
    assert!(
        !solver.has_empty_clause(),
        "refutation derived at depth 1 must be retracted by popping to depth 0"
    );

    solver.push();
    solver.push();
    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.pop());
    assert!(
        !solver.has_empty_clause(),
        "refutation derived at depth 2 must be retracted by popping to depth 1; \
         a surviving flag carries the depth of the earlier retracted refutation"
    );
    // The contradiction is in the base clauses, so it is derived again.
    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.pop());
    assert_eq!(solve(&mut solver), "unsat");
}

/// A refutation derived with no scope live is permanent, even when an earlier
/// scoped refutation was retracted before it.
#[test]
#[timeout(10_000)]
fn base_level_refutation_survives_every_pop_after_an_earlier_retraction() {
    let x = lit(0);
    let mut solver = Solver::new(1);
    solver.add_clause(vec![x]);
    solver.add_clause(vec![x.negated()]);

    solver.push();
    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.pop());

    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.has_empty_clause());
    solver.push();
    assert!(solver.pop());
    assert!(
        solver.has_empty_clause(),
        "a refutation derived at depth 0 must survive every pop"
    );
    assert_eq!(solve(&mut solver), "unsat");
}

/// A clone retracts a scoped refutation on the same pop as its original.
#[test]
#[timeout(10_000)]
fn clone_retracts_a_scoped_refutation_like_its_original() {
    let x = lit(0);
    let mut solver = Solver::new(1);
    solver.add_clause(vec![x]);
    solver.add_clause(vec![x.negated()]);
    solver.push();
    assert_eq!(solve(&mut solver), "unsat");

    let mut clone = solver.clone_for_incremental();
    assert!(solver.pop());
    assert!(clone.pop());
    assert_eq!(
        clone.has_empty_clause(),
        solver.has_empty_clause(),
        "clone and original must agree on the refutation after the same pop"
    );
    assert_eq!(solve(&mut solver), "unsat");
    assert_eq!(solve(&mut clone), "unsat");
}

/// With proof production on, a scoped contradiction records a scope-dependent
/// empty clause. A clone that treated it as base-level answered `unsat` for a
/// satisfiable formula after the pop.
#[test]
#[timeout(10_000)]
fn clone_does_not_keep_a_popped_scoped_refutation() {
    let x = lit(0);
    let mut solver = Solver::with_proof_output(1, ProofOutput::lrat_text(Vec::new(), 0));
    solver.push();
    solver.add_clause(vec![x]);
    solver.add_clause(vec![x.negated()]);
    assert_eq!(solve(&mut solver), "unsat");

    let mut clone = solver.clone_for_incremental();
    assert!(clone.pop());
    assert_eq!(
        solve(&mut clone),
        "sat",
        "the scoped contradiction was popped; the remaining formula is empty"
    );
    assert!(solver.pop());
    assert_eq!(solve(&mut solver), "sat");
}

/// Incremental QF_LRA engine lane, contradictory unit: the refutation is found
/// while attaching the unit under two scopes, retracted by the pop to depth
/// one, and must be derived again at depth one.
#[test]
#[timeout(10_000)]
fn inc_engine_rederives_a_base_refutation_after_its_scoped_retraction_unit() {
    let x = lit(0);
    let mut solver = inc_engine_solver(1);
    solver.add_clause(vec![x]);
    assert_eq!(solve(&mut solver), "sat");

    // Base-level (depth 0), deferred to the next incremental reset.
    solver.add_clause(vec![x.negated()]);
    solver.push();
    solver.push();
    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.pop());
    assert_eq!(
        solve(&mut solver),
        "unsat",
        "x and !x are both base-level clauses; popping a scope cannot make them satisfiable"
    );
    assert!(solver.pop());
    assert_eq!(solve(&mut solver), "unsat");
}

/// Incremental QF_LRA engine lane, falsified clause found by BCP (the shape of
/// the fuzzed `(assert (or p q)) (assert (not p)) (assert (not q))` scripts).
#[test]
#[timeout(10_000)]
fn inc_engine_rederives_a_base_refutation_after_its_scoped_retraction_bcp() {
    let (a, b, c) = (lit(0), lit(1), lit(2));
    let mut solver = inc_engine_solver(3);
    solver.add_clause(vec![c]);
    assert_eq!(solve(&mut solver), "sat");

    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![a.negated()]);
    solver.add_clause(vec![b.negated()]);
    solver.push();
    solver.push();
    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.pop());
    assert_eq!(solve(&mut solver), "unsat");
    assert!(solver.pop());
    assert_eq!(solve(&mut solver), "unsat");
}

/// `clear_empty_clause` (the CP-SAT optimizer's retraction) must leave a
/// refutation that still holds derivable. In the incremental QF_LRA engine
/// lane's scoped solve, the state-preserving reset resumed from the level-0
/// trail that had consumed the conflict, and the attach that found `!x`
/// falsified had stopped there while recording the clauses after it as
/// attached: the search returned the model `x`, which violates `!x`
/// (`FINALIZE_SAT_FAIL`, so `unknown`).
#[test]
#[timeout(10_000)]
fn inc_engine_rederives_a_base_refutation_after_clear_empty_clause() {
    let (x, a, b) = (lit(0), lit(1), lit(2));
    let mut solver = inc_engine_solver(3);
    solver.add_clause(vec![x]);
    assert_eq!(solve(&mut solver), "sat");

    // Base-level clauses, deferred to the next incremental reset; its attach
    // finds `!x` falsified first. `(a | b) & !a & !b` is unsatisfiable on its
    // own.
    solver.add_clause(vec![x.negated()]);
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![a.negated()]);
    solver.add_clause(vec![b.negated()]);
    // A live scope routes every solve below through the lane's
    // state-preserving reset; an unscoped solve takes the full reset.
    solver.push();
    assert_eq!(solve(&mut solver), "unsat");

    solver.clear_empty_clause();
    assert_eq!(
        solve(&mut solver),
        "unsat",
        "every clause is base-level; clearing the flag cannot make them satisfiable"
    );
}

/// Incremental QF_LRA engine lane, depth-0 extension solve: a unit that
/// contradicts the level-0 trail refutes the database during the attach, and
/// the solve must answer `unsat` without searching a refuted database. Before
/// the fix it initialised the extension and ran one BCP pass over the refuted
/// database first (`BUG: propagate_bcp_unsafe called with
/// has_empty_clause=true` in debug builds); the search loop's own flag check
/// then answered `unsat`, so release builds were right and only a debug build
/// fails this test on the unfixed solver.
#[test]
#[timeout(10_000)]
fn inc_engine_extension_solve_reports_an_attach_refutation() {
    let x = lit(0);
    let y = lit(1);
    let mut solver = inc_engine_solver(2);
    solver.add_clause(vec![x]);
    solver.add_clause(vec![x.negated(), y]);
    assert_eq!(
        verdict(solver.solve_with_extension(&mut NoopExtension).into_inner()),
        "sat"
    );

    solver.add_clause(vec![y.negated()]);
    assert_eq!(
        verdict(solver.solve_with_extension(&mut NoopExtension).into_inner()),
        "unsat"
    );
    assert!(solver.has_empty_clause());
    assert_eq!(
        verdict(solver.solve_with_extension(&mut NoopExtension).into_inner()),
        "unsat"
    );
}
