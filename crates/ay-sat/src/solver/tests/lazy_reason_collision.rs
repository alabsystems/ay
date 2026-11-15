// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy theory reason indices colliding with arena clause references.
//!
//! A lazy theory reason (#8467) stores an index into `lazy_theory_reasons` in
//! `VarData.reason`. Those indices start at 0, exactly like arena offsets, so
//! a variable whose lazy index is `k` looks, to a raw `reason == cref.0`
//! comparison, as if its reason were the arena clause at offset `k`. Clause
//! deletion and replacement used such raw comparisons: deleting the clause at
//! offset `k` wrote `NO_REASON` over the lazy index and left the lazy flag
//! set, and the next lazy materialization walk indexed the table with
//! `u32::MAX` (the QSAT kernel's assumption-core solve panicked there).

use super::*;
use crate::extension::{ExtPropagateResult, Extension, SolverContext};
use crate::solver::mutate::{DeleteResult, ReasonPolicy};

/// Explains every lazy propagation `p` as the clause `p ∨ ¬support`.
struct SupportExtension {
    support: Literal,
}

impl Extension for SupportExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn explain_lazy_reason(
        &mut self,
        propagated: Literal,
        _reason_data: u64,
    ) -> Option<Vec<Literal>> {
        Some(vec![propagated, self.support.negated()])
    }
}

fn assign_level0(solver: &mut Solver, lit: Literal, reason: Option<ClauseRef>) {
    assert_eq!(solver.decision_level, 0);
    solver.enqueue(lit, reason);
}

/// The collision fixture.
///
/// Variables: `a` (decision), `b` propagated by the arena clause at offset 0
/// (`b ∨ ¬a ∨ ¬x`), `x` lazily propagated by the theory with lazy index 0.
/// So `x`'s lazy index equals the ClauseRef of `b`'s reason clause, and `x`
/// occurs in that clause.
struct Fixture {
    solver: Solver,
    a: Literal,
    b: Literal,
    x: Literal,
    clause_idx: usize,
}

fn collision_fixture() -> Fixture {
    let mut solver = Solver::new(3);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let x = Literal::positive(Variable(2));

    let clause_idx = solver.arena.len();
    assert_eq!(clause_idx, 0, "the collision needs the clause at offset 0");
    assert!(solver.add_clause(vec![b, a.negated(), x.negated()]));
    let cref = ClauseRef(clause_idx as u32);

    assign_level0(&mut solver, a, None);
    solver.add_lazy_theory_propagation(x, 42);
    assign_level0(&mut solver, b, Some(cref));
    solver.refresh_reason_clause_marks();

    let xd = solver.var_data[x.variable().index()];
    assert!(xd.is_lazy_theory_reason());
    assert_eq!(
        xd.reason, cref.0,
        "fixture must collide: lazy idx == ClauseRef"
    );
    assert!(
        !xd.has_clause_reason(cref),
        "a lazy index is never a clause reason"
    );
    assert!(solver.var_data[b.variable().index()].has_clause_reason(cref));
    assert!(solver.is_reason_clause_marked(clause_idx));

    Fixture {
        solver,
        a,
        b,
        x,
        clause_idx,
    }
}

/// After the mutation, `x` must still hold its lazy reason, and materializing
/// it must produce `x`'s own theory reason (`x ∨ ¬a`).
fn assert_lazy_reason_survives(fixture: &mut Fixture) {
    let x_idx = fixture.x.variable().index();
    let xd = fixture.solver.var_data[x_idx];
    assert!(
        xd.is_lazy_theory_reason(),
        "deleting an unrelated clause must not touch a lazy reason"
    );
    assert_eq!(xd.reason, 0, "the lazy table index must be preserved");

    let mut ext = SupportExtension { support: fixture.a };
    fixture
        .solver
        .materialize_all_lazy_reasons_before_extension_restart(&mut ext);
    let cref = fixture
        .solver
        .var_reason(x_idx)
        .expect("x's lazy reason must materialize into a clause");
    let lits = fixture.solver.arena.literals(cref.0 as usize).to_vec();
    assert_eq!(lits.len(), 2);
    assert_eq!(lits[0], fixture.x);
    assert_eq!(lits[1], fixture.a.negated());
}

#[test]
fn clear_level0_delete_keeps_colliding_lazy_reason() {
    let mut fixture = collision_fixture();
    let deleted = fixture
        .solver
        .delete_clause_checked(fixture.clause_idx, ReasonPolicy::ClearLevel0);
    assert_eq!(deleted, DeleteResult::Deleted);
    assert!(!fixture.solver.arena.is_active(fixture.clause_idx));
    assert_eq!(
        fixture.solver.var_data[fixture.b.variable().index()].reason,
        NO_REASON,
        "the real reason edge of the deleted clause is cleared"
    );
    assert_lazy_reason_survives(&mut fixture);
}

#[test]
fn clear_level0_full_scan_keeps_colliding_lazy_reason_outside_the_clause() {
    // Same collision, but `x` does not occur in the deleted clause, so only
    // the full `0..num_vars` stale-reason scan can reach it.
    let mut solver = Solver::new(4);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let x = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let clause_idx = solver.arena.len();
    assert_eq!(clause_idx, 0);
    assert!(solver.add_clause(vec![b, a.negated(), d.negated()]));
    let cref = ClauseRef(clause_idx as u32);
    assign_level0(&mut solver, a, None);
    assign_level0(&mut solver, d, None);
    solver.add_lazy_theory_propagation(x, 7);
    assign_level0(&mut solver, b, Some(cref));
    solver.refresh_reason_clause_marks();
    assert_eq!(solver.var_data[x.variable().index()].reason, cref.0);

    assert_eq!(
        solver.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0),
        DeleteResult::Deleted
    );
    let mut fixture = Fixture {
        solver,
        a,
        b,
        x,
        clause_idx,
    };
    assert_lazy_reason_survives(&mut fixture);
}

/// The site the QSAT kernel's assumption-core solve reached
/// (`qsat-verify/wf/game-lens/repro/z3mode_kernel_core_panic.smt2` under
/// `--z3-mode`): an instrumented build showed this reset writing `NO_REASON`
/// over lazy index 0 right before the out-of-bounds read.
#[test]
fn replacement_dropping_the_colliding_literal_keeps_lazy_reason() {
    let mut fixture = collision_fixture();
    let old_lits = fixture.solver.arena.literals(fixture.clause_idx).to_vec();
    // Drop x: a raw `reason == clause_ref` test reads x's lazy index 0 as
    // "x is propagated by this clause, and its literal was removed".
    let new_lits = vec![fixture.b, fixture.a.negated()];
    fixture.solver.clear_level0_reasons_removed_by_replacement(
        fixture.clause_idx,
        &old_lits,
        &new_lits,
        0,
    );
    assert!(
        fixture.solver.var_data[fixture.b.variable().index()]
            .has_clause_reason(ClauseRef(fixture.clause_idx as u32)),
        "b's literal survives the replacement, so its reason stays"
    );
    assert_lazy_reason_survives(&mut fixture);
}

#[test]
fn clear_reason_drops_the_lazy_flag() {
    let mut vd = VarData::UNASSIGNED;
    vd.reason = 0;
    vd.set_lazy_theory_reason(true);
    vd.set_seen(true);
    vd.clear_reason();
    assert_eq!(vd.reason, NO_REASON);
    assert!(!vd.is_lazy_theory_reason());
    assert!(vd.is_seen(), "clearing the reason keeps analysis marks");
}

/// A lazy flag left over `NO_REASON` is a broken invariant. The
/// materialization walk must demote the variable to a decision, never index
/// the lazy table with `u32::MAX`.
#[test]
fn lazy_flag_over_no_reason_is_demoted_not_indexed() {
    let mut solver = Solver::new(2);
    let a = Literal::positive(Variable(0));
    let x = Literal::positive(Variable(1));
    assign_level0(&mut solver, a, None);
    solver.add_lazy_theory_propagation(x, 1);
    // Break the invariant the way the unguarded reset sites did.
    solver.var_data[x.variable().index()].reason = NO_REASON;

    let mut ext = SupportExtension { support: a };
    solver.materialize_all_lazy_reasons_before_extension_restart(&mut ext);

    let xd = solver.var_data[x.variable().index()];
    assert!(!xd.is_lazy_theory_reason());
    assert_eq!(xd.reason, NO_REASON);
    assert_eq!(
        solver.arena.num_clauses(),
        0,
        "no reason clause is invented"
    );
}

/// A lazy index that names another variable's table entry must not be read
/// as this variable's reason: that would justify `y` with `x`'s explanation.
#[test]
fn lazy_index_naming_another_variable_is_demoted() {
    let mut solver = Solver::new(3);
    let a = Literal::positive(Variable(0));
    let x = Literal::positive(Variable(1));
    let y = Literal::positive(Variable(2));
    assign_level0(&mut solver, a, None);
    solver.add_lazy_theory_propagation(x, 1);
    solver.add_lazy_theory_propagation(y, 2);
    let x_lazy = solver.var_data[x.variable().index()].reason;
    // Point y at x's entry.
    solver.var_data[y.variable().index()].reason = x_lazy;

    let mut ext = SupportExtension { support: a };
    solver.materialize_all_lazy_reasons_before_extension_restart(&mut ext);

    let x_reason = solver
        .var_reason(x.variable().index())
        .expect("x's own entry still materializes");
    assert_eq!(solver.arena.literals(x_reason.0 as usize)[0], x);
    let yd = solver.var_data[y.variable().index()];
    assert!(!yd.is_lazy_theory_reason());
    assert_eq!(yd.reason, NO_REASON, "y gets no reason borrowed from x");
}
