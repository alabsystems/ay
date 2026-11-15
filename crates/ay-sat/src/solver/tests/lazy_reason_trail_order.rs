// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A materialized lazy theory reason may cite a literal of the propagation's
//! own level only when that literal precedes the propagation on the trail.
//!
//! A theory explains a lazy propagation under its CURRENT bounds, which can
//! include facts asserted after the propagation and derived from it. Such a
//! reason closes a cycle in the implication graph, and 1UIP then drops the
//! premises that really implied the literal (ay-sat `extension_tests` t4e).

use super::*;
use crate::extension::{ExtPropagateResult, Extension, SolverContext};

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

/// Level 1: `before`, then the lazy propagation `p`, then `after`.
fn solver_with_lazy_p_between() -> (Solver, Literal, Literal, Literal) {
    let mut solver = Solver::new(3);
    let before = Literal::positive(Variable(0));
    let p = Literal::positive(Variable(1));
    let after = Literal::positive(Variable(2));
    solver.decision_level = 1;
    solver.trail_lim.push(0);
    solver.enqueue(before, None);
    solver.add_lazy_theory_propagation(p, 7);
    solver.enqueue(after, None);
    (solver, before, p, after)
}

#[test]
fn a_lazy_reason_through_a_later_literal_of_its_level_is_rejected() {
    let (mut solver, _before, p, after) = solver_with_lazy_p_between();
    let mut ext = SupportExtension { support: after };
    solver.materialize_current_level_lazy_reasons(&mut ext);
    let data = solver.var_data[p.variable().index()];
    assert!(
        !data.is_lazy_theory_reason() && data.reason == NO_REASON,
        "p must be demoted to a decision, not justified by a literal assigned after it"
    );
    assert_eq!(
        solver.arena.num_clauses(),
        0,
        "the cyclic reason clause must not enter the clause DB"
    );
    assert!(
        solver.cold.lazy_materialization_failed,
        "a current-level failure is reported to the caller"
    );
}

/// Negative twin: the same reason through a literal that precedes `p` is
/// materialized as p's reason clause.
#[test]
fn a_lazy_reason_through_an_earlier_literal_of_its_level_is_materialized() {
    let (mut solver, before, p, _after) = solver_with_lazy_p_between();
    let mut ext = SupportExtension { support: before };
    solver.materialize_current_level_lazy_reasons(&mut ext);
    let data = solver.var_data[p.variable().index()];
    assert!(
        !data.is_lazy_theory_reason() && data.reason != NO_REASON,
        "a reason through an earlier literal must become p's reason clause"
    );
    assert_eq!(solver.arena.num_clauses(), 1);
    assert!(!solver.cold.lazy_materialization_failed);
}
