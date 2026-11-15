// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! t5: a theory conflict that lies wholly BELOW the current level.
//!
//! The assumption loop consults the eager extension only once the assumption
//! prefix is set, so a conflict among root facts (or among the consequences of
//! an early assumption) is reported levels above the literals it mentions.
//! Without chronological backtracking — the session/IC3 profile — 1UIP found
//! no current-level literal, failed closed (back to level 0, nothing learned),
//! and the extension reported the identical conflict again: a livelock that a
//! stop predicate or a deadline ended with `Unknown` (the session-persistent
//! QF_LRA lane answered `unknown` on base assertions refuted by three bounds).
//! The loop now backtracks to the conflict's own level first; at level 0 the
//! clause database itself is refuted.

use std::cell::Cell;

use ay_sat::{
    AssumeResult, ExtCheckResult, ExtPropagateResult, Extension, Literal, SolverContext, Variable,
};

use super::{counted_stop, neg, pos, session_solver};

/// Reports the theory conflict `¬x ∨ ¬y` whenever `x` and `y` are both true.
struct PairConflictExtension {
    x: Variable,
    y: Variable,
    reports: u32,
}

impl PairConflictExtension {
    fn new(x: u32, y: u32) -> Self {
        Self {
            x: Variable::new(x),
            y: Variable::new(y),
            reports: 0,
        }
    }

    fn both_true(&self, ctx: &dyn SolverContext) -> bool {
        ctx.value(self.x) == Some(true) && ctx.value(self.y) == Some(true)
    }
}

impl Extension for PairConflictExtension {
    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        self.both_true(ctx)
    }

    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        let mut out = ExtPropagateResult::none();
        if self.both_true(ctx) {
            self.reports += 1;
            out.conflict = Some(vec![Literal::negative(self.x), Literal::negative(self.y)]);
        }
        out
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        if self.both_true(ctx) {
            self.reports += 1;
            return ExtCheckResult::Conflict(vec![
                Literal::negative(self.x),
                Literal::negative(self.y),
            ]);
        }
        ExtCheckResult::Sat
    }
}

/// t5a: f and g are root units and the theory refutes them together. The
/// conflict surfaces at level 1 (after the assumption) with both literals at
/// level 0, so the database is refuted: Unsat, decided after ONE report, and
/// still Unsat with no assumptions at all.
#[test]
fn t5a_root_level_theory_conflict_under_an_assumption_refutes_the_database() {
    let mut solver = session_solver(3, &[vec![pos(1)], vec![pos(2)]]);
    let mut ext = PairConflictExtension::new(1, 2);
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let result = solver.solve_with_extension_and_assumptions_core(&mut ext, &[pos(0)], Some(&stop));
    assert!(
        matches!(result.result(), AssumeResult::Unsat(..)),
        "a root-level theory conflict must refute, got {result:?} after {} reports",
        ext.reports
    );
    assert_eq!(
        ext.reports, 1,
        "the same conflict was reported again: the analysis bailed instead of refuting"
    );
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let again = solver.solve_with_extension_and_assumptions_core(&mut ext, &[], Some(&stop));
    assert!(
        matches!(again.result(), AssumeResult::Unsat(..)),
        "the refutation is of the database, not of the assumption: {again:?}"
    );
}

/// t5b: a1 implies f and g (level 1), a2 is set at level 2, and the theory
/// refutes f ∧ g once both assumptions are in. The conflict is learned at
/// level 1 (¬a1, core {a1}, one report), and — the negative twin of t5a's
/// refutation exit — a conflict above the root does not refute the database:
/// dropping a1 leaves a satisfiable query. (This shape never livelocked: the
/// lemma stays watched and BCP finds it at level 1 on the next round. It pins
/// that the new backtrack goes to the conflict's level, not to the root.)
#[test]
fn t5b_conflict_above_the_root_is_learned_at_its_level_and_refutes_nothing_else() {
    let mut solver = session_solver(4, &[vec![pos(2), neg(0)], vec![pos(3), neg(0)]]);
    let mut ext = PairConflictExtension::new(2, 3);
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let result =
        solver.solve_with_extension_and_assumptions_core(&mut ext, &[pos(0), pos(1)], Some(&stop));
    let core = result.unsat_core().unwrap_or_else(|| {
        panic!(
            "expected Unsat, got {result:?} after {} reports",
            ext.reports
        )
    });
    assert!(
        core.contains(&pos(0)) && !core.contains(&pos(1)),
        "the conflict needs a1 only; core {core:?}"
    );
    assert_eq!(ext.reports, 1, "the same conflict was reported again");
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let second = solver.solve_with_extension_and_assumptions_core(&mut ext, &[pos(1)], Some(&stop));
    assert!(
        matches!(second.result(), AssumeResult::Sat(..)),
        "without a1 the query is satisfiable (a1 false, f/g free): {second:?}"
    );
}
