// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! t4b-t4e: LAZY reasons at the conflict level of the assumption loop (#8467).
//!
//! The loop materialises current-level lazy reasons before the analysis and
//! the surviving ones before each backtrack, as the theory-backend loop does.
//! It used to do neither: 1UIP met the `LazyTheory` handle, failed closed
//! (back to level 0, nothing learned), and the extension re-propagated the
//! same literal, so a theory that could not re-explain it through a conflict
//! clause looped until the stop predicate fired. That bail loop is what turned
//! a two-conflict UNSAT check of the session-persistent QF_LRA lane into
//! 999,997 conflicts and 6 s of CPU (ay-dpll `executor_tests::
//! lra_inc_dead_atoms::ite_lifted_atoms_die_with_their_scope_and_revive_with_a_new_one`).
//!
//! A handle the theory cannot rebuild is demoted to a decision, and only an
//! analysis that resolves into it fails closed (t4c); one whose cone never
//! meets it learns as usual (t4d). A rebuilt reason through a literal assigned
//! AFTER the propagation is refused like an unrebuildable one (t4e).

use std::cell::Cell;

use ay_sat::{
    AssumeResult, ExtCheckResult, ExtPropagateResult, Extension, Literal, SatUnknownReason,
    SolverContext, Variable,
};

use super::{
    assert_core_subset, counted_stop, neg, pos, session_solver, t4_assumptions, t4_solver,
    ReasonExtension,
};

/// t4b: the lazy reason is materialised before 1UIP, so the refutation is
/// learned in ONE analysis exactly as with the eager reason (t4a): no bail to
/// level 0, no theory re-explanation, the strict-subset core {a1, a4}.
/// Without the pre-analysis materialisation the handle is never explained
/// (`explains == 0`) and the first backtrack is to level 0.
#[test]
fn t4b_lazy_reason_in_the_cone_is_materialised_before_analysis() {
    let mut solver = t4_solver();
    let mut ext = ReasonExtension::new(true);
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let result =
        solver.solve_with_extension_and_assumptions_core(&mut ext, &t4_assumptions(), Some(&stop));
    assert!(ext.propagations > 0, "the extension never propagated p");
    assert!(
        ext.explains > 0,
        "the loop never materialised the lazy handle before 1UIP"
    );
    assert!(
        !ext.backtracks.contains(&0),
        "a lazy reason the theory can rebuild must not make the analysis bail to \
         level 0: {:?}",
        ext.backtracks
    );
    assert_eq!(
        ext.theory_conflicts, 0,
        "the theory had to re-explain p: the lazy reason was not resolved through"
    );
    let core = result
        .unsat_core()
        .unwrap_or_else(|| panic!("expected Unsat, got {result:?}"));
    assert_core_subset(core, &t4_assumptions());
    assert!(
        !core.contains(&pos(1)) && !core.contains(&pos(2)) && core.len() < 4,
        "a materialised lazy reason must give the eager core; got {core:?}"
    );
}

/// t4c (negative twin): a lazy handle the theory can NOT rebuild is never
/// learned from. Materialisation demotes p to a decision, and 1UIP, which has
/// to resolve p (q is the UIP), fails closed on it (#8707): back to level 0,
/// nothing learned. Each round re-propagates p the same way, so the counted
/// stop ends the solve with `Unknown(Interrupted)`; an `Unsat` is acceptable
/// only through the theory's own conflict clause.
#[test]
fn t4c_unexplainable_lazy_reason_fails_closed() {
    let mut solver = t4_solver();
    let mut ext = ReasonExtension::new(true);
    ext.explainable = false;
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let result =
        solver.solve_with_extension_and_assumptions_core(&mut ext, &t4_assumptions(), Some(&stop));
    assert!(ext.propagations > 0, "the extension never propagated p");
    assert!(
        ext.explains > 0,
        "the loop never asked the theory to rebuild the lazy handle"
    );
    assert_eq!(
        ext.backtracks.first(),
        Some(&0),
        "an unexplainable lazy reason must make the analysis bail to level 0: {:?}",
        ext.backtracks
    );
    match result.result() {
        AssumeResult::Unsat(core, _) => {
            assert_core_subset(core, &t4_assumptions());
            assert!(
                ext.theory_conflicts > 0,
                "Unsat without the theory re-explaining p: {core:?}"
            );
        }
        AssumeResult::Unknown => {
            assert_eq!(
                solver.last_unknown_reason(),
                Some(SatUnknownReason::Interrupted),
                "Unknown for a reason other than the stop predicate"
            );
        }
        AssumeResult::Sat(model) => panic!("the assumptions are Unsat; got Sat({model:?})"),
        other => panic!("unexpected result variant {other:?}"),
    }
}

/// u=7 of t4d: an atom no clause mentions.
const STRAY: u32 = 7;

/// t4's EAGER reason for p, plus a lazy propagation of the unrelated atom u
/// once a4 is set (so at the conflict level) through a handle the theory can
/// NOT rebuild.
struct StrayLazyExtension {
    inner: ReasonExtension,
    stray_propagations: u32,
    stray_explains: u32,
}

impl StrayLazyExtension {
    const STRAY_HANDLE: u64 = 11;

    fn stray_due(ctx: &dyn SolverContext) -> bool {
        ctx.value(Variable::new(3)) == Some(true) && ctx.value(Variable::new(STRAY)).is_none()
    }
}

impl Extension for StrayLazyExtension {
    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        self.inner.can_propagate(ctx) || Self::stray_due(ctx)
    }

    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        let mut out = self.inner.propagate(ctx);
        if Self::stray_due(ctx) {
            self.stray_propagations += 1;
            out.lazy_propagations.push((pos(STRAY), Self::STRAY_HANDLE));
        }
        out
    }

    fn explain_lazy_reason(&mut self, _propagated: Literal, _data: u64) -> Option<Vec<Literal>> {
        self.stray_explains += 1;
        None
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.inner.check(ctx)
    }

    fn backtrack(&mut self, new_level: u32) {
        self.inner.backtrack(new_level);
    }
}

/// t4d: an unrebuildable lazy handle at the conflict level but OUTSIDE the
/// 1UIP cone does not stop learning. Materialisation demotes u, yet 1UIP
/// never resolves it, so the refutation is learned in one analysis exactly as
/// in t4a. Arming the sticky failure flag instead aborted EVERY analysis at
/// that level: each round re-propagated u, nothing was learned, and the
/// counted stop answered `Unknown` (the session QF_LRA lane spent 363,646
/// conflicts on an 11-conflict script this way).
#[test]
fn t4d_unexplainable_lazy_reason_outside_the_cone_does_not_stop_learning() {
    let mut solver = session_solver(
        8,
        &[
            vec![pos(4), neg(3)],
            vec![neg(5), neg(4), neg(6)],
            vec![neg(5), neg(4), pos(6)],
        ],
    );
    let mut ext = StrayLazyExtension {
        inner: ReasonExtension::new(false),
        stray_propagations: 0,
        stray_explains: 0,
    };
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let result =
        solver.solve_with_extension_and_assumptions_core(&mut ext, &t4_assumptions(), Some(&stop));
    assert!(
        ext.inner.propagations > 0,
        "the extension never propagated p"
    );
    assert!(
        ext.stray_propagations > 0,
        "the extension never propagated u"
    );
    assert!(
        ext.stray_explains > 0,
        "the loop never tried to rebuild u's handle, so no demoted var was on the \
         trail when 1UIP ran"
    );
    assert!(
        !ext.inner.backtracks.contains(&0),
        "a demoted var outside the cone made the analysis bail to level 0: {:?}",
        ext.inner.backtracks
    );
    let core = result.unsat_core().unwrap_or_else(|| {
        panic!(
            "expected Unsat, got {result:?} after {} propagations of u",
            ext.stray_propagations
        )
    });
    assert_core_subset(core, &t4_assumptions());
    assert!(
        !core.contains(&pos(1)) && !core.contains(&pos(2)) && core.len() < 4,
        "the refutation needs a1 and a4 only; got {core:?}"
    );
}

/// Variables of t4e: assumptions a=0 (level 1) and b=1 (level 2); p=2 is the
/// theory atom, q=3 follows it through (¬p ∨ q), and (¬b ∨ ¬q ∨ ¬p) closes
/// the refutation. The theory knows a → p and q → p.
struct CyclicReasonExtension {
    explains: u32,
}

impl CyclicReasonExtension {
    const HANDLE: u64 = 13;

    fn is_true(ctx: &dyn SolverContext, var: u32) -> bool {
        ctx.value(Variable::new(var)) == Some(true)
    }
}

impl Extension for CyclicReasonExtension {
    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        Self::is_true(ctx, 0) && ctx.value(Variable::new(2)).is_none()
    }

    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        let mut out = ExtPropagateResult::none();
        if Self::is_true(ctx, 0) && ctx.value(Variable::new(2)).is_none() {
            out.lazy_propagations.push((pos(2), Self::HANDLE));
        }
        out
    }

    /// The first explanation is taken under the current state, where q (a
    /// consequence of p) is true: `q → p` is T-valid but circular. Later
    /// ones cite the real premise a.
    fn explain_lazy_reason(&mut self, _propagated: Literal, _data: u64) -> Option<Vec<Literal>> {
        self.explains += 1;
        Some(if self.explains == 1 {
            vec![pos(2), neg(3)]
        } else {
            vec![pos(2), neg(0)]
        })
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        let p_false = ctx.value(Variable::new(2)) == Some(false);
        for premise in [0, 3] {
            if p_false && Self::is_true(ctx, premise) {
                return ExtCheckResult::Conflict(vec![pos(2), neg(premise)]);
            }
        }
        ExtCheckResult::Sat
    }
}

/// t4e: a reason through a later literal of the propagation's level is
/// refused. Accepting `p ∨ ¬q` (q was derived from p) let 1UIP resolve p and
/// q as each other's justification: it learned the unit ¬b, so the core was
/// {b} and b alone stayed refuted although b with a false is satisfiable.
/// Refused, p is demoted, that analysis fails closed, and the next round's
/// grounded reason `p ∨ ¬a` gives the exact core {a, b}.
#[test]
fn t4e_lazy_reason_through_a_later_literal_is_refused() {
    let mut solver = session_solver(4, &[vec![neg(2), pos(3)], vec![neg(1), neg(3), neg(2)]]);
    let mut ext = CyclicReasonExtension { explains: 0 };
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let result =
        solver.solve_with_extension_and_assumptions_core(&mut ext, &[pos(0), pos(1)], Some(&stop));
    let core = result.unsat_core().map(<[Literal]>::to_vec);
    let explains = ext.explains;
    let polls = Cell::new(0u32);
    let stop = counted_stop(&polls);
    let second = solver.solve_with_extension_and_assumptions_core(&mut ext, &[pos(1)], Some(&stop));
    assert!(
        core.as_ref()
            .is_some_and(|core| core.contains(&pos(0)) && core.contains(&pos(1))),
        "a ∧ b is Unsat and the refutation needs both: got {result:?}; b alone then gave {second:?}"
    );
    assert!(
        matches!(second.result(), AssumeResult::Sat(..)),
        "b alone is satisfiable (a, p, q false); a learned clause outlived its premise: {second:?}"
    );
    assert!(
        explains >= 2,
        "the circular reason was the only one asked for: {explains} explanations"
    );
}
