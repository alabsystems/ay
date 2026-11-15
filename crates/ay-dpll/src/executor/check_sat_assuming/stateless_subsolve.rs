// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assumption sub-solves that must not touch session-persistent encoders.

use super::{Executor, Result, SolveResult};
use crate::incremental_state::{IncrementalBvState, IncrementalTheoryState};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

/// The lanes a scoped window was solved on outside incremental mode, kept for
/// the rest of the query: a later sub-solve of the SAME window (the named-core
/// rescue after the arm's scoped retry) continues them, as origin/main's
/// non-incremental route continued the session's lanes. Dropped at the query
/// boundary (`with_scope_root_depths`).
pub(crate) struct ScopedWindowLanes {
    window: Vec<TermId>,
    theory: Option<IncrementalTheoryState>,
    bv: Option<Box<IncrementalBvState>>,
}

impl Executor {
    /// Run `solve` over `ctx.assertions` with every session-persistent
    /// incremental encoder swapped out for a fresh one, then restore them.
    ///
    /// `solve_scoped_assumptions` and `solve_quantified_assumptions` merge
    /// query-local assumption literals into `ctx.assertions`. In incremental
    /// mode the ordinary dispatch lands on lanes that keep ONE SAT solver per
    /// session (`#lra-inc-engine`, the persist-SAT and lazy push/pop pipelines
    /// on `incr_theory_state`, the BV lane on `incr_bv_state`). They encode
    /// every root of `ctx.assertions` and add its activation unit at the
    /// current scope depth. Restoring `ctx.assertions` does not retract that
    /// unit: the assumption stays a hard constraint until the enclosing user
    /// scope is popped, and at depth 0 forever. `(assert (not (= z x))) (push 1) (check-sat-assuming (p))
    /// (assert (not p)) (check-sat)` answered `unsat`.
    ///
    /// An assumption literal must never enter a persistent clause database,
    /// so the sub-solve gets fresh state, as `with_isolated_incremental_state`
    /// gives every other inner solve. The saved state never sees the
    /// assumptions and is put back on every exit, including a panic.
    ///
    /// Outside incremental mode this runs `solve` as is; the scoped route
    /// uses [`Self::solve_scoped_window`], which does not.
    pub(super) fn solve_without_persistent_encoding(
        &mut self,
        solve: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<SolveResult> {
        if !self.incremental_mode {
            return solve(self);
        }
        let saved_theory = self
            .incr_theory_state
            .replace(IncrementalTheoryState::new());
        let saved_bv = self.incr_bv_state.take();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| solve(self)));
        self.incr_theory_state = saved_theory;
        self.incr_bv_state = saved_bv;
        result.unwrap_or_else(|payload| std::panic::resume_unwind(payload))
    }

    /// Solve the scoped route's window (`ctx.assertions` = base ∧ A) on lanes
    /// that are never the session's own, in EVERY session, and put the
    /// session's lanes back on every exit, a panic included.
    ///
    /// A session with `check-sat-assuming` and no `push` never enters
    /// incremental mode, but the lanes below the scoped route keep their state
    /// across queries all the same; origin/main (whose
    /// `solve_without_persistent_encoding` returns early there) solved the
    /// window on the session's lanes, and its assumptions became permanent
    /// units (2026-09-29 scope-leak fix-up: a QF_NIA script of depth-0
    /// windows, `--z3-mode` wrong `unsat`; the same script with a `(push 1)
    /// (pop 1)` first is right). The lanes this solve gets are
    /// [`Self::lanes_for_scoped_window`].
    pub(super) fn solve_scoped_window(
        &mut self,
        solve: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<SolveResult> {
        let (theory, bv, keep) = self.lanes_for_scoped_window();
        let saved_theory = std::mem::replace(&mut self.incr_theory_state, theory);
        let saved_bv = std::mem::replace(&mut self.incr_bv_state, bv);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| solve(self)));
        let theory = std::mem::replace(&mut self.incr_theory_state, saved_theory);
        let bv = std::mem::replace(&mut self.incr_bv_state, saved_bv);
        if keep && result.is_ok() {
            self.scoped_window_lanes = Some(Box::new(ScopedWindowLanes {
                window: self.ctx.assertions.clone(),
                theory,
                bv,
            }));
        }
        result.unwrap_or_else(|payload| std::panic::resume_unwind(payload))
    }

    /// The lanes a scoped window starts on, and whether they are kept for a
    /// later sub-solve of the same window in this query.
    ///
    /// - In incremental mode: an empty theory lane and no BV lane, exactly
    ///   [`Self::solve_without_persistent_encoding`].
    /// - Outside it, the lanes an earlier sub-solve of the same window left
    ///   in this query, if any. Else, when no checked certificate is demanded
    ///   and the window contains every root of the query, a COPY of the
    ///   session's lanes: origin/main's warm computation, on lanes the session
    ///   never sees (the window `(p2 p3)` of the NIA-soundness verifier's
    ///   `incr_nia_7001_0004` is decided only warm). A copy's SAT solvers do
    ///   not log proofs (`Solver::clone_for_incremental`), so a session that
    ///   DEMANDS a checked certificate (`--proof`, `--self-check`, strict
    ///   proofs) gets no copy. The default posture's best-effort tracker
    ///   demands none (measured, 2026-09-29 scope-leak fix-up: with a copy
    ///   there, the non-incremental windows of 2,580 files are decided exactly
    ///   as base decides them, 383 unsat included, and 2 sat windows more).
    ///   A window missing a root (an unsat-core minimizer subset) must not be
    ///   solved under that root's live activation. Else no lanes at all: what
    ///   a non-incremental session starts with (the LIRA disjoint Int/Real
    ///   split is gated on the absence of a theory lane).
    fn lanes_for_scoped_window(
        &mut self,
    ) -> (
        Option<IncrementalTheoryState>,
        Option<Box<IncrementalBvState>>,
        bool,
    ) {
        if self.incremental_mode {
            return (Some(IncrementalTheoryState::new()), None, false);
        }
        if let Some(kept) = self.scoped_window_lanes.take() {
            if kept.window == self.ctx.assertions {
                return (kept.theory, kept.bv, true);
            }
        }
        let window: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let covers_roots = self
            .scope_root_depths
            .as_ref()
            .is_some_and(|roots| roots.keys().all(|root| window.contains(root)));
        if self.checked_certificate_demanded() || !covers_roots {
            return (None, None, true);
        }
        let theory = match self.incr_theory_state.as_ref() {
            None => None,
            Some(session) => match session.fork_for_window() {
                Some(fork) => Some(fork),
                None => return (None, None, true),
            },
        };
        let bv = self
            .incr_bv_state
            .as_ref()
            .map(|session| Box::new(session.fork_for_window()));
        (theory, bv, true)
    }
}

#[cfg(test)]
#[path = "stateless_subsolve_tests.rs"]
mod tests;
