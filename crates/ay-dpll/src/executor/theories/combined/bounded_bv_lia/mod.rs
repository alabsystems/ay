// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-exact bounded Bool/BV/LIA refutation lane.
//!
//! This is intentionally not another theory bridge. The independent proof
//! checker interprets the exact live assertion-plus-assumption roots and
//! returns an opaque snapshot-bound witness only when that source query is
//! UNSAT. The witness is consumed here only as a decision bit: the ordinary
//! public UNSAT funnel re-authenticates the immutable public source roots and
//! remains the sole authority for publication. No transformed proof, model,
//! or solver state exists to leak into the enclosing solve.

use crate::executor::Executor;
use crate::executor_types::SolveResult;
use ay_core::TermId;

impl Executor {
    /// Return a provisional BV/LIA refutation with a conservative assumption
    /// core. Bridge assertions may be consequences of any active assumption,
    /// so a core harvested after those consequences become base assertions is
    /// not source-valid unless it retains every assumption.
    pub(super) fn bv_lia_unsat_candidate(&mut self, assumptions: &[TermId]) -> SolveResult {
        if !assumptions.is_empty() {
            self.last_assumption_core = Some(assumptions.to_vec());
        }
        SolveResult::unsat()
    }

    pub(super) fn try_solve_via_bounded_bv_lia(
        &mut self,
        assumptions: &[TermId],
    ) -> Option<SolveResult> {
        if self.should_abort_theory_loop() {
            return Some(SolveResult::Unknown);
        }

        let mut exact_roots = self.ctx.assertions.clone();
        exact_roots.extend_from_slice(assumptions);
        let authenticated = ay_proof::authenticate_bv_lia_unsat_query(
            &self.ctx.terms,
            &exact_roots,
            self.current_solve_deadline(),
        )
        .ok()
        .is_some_and(|evidence| evidence.is_current_for(&self.ctx.terms, &exact_roots));

        if self.should_abort_theory_loop() {
            return Some(SolveResult::Unknown);
        }

        self.last_statistics.set_string(
            "solver.bv_lia_bounded_source",
            if authenticated { "unsat" } else { "declined" },
        );
        if !authenticated {
            return None;
        }
        self.last_unknown_reason = None;
        Some(self.bv_lia_unsat_candidate(assumptions))
    }
}
