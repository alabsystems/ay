// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane under `check-sat-assuming` (#dt-fd-session).
//!
//! `check-sat-assuming A` over base assertions `B` is `check-sat (B ∧ A)`.
//! The lane reads only `ctx.assertions`, so on the assumption routes it runs
//! on the scoped window that merges `A` into the assertions
//! (`solve_scoped_assumptions`), exactly as the scoped fallback of the QF_DT
//! and DtAx arms has always run it. What changes is the ORDER: those arms ran
//! the direct DT assumption engine first, and only an `unknown` from it
//! reached the lane. On a session whose earlier check the lane decided, the
//! direct engine starts from a state main's warm session never hands it, and
//! measured, it either spent the whole budget (`e13only_hang_burn_budget_csa`)
//! or met main's own DT model-builder defect (`e13only_lost_z3mode_csa_after_lane`),
//! on queries the lane decides at once. So a query the lane's gate admits
//! asks the lane first; anything it does not decide continues to the direct
//! engine unchanged.
//!
//! Soundness is the plain check's: the window is an ordinary assertion set,
//! a SAT answer passes the same validation and independent gate (which also
//! evaluates the assumptions), and an UNSAT (published only where the lane
//! publishes UNSAT at all) reports every assumption as the core, which is
//! always a sound core of an unsatisfiable `B ∧ A`.

use ay_core::TermId;

use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

impl Executor {
    /// Ask the lane for `check-sat-assuming assumptions` over `base`.
    /// `Ok(None)`: not admitted or not decided; the caller continues with its
    /// own routes, and no state of this attempt survives (the lane's bracket
    /// erased it).
    pub(in crate::executor) fn try_dt_finite_domain_assuming(
        &mut self,
        base: &[TermId],
        assumptions: &[TermId],
    ) -> Result<Option<SolveResult>> {
        if !self.dt_fd_admits_window(base, assumptions) {
            return Ok(None);
        }
        let result = self.solve_scoped_assumptions(base, assumptions, Self::solve_dt_fd_only)?;
        Ok((!matches!(result, SolveResult::Unknown)).then_some(result))
    }

    /// The read-only gate over `base ∧ assumptions`, so a query outside the
    /// fragment never pays for a scoped window.
    fn dt_fd_admits_window(&mut self, base: &[TermId], assumptions: &[TermId]) -> bool {
        let mut window = base.to_vec();
        window.extend_from_slice(assumptions);
        let saved = std::mem::replace(&mut self.ctx.assertions, window);
        let admitted = self.dt_fd_scan().is_ok();
        self.ctx.assertions = saved;
        admitted
    }

    /// The lane alone, as a scoped-window solve: `Unknown` when it does not
    /// decide.
    fn solve_dt_fd_only(&mut self) -> Result<SolveResult> {
        Ok(self
            .try_solve_dt_finite_domain()?
            .unwrap_or(SolveResult::Unknown))
    }
}
