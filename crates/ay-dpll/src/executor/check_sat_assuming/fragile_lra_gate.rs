// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The QF_LRA/LRA fragile-construct gate on assumption UNSAT verdicts.
//!
//! # What it guards
//!
//! A June 2026 differential fuzz found false `unsat` answers from
//! `check-sat-assuming` on QF_LRA queries carrying a disequality (`distinct`,
//! `(not (= ..))`) or Boolean structure (`ite`, `or`). The assumption routes —
//! the direct `solve_with_assumptions` route and the scoped fallback — do not
//! reach the plain path's #9604 standalone re-verification, so a guard was
//! added here that turned EVERY such UNSAT into `unknown`. The mechanism
//! behind those witnesses was never isolated. A later one was: scoped
//! assumption sub-solves leaked the assumption literals into
//! session-persistent SAT state (fixed by isolating every scoped-window lane,
//! ec28f5b4f). Absence of a known bug is not a soundness
//! argument, so the gate is kept and its action changes.
//!
//! # What it does now
//!
//! A suspect UNSAT is published only when it is CERTIFIED independently of
//! the route that produced it: `base ∧ core` (the harvested assumption core,
//! falling back to the full assumption set) is re-decided on a disposable,
//! non-incremental executor through the ordinary `check_sat` pipeline, and
//! the verdict counts only if that probe's mandatory UNSAT funnel mints a
//! checked certificate (`checked_exact_unsat_solve_without_trust_discharge`:
//! a strict proof, an independently checked refutation, or an exact semantic
//! theorem). Two classes are refused: the competition raw admission (the
//! probe never enters shedding) and `DischargedTrust`, whose evidence is a
//! fresh run of the same engine re-deriving `unsat` — exactly what a
//! repeatable engine bug in this class would also do. The token must still
//! match this executor's exact roots and term snapshot when consumed. Any
//! failure — budget, stop, SAT, unknown, uncertified — keeps the old
//! fail-closed `unknown`.
//!
//! The check runs in every posture. Under competition shedding the outer
//! UNSAT would otherwise publish raw; in certified postures the outer funnel
//! would certify a public verdict anyway, but INTERNAL consumers of
//! `check_sat_assuming` (optimization bound probes, the MaxSMT lower bound)
//! read the verdict without that funnel, so the gate must not assume it.

use ay_core::TermId;

use super::Executor;

/// Wall-clock allowance for one certification probe. Matches the
/// assumption-core certification probes in this module family; the outer
/// solve deadline still bounds it.
const FRAGILE_LRA_CERTIFICATION_BUDGET_MS: u64 = 2_000;

impl Executor {
    /// `true` when the provisional assumption UNSAT is in the fragile QF_LRA /
    /// LRA class AND no checked certificate could be obtained for it — the
    /// caller must then publish `unknown`.
    ///
    /// On success the harvested assumption core is certified along with the
    /// verdict: a proper-subset core is kept only if `base ∧ core` itself was
    /// certified; if only `base ∧ assumptions` was, the core widens to the
    /// full assumption set, which that certificate covers.
    pub(super) fn fragile_lra_assumption_unsat_uncertified(
        &mut self,
        assumptions: &[TermId],
    ) -> bool {
        if !self.logic().is_some_and(|l| l == "QF_LRA" || l == "LRA")
            || !self.lra_roots_contain_disequality(assumptions)
        {
            return false;
        }
        let core = self
            .last_assumption_core
            .clone()
            .filter(|core| core.iter().all(|t| assumptions.contains(t)));
        let proper_core = core
            .as_ref()
            .filter(|core| assumptions.iter().any(|t| !core.contains(t)));
        if let Some(core) = proper_core {
            if self.certify_fragile_lra_obligation(core) {
                return false;
            }
        }
        if self.certify_fragile_lra_obligation(assumptions) {
            if proper_core.is_some() {
                self.last_assumption_core = Some(assumptions.to_vec());
            }
            return false;
        }
        true
    }

    fn certify_fragile_lra_obligation(&mut self, literals: &[TermId]) -> bool {
        let mut obligation = self.ctx.assertions.clone();
        obligation.extend_from_slice(literals);
        // A decline is visible under `--probe-cert-reject` ("checked-isolated
        // UNSAT declined: ... token=<class>").
        self.checked_exact_unsat_solve_without_trust_discharge(
            obligation.clone(),
            FRAGILE_LRA_CERTIFICATION_BUDGET_MS,
        )
        .is_some_and(|checked| checked.consume(self, &obligation))
    }
}

#[cfg(test)]
#[path = "fragile_lra_gate_tests.rs"]
mod tests;
