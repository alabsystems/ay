// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Global-lemma recheck state transitions for the NRA refinement loop.

use ay_core::{TheoryResult, TheorySolver};

use crate::NraSolver;

impl NraSolver<'_> {
    /// Capture assertion-derived factor pins after the first LRA check.
    ///
    /// The initial check-loop state contains only asserted atoms; after a
    /// tentative scope, model-point cuts could contaminate the snapshot timing.
    pub(super) fn snapshot_fixed_factors_on_first_iteration(&mut self, iteration: usize) {
        if iteration != 0 {
            return;
        }
        debug_assert_eq!(self.tentative_depth, 0);
        self.refresh_fixed_factor_values();
    }

    /// Authenticate a post-refinement UNSAT using global lemmas only.
    ///
    /// Model-sign cuts choose one branch of a globally satisfiable problem, and
    /// division refinement is a model-point tangent plane. Both are discarded.
    /// Only assertion-implied fixed-factor identities and unconditional
    /// even-power non-negativity are replayed. McCormick envelopes are omitted:
    /// their LRA bounds can depend on shared or implied premises whose exact
    /// provenance is not owned here.
    pub(super) fn recheck_with_global_lemmas(&mut self) -> TheoryResult {
        self.undo_tentative_patch();
        self.fixed_lin_emitted.clear();
        let base = self.lra.check();
        match self.normalize_lra_result(base) {
            result @ (TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)) => return result,
            TheoryResult::Sat => {}
            _ => return TheoryResult::Unknown,
        }
        // A reasonless Gomory cut falls back to its source term, which is an
        // internal arithmetic term rather than an asserted Boolean literal.
        // With no NRA assertions there is no conflict authority to attach.
        if self.asserted.is_empty() {
            return TheoryResult::Unknown;
        }
        self.refresh_fixed_factor_values();

        self.lra.push();
        self.tentative_depth += 1;

        // These reasons authenticate only lemmas entailed by the complete NRA
        // assertion conjunction plus registered monomial semantics. The pin
        // snapshot intentionally ignores arbitrary LRA/shared bounds.
        // Model-selected sign cuts, McCormick bounds, and division tangent
        // planes are not replayed and must never inherit these reasons.
        let reasons = self.asserted.clone();
        let mons = std::mem::take(&mut self.monomials);
        let aliases = std::mem::take(&mut self.scaled_aliases);
        for mon in mons.values().chain(aliases.iter()) {
            self.add_even_power_nonneg_with_reasons(mon, &reasons);
            self.add_fixed_factor_linearization_with_reasons(mon, &reasons);
        }

        let recheck = self.lra.check();
        let recheck = self.normalize_lra_result(recheck);
        let proved = matches!(
            &recheck,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        );

        self.monomials = mons;
        self.scaled_aliases = aliases;
        self.undo_tentative_patch();
        self.fixed_lin_emitted.clear();
        if proved {
            recheck
        } else {
            TheoryResult::Unknown
        }
    }
}

#[cfg(test)]
#[path = "global_recheck_tests.rs"]
mod tests;
