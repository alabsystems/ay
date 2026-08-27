// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Test-only state access and fault-injection hooks for `Executor`.

use super::Executor;

impl Executor {
    #[cfg(test)]
    pub(crate) fn last_applied_sat_random_seed_for_test(&self) -> Option<u64> {
        self.last_applied_sat_random_seed.get()
    }

    #[cfg(test)]
    pub(crate) fn last_applied_dpll_random_seed_for_test(&self) -> Option<u64> {
        self.last_applied_dpll_random_seed.get()
    }

    /// Number of core-guided rounds the OLL MaxSMT engine completed on its most
    /// recent invocation (#phase2-pr1). 0 means OLL fell back to the baseline
    /// without core-guided progress. Used by the MaxSMT soundness tests.
    #[cfg(test)]
    pub(crate) fn last_oll_core_rounds_for_test(&self) -> u64 {
        self.last_oll_core_rounds.get()
    }

    /// Force one exact MaxSMT final-accounting value for a fail-closed canary.
    #[cfg(test)]
    pub(crate) fn force_maxsmt_exact_cost_for_test(&self, cost: u64) {
        self.forced_maxsmt_exact_cost.set(Some(cost));
    }

    /// Inject one non-assumption OLL core literal for a fail-closed canary.
    #[cfg(test)]
    pub(crate) fn force_maxsmt_oll_core_anomaly_for_test(&self) {
        self.forced_maxsmt_oll_core_anomaly.set(true);
    }

    /// Corrupt the final MaxSMT witness once, after SAT emission, to prove that
    /// public soft accounting is bound to the final consumer-visible model.
    #[cfg(test)]
    pub(crate) fn force_maxsmt_post_emit_soft_flip_for_test(&self) {
        self.forced_maxsmt_post_emit_soft_flip.set(true);
    }

    /// Corrupt one finite LIA objective after SAT emission to prove that public
    /// optimization outcomes are bound to the final consumer-visible model.
    #[cfg(test)]
    pub(crate) fn force_optimization_post_emit_objective_flip_for_test(&self) {
        self.forced_optimization_post_emit_objective_flip.set(true);
    }

    /// Test-only: record whether the Phase 5 diff-logic engine decided the most
    /// recent solve. No-op outside tests.
    pub(crate) fn record_diff_logic_decided_for_test(&self, decided: bool) {
        #[cfg(test)]
        self.last_diff_logic_decided.set(decided);
        #[cfg(not(test))]
        let _ = decided;
    }

    /// Test-only: whether the Phase 5 diff-logic engine decided the last solve.
    #[cfg(test)]
    pub(crate) fn last_diff_logic_decided_for_test(&self) -> bool {
        self.last_diff_logic_decided.get()
    }
}
