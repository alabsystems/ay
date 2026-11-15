// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-check-sat budget on what E-matching may create.
//!
//! The round limit and the per-quantifier cap bound one round, not what the
//! rounds add up to, and every instance feeds later passes whose cost can be
//! quadratic in the ground terms it mints (eager BV congruence is one). The
//! budget charges every preprocessing and interleaved round against one
//! allowance for the whole check-sat. Once it is spent no further round
//! runs and the campaign reports `reached_limit`, which routes a ground SAT
//! to `unknown` with reason `(incomplete quantifier-round-limit)`. An UNSAT
//! still stands: each instance is a consequence of its universal whatever
//! the budget left out.

/// Instances one check-sat may create across all E-matching rounds.
pub(in crate::executor) const MAX_EMATCHING_INSTANCES_PER_CHECK: u64 = 100_000;

/// Terms E-matching rounds may add to the term store in one check-sat.
pub(in crate::executor) const MAX_EMATCHING_NEW_TERMS_PER_CHECK: u64 = 2_000_000;

/// What the E-matching rounds of the current check-sat have created so far.
#[derive(Debug, Default, Clone, Copy)]
pub(in crate::executor) struct EmatchingCheckBudget {
    instances: u64,
    new_terms: u64,
}

impl EmatchingCheckBudget {
    /// Charge one round's instances and new terms; returns `true` once the
    /// budget is spent.
    pub(in crate::executor) fn charge(&mut self, instances: usize, new_terms: usize) -> bool {
        self.instances = self.instances.saturating_add(instances as u64);
        self.new_terms = self.new_terms.saturating_add(new_terms as u64);
        self.exhausted()
    }

    /// True when no further E-matching round may run in this check-sat.
    pub(in crate::executor) fn exhausted(&self) -> bool {
        self.instances >= MAX_EMATCHING_INSTANCES_PER_CHECK
            || self.new_terms >= MAX_EMATCHING_NEW_TERMS_PER_CHECK
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn budget_is_spent_by_instances_or_terms() {
        let mut budget = EmatchingCheckBudget::default();
        assert!(!budget.exhausted());
        assert!(!budget.charge(10, 10));
        let rest = (MAX_EMATCHING_INSTANCES_PER_CHECK - 10) as usize;
        assert!(budget.charge(rest, 0));

        let mut budget = EmatchingCheckBudget::default();
        assert!(budget.charge(0, MAX_EMATCHING_NEW_TERMS_PER_CHECK as usize));
    }
}
