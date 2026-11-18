// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{checked_double, try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl CongruenceClosure {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self {
            num_vars,
            stats: CongruenceStats::default(),
            gate_extraction_delay: GateExtractionDelay::default(),
            cached_pos_occs: Vec::new(),
            cached_neg_occs: Vec::new(),
            cached_ternary_count: Vec::new(),
            cached_binary_adj: Vec::new(),
            forward_subsumption_matchable: try_vec_with(owner, num_vars, |_| false)?,
            forward_subsumption_marked: try_vec_with(
                owner,
                checked_double(owner, num_vars)?,
                |_| false,
            )?,
            forward_subsume_irredundant_husks: 0,
            deterministic: crate::determinism::deterministic_inproc_enabled(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counted_initial_state_matches_normal_constructor() {
        for size in [0, 1, 7] {
            let owner = crate::counted_storage::test_owner(100_000, 100_000);
            let actual = CongruenceClosure::try_new_counted(size, &owner).unwrap();
            let expected = CongruenceClosure::new(size);
            assert_eq!(actual.num_vars, expected.num_vars);
            assert_eq!(
                actual.forward_subsumption_matchable,
                expected.forward_subsumption_matchable
            );
            assert_eq!(
                actual.forward_subsumption_marked,
                expected.forward_subsumption_marked
            );
            assert_eq!(actual.deterministic, expected.deterministic);
        }
    }
}
