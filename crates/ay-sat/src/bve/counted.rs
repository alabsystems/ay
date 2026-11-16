// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl BVE {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self {
            // Sized on first use: `OccList::add_clause` grows to cover each
            // literal it sees, and `get` is bounds-safe, so nothing has to
            // pre-size this. Eagerly it costs ~128 resident bytes per
            // variable at solver construction, on every instance, whether or
            // not this engine ever runs.
            occ: BVEOccList::new(0),
            stats: BVEStats::default(),
            num_vars,
            eliminated: try_vec_with(owner, num_vars, |_| false)?,
            resolvent_buf: Vec::new(),
            pruned_root_vars_buf: Vec::new(),
            pos_occ_buf: Vec::new(),
            neg_occ_buf: Vec::new(),
            schedule_gate_pair_credit: try_vec_with(owner, num_vars, |_| 0)?,
            schedule: ElimHeap::try_new_counted(num_vars, owner)?,
            candidate_dirty: try_vec_with(owner, num_vars, |_| false)?,
            rejected_at_bound: try_vec_with(owner, num_vars, |_| u8::MAX)?,
            skip_rejected_at_bound: false,
            schedule_built: false,
            growth_bound: 0,
            fastelim_mode: false,
            quick_elim_mode: false,
            occ_populated: false,
            occ_consistency_epoch: None,
            occ_delta: BveOccDelta::default(),
            occ_saved_state_reuse_enabled: false,
            pos_profile_buf: Vec::new(),
            neg_profile_buf: Vec::new(),
            scope_var_floor: 0,
            additive_fastelim: additive_fastelim_default(num_vars),
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
            let actual = BVE::try_new_counted(size, &owner).unwrap();
            let expected = BVE::new(size);
            assert_eq!(actual.num_vars, expected.num_vars);
            assert_eq!(actual.eliminated, expected.eliminated);
            assert_eq!(
                actual.schedule_gate_pair_credit,
                expected.schedule_gate_pair_credit
            );
            assert_eq!(actual.candidate_dirty, expected.candidate_dirty);
            assert_eq!(actual.rejected_at_bound, expected.rejected_at_bound);
            assert_eq!(actual.growth_bound, expected.growth_bound);
            assert_eq!(actual.additive_fastelim, expected.additive_fastelim);
            assert_eq!(
                actual.skip_rejected_at_bound,
                expected.skip_rejected_at_bound
            );
            assert_eq!(actual.schedule_built, expected.schedule_built);
        }
    }
}
