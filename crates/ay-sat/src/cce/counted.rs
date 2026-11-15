// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{checked_double, try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl Cce {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, std::mem::size_of::<Self>())?;
        Ok(Self {
            // Sized on demand, not here. `OccList::new(n)` commits
            // `vec![Vec::new(); 2n]` plus a per-literal `PosMap` — 128 resident
            // bytes per variable — and CCE's entry point
            // (`solver/inprocessing/cce.rs`) already calls `ensure_num_vars`
            // immediately before `rebuild`, so nothing reads the list until it
            // has been grown. Measured: this is 863 MB on a 6.7 M-variable
            // SAT-COMP 2026 instance, committed before a clause is read on
            // every instance whether or not CCE ever runs.
            occ: OccList::new(0),
            local_vals: try_vec_with(owner, checked_double(owner, num_vars)?, |_| 0i8)?,
            covered: Vec::new(),
            intersection: Vec::new(),
            cla_marks: try_vec_with(owner, num_vars, |_| 0i8)?,
            added_trail: Vec::new(),
            occ_cache: Vec::new(),
            stats: CCEStats::default(),
            effort: 0,
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
            let actual = Cce::try_new_counted(size, &owner).unwrap();
            let expected = Cce::new(size);
            assert_eq!(actual.local_vals, expected.local_vals);
            assert_eq!(actual.cla_marks, expected.cla_marks);
            assert_eq!(actual.covered, expected.covered);
            assert_eq!(actual.intersection, expected.intersection);
            assert_eq!(actual.effort, expected.effort);
        }
    }
}
