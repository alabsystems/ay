// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{checked_double, try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl Conditioning {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, std::mem::size_of::<Self>())?;
        Ok(Self {
            marks: try_vec_with(owner, num_vars, |_| 0)?,
            candidate_lits: try_vec_with(owner, checked_double(owner, num_vars)?, |_| false)?,
            conditional: Vec::new(),
            occs: Vec::new(),
            candidates: Vec::new(),
            unassigned: Vec::new(),
            stats: ConditioningStats::default(),
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
            let actual = Conditioning::try_new_counted(size, &owner).unwrap();
            let expected = Conditioning::new(size);
            assert_eq!(actual.marks, expected.marks);
            assert_eq!(actual.candidate_lits, expected.candidate_lits);
            assert_eq!(actual.conditional, expected.conditional);
            assert_eq!(actual.occs, expected.occs);
            assert_eq!(actual.candidates, expected.candidates);
            assert_eq!(actual.unassigned, expected.unassigned);
        }
    }
}
