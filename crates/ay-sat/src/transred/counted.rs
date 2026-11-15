// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl TransRed {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, std::mem::size_of::<Self>())?;
        Ok(Self {
            marks: try_vec_with(owner, num_vars, |_| Mark::None)?,
            work: Vec::new(),
            stats: TransRedStats::default(),
            checked: Vec::new(),
            pending_delete: Vec::new(),
            generation: 0,
            last_propagations: 0,
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
            let actual = TransRed::try_new_counted(size, &owner).unwrap();
            let expected = TransRed::new(size);
            assert_eq!(actual.marks, expected.marks);
            assert_eq!(actual.work, expected.work);
            assert_eq!(actual.checked, expected.checked);
            assert_eq!(actual.pending_delete, expected.pending_delete);
            assert_eq!(actual.generation, expected.generation);
            assert_eq!(actual.last_propagations, expected.last_propagations);
        }
    }
}
