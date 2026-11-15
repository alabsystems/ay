// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{checked_double, try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl Sbva {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, std::mem::size_of::<Self>())?;
        Ok(Self {
            num_vars,
            marks: try_vec_with(owner, checked_double(owner, num_vars)?, |_| false)?,
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
            let actual = Sbva::try_new_counted(size, &owner).unwrap();
            let expected = Sbva::new(size);
            assert_eq!(actual.num_vars, expected.num_vars);
            assert_eq!(actual.marks, expected.marks);
        }
    }
}
