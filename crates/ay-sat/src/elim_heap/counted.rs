// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl ElimHeap {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self {
            heap: Vec::new(),
            pos: try_vec_with(owner, num_vars, |_| INVALID_POS)?,
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
            let actual = ElimHeap::try_new_counted(size, &owner).unwrap();
            let expected = ElimHeap::new(size);
            assert_eq!(actual.heap, expected.heap);
            assert_eq!(actual.pos, expected.pos);
        }
    }
}
