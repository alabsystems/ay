// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl Subsumer {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self {
            marks: try_vec_with(owner, num_vars, |_| 0)?,
            stats: SubsumeStats::default(),
            check_limit: DEFAULT_CHECK_LIMIT,
            round_checks: 0,
            schedule: Vec::new(),
            sched_sigs: Vec::new(),
            occs: Vec::new(),
            bins: Vec::new(),
            noccs: Vec::new(),
            // Sized on first use: `OccList::add_clause` grows to cover each
            // literal it sees, and `get` is bounds-safe, so nothing has to
            // pre-size this. Eagerly it costs ~128 resident bytes per
            // variable at solver construction, on every instance, whether or
            // not this engine ever runs.
            full_occs: OccList::new(0),
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
            let actual = Subsumer::try_new_counted(size, &owner).unwrap();
            let expected = Subsumer::new(size);
            assert_eq!(actual.marks, expected.marks);
            assert_eq!(actual.check_limit, expected.check_limit);
            assert_eq!(actual.round_checks, expected.round_checks);
        }
    }
}
