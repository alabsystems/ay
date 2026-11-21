// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::Result;
use ay_core::original_query::CountedAdmission;

impl Factor {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self {
            num_vars,
            // Allocated on the first factoring round, as in `Factor::new`.
            marks: Vec::new(),
            counts: Vec::new(),
            occ_binary_counts: Vec::new(),
            occ_large_counts: Vec::new(),
            occ_next_large_counts: Vec::new(),
            occ_candidates: Vec::new(),
            counted: Vec::new(),
            nounted: Vec::new(),
            cand_matches: Vec::new(),
            eligible_buf: Vec::new(),
            dedup_keys: Vec::new(),
            probe_lines: 0,
            delete_marks: Vec::new(),
            step_deleted: Vec::new(),
            schedule: std::collections::BinaryHeap::new(),
            in_schedule: Vec::new(),
            lrat_dry_run_sidecars: Vec::new(),
            lrat_preflight_stats: FactorLratPreflightStats::default(),
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
            let actual = Factor::try_new_counted(size, &owner).unwrap();
            let expected = Factor::new(size);
            assert_eq!(actual.num_vars, expected.num_vars);
            assert_eq!(actual.marks, expected.marks);
            assert_eq!(actual.counts, expected.counts);
            assert_eq!(actual.occ_binary_counts, expected.occ_binary_counts);
            assert_eq!(actual.occ_large_counts, expected.occ_large_counts);
            assert_eq!(actual.occ_next_large_counts, expected.occ_next_large_counts);
            assert_eq!(actual.in_schedule, expected.in_schedule);
            assert_eq!(actual.probe_lines, expected.probe_lines);
        }
    }
}
