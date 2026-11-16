// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{checked_double, try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl Prober {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        let num_lits = checked_double(owner, num_vars)?;
        Ok(Self {
            num_vars,
            probes: Vec::new(),
            bin_occs: try_vec_with(owner, num_lits, |_| 0)?,
            propfixed: try_vec_with(owner, num_lits, |_| -1)?,
            uip_seen: try_vec_with(owner, num_vars, |_| false)?,
            stats: ProbeStats::default(),
            last_search_ticks: 0,
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
            let actual = Prober::try_new_counted(size, &owner).unwrap();
            let expected = Prober::new(size);
            assert_eq!(actual.num_vars, expected.num_vars);
            assert_eq!(actual.bin_occs, expected.bin_occs);
            assert_eq!(actual.propfixed, expected.propfixed);
            assert_eq!(actual.uip_seen, expected.uip_seen);
            assert_eq!(actual.last_search_ticks, expected.last_search_ticks);
        }
    }
}
