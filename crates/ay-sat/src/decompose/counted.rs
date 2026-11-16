// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{checked_double, try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl Decompose {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        let num_lits = checked_double(owner, num_vars)?;
        Ok(Self {
            dfs: try_vec_with(owner, num_lits, |_| DfsEntry::default())?,
            work: Vec::new(),
            scc_stack: Vec::new(),
            reprs: try_vec_with(owner, num_lits, |i| Literal(i as u32))?,
            stats: DecomposeStats::default(),
            lrat_dry_run_sidecars: Vec::new(),
            lrat_proof_emit_contexts: Vec::new(),
            fmla_guarded_equiv_overlay_lrat_sidecars: Vec::new(),
            fmla_guarded_equiv_support_cover_lrat_sidecars: Vec::new(),
            lrat_main_rewrite_materializer_preflight_enabled: false,
            lrat_preflight_stats: DecomposeLratPreflightStats::default(),
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
            let actual = Decompose::try_new_counted(size, &owner).unwrap();
            let expected = Decompose::new(size);
            assert_eq!(actual.reprs, expected.reprs);
            assert_eq!(actual.work, expected.work);
            assert_eq!(actual.scc_stack, expected.scc_stack);
            assert_eq!(
                actual.lrat_main_rewrite_materializer_preflight_enabled,
                expected.lrat_main_rewrite_materializer_preflight_enabled
            );
            assert_eq!(actual.dfs.len(), expected.dfs.len());
            for (actual, expected) in actual.dfs.iter().zip(&expected.dfs) {
                assert_eq!((actual.idx, actual.min), (expected.idx, expected.min));
            }
        }
    }
}
