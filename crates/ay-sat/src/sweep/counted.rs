// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl Sweeper {
    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self {
            num_vars,
            stats: SweepStats::default(),
            marks: LitMarks::try_new_counted(num_vars, owner)?,
            scratch: Vec::new(),
            kitten: {
                // Antecedent tracking is on in BOTH postures so the kitten
                // search is identical with and without a proof surface
                // (proof-posture-parity); cores are only extracted when
                // `want_proof` is set.
                let mut kitten = Kitten::new();
                kitten.enable_antecedent_tracking();
                kitten
            },
            coi_vars: Vec::new(),
            coi_depths: try_vec_with(owner, num_vars, |_| 0)?,
            coi_clauses: HashSet::default(),
            sweep_cursor: 0,
            want_proof: false,
            charge_all_work: false,
            swept_in_pass: try_vec_with(owner, num_vars, |_| 0)?,
            sweep_pass: 1,
            proof_facts: Vec::new(),
            env_kissat: false,
            kissat_call: env_kissat::KissatCall::default(),
            deterministic: crate::determinism::deterministic_inproc_enabled(),
            call: CallBudget::UNLIMITED,
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
            let actual = Sweeper::try_new_counted(size, &owner).unwrap();
            let expected = Sweeper::new(size);
            assert_eq!(actual.num_vars, expected.num_vars);
            assert_eq!(actual.coi_depths, expected.coi_depths);
            assert_eq!(actual.swept_in_pass, expected.swept_in_pass);
            assert_eq!(actual.sweep_cursor, expected.sweep_cursor);
            assert_eq!(actual.sweep_pass, expected.sweep_pass);
            assert_eq!(actual.want_proof, expected.want_proof);
            assert_eq!(actual.charge_all_work, expected.charge_all_work);
            assert_eq!(actual.env_kissat, expected.env_kissat);
            assert_eq!(actual.deterministic, expected.deterministic);
        }
    }
}
