// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl LitMarks {
    /// Ordinary eager subsumption needs a retired, allocation-free mark array.
    /// Admit actual validation/growth and both normal/exceptional clear walks.
    pub(crate) fn prepare_eager_counted(
        &mut self,
        lits: &[Literal],
        owner: &CountedAdmission,
    ) -> Result<()> {
        use crate::decision_trace::counted_decision::invalid;
        owner.admit(self.marks.len().saturating_add(4), 0)?;
        if !self.overflow.is_empty() || self.marks.iter().any(|mark| *mark != 0) {
            return Err(invalid(owner, "eager subsumption requires retired marks"));
        }
        let mut needed = self.marks.len();
        for &lit in lits {
            owner.admit(5, 0)?; // visit, two marks, normal and exceptional clear
            let var = lit.variable().index();
            if var >= MAX_DENSE_MARK_VARS {
                return Err(invalid(
                    owner,
                    "sparse eager subsumption marks are not admitted",
                ));
            }
            needed = needed.max(var + 1);
        }
        let growth = needed - self.marks.len();
        crate::counted_storage::try_reserve(owner, &mut self.marks, growth)?;
        owner.admit(growth, 0)?;
        self.marks.resize(needed, 0);
        Ok(())
    }

    /// Construct the normal initial state under the invocation's original owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self {
            marks: try_vec_with(owner, num_vars.min(MAX_DENSE_MARK_VARS), |_| 0)?,
            overflow: DetHashMap::default(),
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
            let actual = LitMarks::try_new_counted(size, &owner).unwrap();
            let expected = LitMarks::new(size);
            assert_eq!(actual.marks, expected.marks);
            assert_eq!(actual.overflow, expected.overflow);
        }
    }
}
