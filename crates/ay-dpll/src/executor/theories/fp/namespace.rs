// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Validate the combined namespace before converting or offsetting CNF literals.

use crate::executor_types::UnknownOrigin;

pub(super) fn validate_tseitin_namespace(variables: u32) -> Result<(), UnknownOrigin> {
    if variables > i32::MAX as u32 {
        Err(UnknownOrigin::DeterministicResourceBudget)
    } else {
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::executor) struct FpNamespace {
    offset: i32,
    total_vars: u32,
}

impl FpNamespace {
    pub(in crate::executor) fn new(
        tseitin_num_vars: u32,
        fp_next_var: u32,
    ) -> Result<Self, UnknownOrigin> {
        validate_tseitin_namespace(tseitin_num_vars)?;
        let fp_vars = fp_next_var
            .checked_sub(1)
            .ok_or(UnknownOrigin::DeterministicResourceBudget)?;
        let total_vars = tseitin_num_vars
            .checked_add(fp_vars)
            .ok_or(UnknownOrigin::DeterministicResourceBudget)?;
        validate_tseitin_namespace(total_vars)?;
        Ok(Self {
            offset: tseitin_num_vars as i32,
            total_vars,
        })
    }

    pub(super) fn offset(&self) -> i32 {
        self.offset
    }

    pub(in crate::executor) fn total_vars(&self) -> u32 {
        self.total_vars
    }

    /// Translate a nonzero literal from this encoding's trusted FP namespace.
    /// `new` has already established that either polarity fits in `i32`.
    pub(super) fn offset_lit(&self, literal: i32) -> i32 {
        debug_assert_ne!(literal, 0);
        debug_assert!(literal.unsigned_abs() <= self.total_vars - self.offset as u32);
        if literal > 0 {
            literal + self.offset
        } else {
            literal - self.offset
        }
    }
}

#[cfg(test)]
#[path = "namespace/tests.rs"]
mod tests;
