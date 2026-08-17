// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Types and bounded accounting for exact original-clause proof fragments.

mod build_steps;
mod builder;
mod metering;
mod propagation_chains;
mod types;
mod unit_chains;

pub(super) use types::OrFoldUnitPlan;
pub(crate) use types::{
    ExactOriginalProofError, ExactOriginalProofFragment, FragmentInstanceDerivation,
    FragmentInstanceRootDerivation, FragmentPropagationEnvironment, FragmentSkolemDerivation,
};

use ay_sat::{ResolutionValidationError, ResolutionValidationResource};

pub(super) const EXACT_NEW_NOT_BYTES: usize = 1024;

pub(super) fn exact_checked_add(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_add(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

pub(super) fn exact_checked_mul(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_mul(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

pub(super) fn exact_sort_work(len: usize) -> Result<usize, ResolutionValidationError> {
    if len <= 1 {
        return Ok(len);
    }
    let passes = (usize::BITS - (len - 1).leading_zeros()) as usize;
    exact_checked_mul(
        len,
        exact_checked_add(passes, 1, ResolutionValidationResource::Work)?,
        ResolutionValidationResource::Work,
    )
}
