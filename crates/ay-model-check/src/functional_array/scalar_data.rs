// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared scalar-copy pricing and bounded scalar/string formatting.

use super::{charge, FunctionalArrayError};
use crate::ModelValue;

pub(super) fn scalar_cost(value: &ModelValue) -> Result<usize, FunctionalArrayError> {
    match value {
        ModelValue::Bool(_) => Ok(1),
        ModelValue::BitVec { value, width } => {
            usize::try_from(value.bits().max(u64::from(*width)).div_ceil(8))
                .map_err(|_| FunctionalArrayError::Resource)
        }
        _ => Err(FunctionalArrayError::Value),
    }
}

pub(super) fn scalar(value: &ModelValue, work: &mut usize) -> Result<String, FunctionalArrayError> {
    // Decimal conversion and the subsequent allocation are bounded BEFORE it.
    charge(
        work,
        scalar_cost(value)?
            .checked_mul(3)
            .and_then(|n| n.checked_add(32))
            .ok_or(FunctionalArrayError::Resource)?,
    )?;
    match value {
        ModelValue::Bool(value) => Ok(value.to_string()),
        ModelValue::BitVec { width, value } => Ok(format!("(_ bv{value} {width})")),
        _ => Err(FunctionalArrayError::Value),
    }
}

pub(super) fn compose(work: &mut usize, parts: &[&str]) -> Result<String, FunctionalArrayError> {
    let length = parts
        .iter()
        .try_fold(0usize, |sum, part| sum.checked_add(part.len()))
        .ok_or(FunctionalArrayError::Resource)?;
    charge(work, length)?;
    let mut output = String::new();
    output
        .try_reserve_exact(length)
        .map_err(|_| FunctionalArrayError::Allocation)?;
    for part in parts {
        output.push_str(part);
    }
    Ok(output)
}
