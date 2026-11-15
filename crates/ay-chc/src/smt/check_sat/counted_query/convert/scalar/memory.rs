// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Allocation/copy accounting uses the shared geometric helper. This extra
/// debit prepays element initialization, movement and eventual destruction.
pub(super) fn reserve<T>(
    output: &mut Vec<T>,
    extra: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    let visits = extra.checked_mul(3).ok_or_else(|| {
        Error::Stopped(owner.refuse(ay_core::original_query::CountedAdmissionError::WorkExhausted))
    })?;
    owner.admit(visits, 0)?;
    allocation::vector(output, extra, owner)
}

pub(super) fn push<T>(output: &mut Vec<T>, value: T, owner: &CountedAdmission) -> Result<()> {
    reserve(output, 1, owner)?;
    output.push(value);
    Ok(())
}
