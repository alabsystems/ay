// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Internal certificate-inventory postcondition, not external problem authority.

use super::{Control, ReadError};
use crate::bundle::BundleReCheck;
use ay_core::TermId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(in crate::bundle) enum ExactInventoryError {
    #[error("retained proof is incomplete")]
    Incomplete,
    #[error("retained proof has no assumptions")]
    Empty,
    #[error("retained obligation inventory differs from first-use assumptions")]
    Mismatch,
}

/// Compare without a cloned vector/hash table or an unpriced equality walk.
/// Repeated proof assumptions are permitted; repeated, reordered or unused
/// inventory entries are not. The quadratic prefix scan is intentional: each
/// probe is admitted before it runs, against the existing caller allowance.
pub(super) fn check(
    checked: &BundleReCheck,
    inventory: &[TermId],
    control: &mut Control<'_>,
) -> Result<(), ReadError> {
    control.charge(1, 0)?;
    if !checked.quality.is_complete() {
        return Err(ExactInventoryError::Incomplete.into());
    }
    if checked.assume_terms.is_empty() {
        return Err(ExactInventoryError::Empty.into());
    }
    let mut unique = 0usize;
    for (index, term) in checked.assume_terms.iter().enumerate() {
        control.charge(1, 0)?;
        let mut repeated = false;
        for prior in &checked.assume_terms[..index] {
            control.charge(1, 0)?;
            if prior == term {
                repeated = true;
                break;
            }
        }
        if !repeated {
            control.charge(1, 0)?;
            if inventory.get(unique) != Some(term) {
                return Err(ExactInventoryError::Mismatch.into());
            }
            // At most one increment per element of an existing slice.
            unique += 1;
        }
    }
    control.charge(1, 0)?;
    if unique != inventory.len() {
        return Err(ExactInventoryError::Mismatch.into());
    }
    Ok(())
}

#[cfg(test)]
mod tests;
