// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Numeric fee eligibility only; the unchanged native BV/LIA checker still
//! re-derives the exact source on every walk. No constant truth is trusted.

use super::*;

const MAX_CHAIN_TERMS: usize = 32;
/// Bounded primitive slot/type/head peeks, prepaid before the source is read.
/// This is logical work, not instruction/allocator/physical-RSS accounting.
pub(crate) const CLOSED_BV_LIA_CLASSIFIER_WORK: usize = 16 * MAX_CHAIN_TERMS;
pub(super) const CHARGE: (usize, usize) = (32 * 1024, 1024 * 1024);

pub(super) fn eligible<E>(
    terms: &TermStore,
    clause: &[TermId],
    poll: Poll<'_, E>,
) -> Result<bool, E> {
    // Explicit outer Not is part of the EXISTING BvLia rule's inverse source.
    // No new syntax, annotation, verifier or decision shortcut is introduced.
    let [literal] = clause else {
        return Ok(false);
    };
    let mut term = *literal;
    for depth in 0..MAX_CHAIN_TERMS {
        poll()?;
        if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::Bool {
            return Ok(false);
        }
        match terms.get(term) {
            TermData::Not(inner) => term = *inner,
            TermData::Const(Constant::Bool(_)) => return Ok(depth != 0),
            // Apps/variables/ITE/Int/BV, dangling/cyclic/too-deep chains,
            // and incomplete scans cannot get a reduced fee.
            _ => return Ok(false),
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests;
