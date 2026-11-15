// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Validate and poll the requested complete decomposition, then reuse its decoder.

use ay_fp::FpDecomposed;

use super::*;

pub(super) fn root(
    terms: &TermStore,
    term: TermId,
    decomposed: FpDecomposed,
    model: &[bool],
    control: &Control<'_>,
) -> Result<Option<FpModelValue>, UnknownOrigin> {
    control.phase(Some(terms), FpEvalPhase::Decode)?;
    if term.index() >= terms.len() {
        return Ok(None);
    }
    let Sort::FloatingPoint(eb, sb) = terms.sort(term) else {
        return Ok(None);
    };
    // Validate each checked field width before traversing supplied vectors.
    if !(2..=ay_fp::MAX_ENCODING_EXPONENT_BITS).contains(eb)
        || !(2..=ay_fp::MAX_ENCODING_SIGNIFICAND_BITS).contains(sb)
        || eb.checked_add(*sb).is_none()
        || decomposed.precision.exponent_bits() != *eb
        || decomposed.precision.significand_bits() != *sb
        || decomposed.exponent.len() != *eb as usize
        || decomposed.significand.len() != (*sb - 1) as usize
    {
        return Ok(None);
    }
    for lit in std::iter::once(&decomposed.sign)
        .chain(&decomposed.exponent)
        .chain(&decomposed.significand)
    {
        control.poll(Some(terms))?;
        // Do not turn a missing SAT assignment into the decoder's legacy
        // out-of-range false default. No signed negation can overflow here.
        let magnitude = lit.unsigned_abs();
        let Some(index) = magnitude.checked_sub(1) else {
            return Ok(None);
        };
        if magnitude > i32::MAX as u32 || index as usize >= model.len() {
            return Ok(None);
        }
    }
    // Keep the same original control live through every decoded field limb.
    // No temporary singleton map or partial model can escape this boundary.
    let value = Executor::extract_fp_value_from_bits_controlled(
        model,
        term,
        &decomposed,
        0,
        terms,
        &mut || control.poll(Some(terms)).is_ok(),
    );
    drop(decomposed);
    control.phase(Some(terms), FpEvalPhase::Decode)?;
    Ok(value)
}

#[cfg(test)]
mod tests;
