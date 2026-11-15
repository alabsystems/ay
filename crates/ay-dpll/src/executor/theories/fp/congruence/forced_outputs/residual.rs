// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded, original-order residual pairs; no candidate-model observations.

use super::{Application, TseitinResult, Work};
use crate::executor::theories::fp::congruence::MAX_RESIDUAL_PAIRS;

fn count([negative, unknown, positive]: [usize; 3]) -> Option<usize> {
    let opposite = negative.checked_mul(positive)?;
    let mixed = unknown.checked_mul(negative.checked_add(positive)?)?;
    let unforced = unknown.checked_mul(unknown.saturating_sub(1))? / 2;
    opposite.checked_add(mixed)?.checked_add(unforced)
}

// The parent supplies the exact census from its full mapping/sort admission.
// This is not an independent authority accepting arbitrary caller counts.
pub(super) fn pairs<E>(
    tseitin: &TseitinResult,
    values: &[i8],
    group: &[Application],
    counts: [usize; 3],
    work: &mut Work,
    check: &mut dyn FnMut() -> Result<(), E>,
) -> Result<Option<Vec<(usize, usize)>>, E> {
    let Some(count) = count(counts) else {
        return Ok(None);
    };
    // Preserve the uniform fast path: no pair scan, allocation or new debit.
    if count == 0 {
        return Ok(Some(Vec::new()));
    }
    if count > MAX_RESIDUAL_PAIRS || !work.debit(count * 2) {
        return Ok(None);
    }
    check()?;
    let mut pairs = Vec::new();
    if pairs.try_reserve_exact(count).is_err() {
        return Ok(None);
    }
    // Each pair retains two indices. Charge allocator excess before use too.
    let Some(excess) = pairs
        .capacity()
        .checked_sub(count)
        .and_then(|n| n.checked_mul(2))
    else {
        return Ok(None);
    };
    if !work.debit(excess) {
        return Ok(None);
    }
    for i in 0..group.len() {
        check()?;
        for j in (i + 1)..group.len() {
            check()?;
            if !work.debit(1) {
                return Ok(None);
            }
            // The caller has already admitted both exact mappings. Borrow the
            // immutable closure again instead of allocating a polarity cache.
            let polarity = |index: usize| {
                tseitin
                    .var_for_term(group[index].0)
                    .and_then(|variable| values.get(variable as usize))
                    .copied()
            };
            let (Some(a), Some(b)) = (polarity(i), polarity(j)) else {
                return Ok(None);
            };
            if a == 0 || a != b {
                // Never grow beyond the fully admitted count, even if the
                // private caller's census and immutable mappings disagree.
                if pairs.len() == count {
                    return Ok(None);
                }
                pairs.push((i, j));
            }
        }
    }
    check()?;
    Ok((pairs.len() == count).then_some(pairs))
}

#[cfg(test)]
#[path = "residual/tests.rs"]
mod tests;
