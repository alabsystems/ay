// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Atomic cumulative-work accounting; no grant, timer or publication authority.

use std::sync::atomic::{AtomicUsize, Ordering};

use super::MAX_FUNCTIONAL_WORK;

// Storage sentinel, not an extra admitted unit or a grant extension. A value
// above the exact limit must remain refused even when the next debit is zero.
pub(super) const REFUSED: usize = MAX_FUNCTIONAL_WORK + 1;

/// Fold an observed original-owner refusal into shared terminal storage.
/// This admits no unit; concurrent debits cannot roll REFUSED back to healthy.
pub(super) fn refuse(used: &AtomicUsize) {
    used.store(REFUSED, Ordering::Release);
}

pub(super) fn debit(used: &AtomicUsize, amount: usize) -> bool {
    used.try_update(Ordering::AcqRel, Ordering::Acquire, |prior| {
        Some(prior.saturating_add(amount).min(REFUSED))
    })
    .is_ok_and(|prior| {
        prior <= MAX_FUNCTIONAL_WORK && amount <= MAX_FUNCTIONAL_WORK.saturating_sub(prior)
    })
}

#[cfg(test)]
mod owner_stop_tests;
#[cfg(test)]
mod tests;
