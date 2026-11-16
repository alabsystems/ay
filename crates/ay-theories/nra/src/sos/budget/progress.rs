// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed proof-wide control; local phase counters never reset this ledger.

use super::*;
use std::fmt;
use std::mem::size_of;

pub(crate) struct SosProgress<'a> {
    callback: &'a mut dyn FnMut(usize, usize) -> bool,
    refused: bool,
}

impl fmt::Debug for SosProgress<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SosProgress")
            .field("refused", &self.refused)
            .finish_non_exhaustive()
    }
}

impl<'a> SosProgress<'a> {
    pub(crate) fn new(callback: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            callback,
            refused: false,
        }
    }

    pub(crate) fn charge(&mut self, work: usize, bytes: usize) -> bool {
        if !self.refused && !(self.callback)(work, bytes) {
            self.refused = true;
        }
        !self.refused
    }

    pub(crate) fn poll(&mut self) -> bool {
        self.charge(0, 0)
    }

    #[cfg(test)]
    pub(crate) fn refused(&self) -> bool {
        self.refused
    }
}

/// Erase only the callback's lifetime, not its sticky state. Short-lived phase
/// budgets borrow this sink without allocating a new shared-control object.
pub(super) trait ProgressSink: fmt::Debug {
    fn charge(&mut self, work: usize, bytes: usize) -> bool;
}

impl ProgressSink for SosProgress<'_> {
    fn charge(&mut self, work: usize, bytes: usize) -> bool {
        self.charge(work, bytes)
    }
}

#[derive(Debug, Default)]
pub(super) struct ProgressHandle<'a>(Option<&'a mut dyn ProgressSink>);

impl<'a> ProgressHandle<'a> {
    pub(super) fn new(progress: &'a mut SosProgress<'_>) -> Self {
        Self(Some(progress))
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> bool {
        self.0
            .as_mut()
            .is_none_or(|progress| progress.charge(work, bytes))
    }

    pub(super) fn array<T>(&mut self, count: usize) -> bool {
        let Some(bytes) = count.checked_mul(2).and_then(|slots| {
            slots
                .max(usize::from(count != 0) * 4)
                .checked_mul(size_of::<T>().saturating_add(32))
        }) else {
            return false;
        };
        self.charge(count, bytes)
    }

    pub(super) fn rational_clone(&mut self, value: &BigRational) -> bool {
        if !rational_fits(value) {
            return false;
        }
        let bits = value.numer().bits() + value.denom().bits();
        self.charge(
            bits.div_ceil(64) as usize + 1,
            bits.div_ceil(8) as usize + size_of::<BigRational>() + 64,
        )
    }

    pub(super) fn rational_operation(&mut self, left: &BigRational, right: &BigRational) -> bool {
        if !rational_fits(left) || !rational_fits(right) {
            return false;
        }
        let bits = left.numer().bits()
            + left.denom().bits()
            + right.numer().bits()
            + right.denom().bits()
            + 2;
        // Cover the bounded products, addition and reduction scratch of
        // num-rational/num-bigint before entering an exact operation.
        self.charge(
            bits.div_ceil(64) as usize + 1,
            32 * bits.div_ceil(8) as usize + 32 * size_of::<BigRational>(),
        )
    }

    pub(super) fn polynomial(&mut self, poly: &MultiPoly) -> bool {
        if poly.terms.len() > MAX_SOS_POLY_TERMS {
            return false;
        }
        // Bounded by the term guard above; the checked form states it.
        let work = match poly.terms.len().checked_mul(MAX_SOS_POLY_TERMS) {
            Some(work) => work.checked_mul(MAX_SOS_POLY_DEGREE),
            None => None,
        };
        let Some(work) = work else {
            return false;
        };
        if !self.charge(work, 0) || !polynomial_fits(poly, None) {
            return false;
        }
        if !self.array::<(Vec<TermId>, BigRational)>(poly.terms.len()) {
            return false;
        }
        for (monomial, coefficient) in &poly.terms {
            if !self.array::<TermId>(monomial.len()) || !self.rational_clone(coefficient) {
                return false;
            }
        }
        true
    }
}
