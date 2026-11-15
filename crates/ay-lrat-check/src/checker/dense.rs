// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fallible dense array storage for the LRAT checker.

use std::collections::TryReserveError;

/// The dense arrays indexed by variable or by literal code, allocated
/// together by [`super::LratChecker::with_strict`].
#[derive(Default)]
pub(super) struct DenseArrays {
    pub(super) assigns: Vec<Option<bool>>,
    pub(super) marks: Vec<bool>,
    pub(super) checked_lits: Vec<bool>,
    pub(super) occ_lists: Vec<Vec<u64>>,
}

impl DenseArrays {
    /// Allocate `universe` variable slots and `lit_slots` literal slots, or
    /// report the allocator's refusal instead of aborting the process.
    pub(super) fn try_alloc(universe: usize, lit_slots: usize) -> Result<Self, TryReserveError> {
        Ok(Self {
            assigns: try_filled(None, universe)?,
            marks: try_filled(false, lit_slots)?,
            checked_lits: try_filled(false, lit_slots)?,
            occ_lists: try_filled(Vec::new(), lit_slots)?,
        })
    }
}

/// `len` copies of `elem`: `vec![elem; len]` with a fallible allocation.
///
/// The buffer is reserved up front with `try_reserve_exact`, so filling it
/// never reallocates.
pub(super) fn try_filled<T: Clone>(elem: T, len: usize) -> Result<Vec<T>, TryReserveError> {
    let mut filled = Vec::new();
    filled.try_reserve_exact(len)?;
    filled.extend(std::iter::repeat_n(elem, len));
    Ok(filled)
}
