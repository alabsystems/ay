// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Epoch-stamped dense index sets for the LRA solver's hot per-backtrack paths.

/// Indices below this limit are stamped in the dense sets' `stamps` table
/// (at most 128 MiB of `u32` stamps). An index at or above it — far beyond any
/// real row or variable count — is still a valid member: it is kept only in
/// `entries`, and its membership is decided by scanning that list.
pub(crate) const DENSE_SET_STAMP_LIMIT: usize = 1 << 25;

/// #inc-dense-sets: epoch-stamped set of dense `usize` indices (rows/vars),
/// replacing `HashSet<usize>` on hot per-backtrack paths where SipHash was
/// pure overhead. `insert`/`contains` are O(1) array ops; `clear` is an O(1)
/// epoch bump (stamps re-zeroed once per 2^32 clears); iteration walks the
/// deduplicated insertion-order `entries` list (more deterministic than
/// HashSet order). API mirrors the `HashSet` subset used by callers, and
/// `Default` starts at epoch 1 so `std::mem::take` leaves a valid empty set.
#[derive(Debug, Clone)]
pub(crate) struct DenseIdxSet {
    stamps: Vec<u32>,
    epoch: u32,
    entries: Vec<usize>,
}

impl Default for DenseIdxSet {
    fn default() -> Self {
        Self {
            stamps: Vec::new(),
            epoch: 1,
            entries: Vec::new(),
        }
    }
}

impl DenseIdxSet {
    #[inline]
    pub(crate) fn insert(&mut self, idx: usize) -> bool {
        if idx >= DENSE_SET_STAMP_LIMIT {
            if self.entries.contains(&idx) {
                return false;
            }
            self.entries.push(idx);
            return true;
        }
        if idx >= self.stamps.len() {
            self.stamps.resize(idx + 1, 0);
        }
        if self.stamps[idx] == self.epoch {
            return false;
        }
        self.stamps[idx] = self.epoch;
        self.entries.push(idx);
        true
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            // Wrap once per 2^32 clears: re-zero so no stale stamp matches.
            for s in self.stamps.iter_mut() {
                *s = 0;
            }
            self.epoch = 1;
        }
    }

    #[inline]
    pub(crate) fn iter(&self) -> std::slice::Iter<'_, usize> {
        self.entries.iter()
    }

    #[inline]
    pub(crate) fn extend<I>(&mut self, it: I)
    where
        I: IntoIterator,
        I::Item: std::borrow::Borrow<usize>,
    {
        use std::borrow::Borrow;
        for i in it {
            self.insert(*i.borrow());
        }
    }
}

impl<'a> IntoIterator for &'a DenseIdxSet {
    type Item = &'a usize;
    type IntoIter = std::slice::Iter<'a, usize>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

/// #inc-dense-sets: `u32`-keyed twin of [`DenseIdxSet`] for dense variable
/// ids (`propagation_dirty_vars` etc.). Same epoch-stamp design; see above.
#[derive(Debug, Clone)]
pub(crate) struct DenseU32Set {
    stamps: Vec<u32>,
    epoch: u32,
    entries: Vec<u32>,
}

impl Default for DenseU32Set {
    fn default() -> Self {
        Self {
            stamps: Vec::new(),
            epoch: 1,
            entries: Vec::new(),
        }
    }
}

impl DenseU32Set {
    /// Test-only membership probe (production paths never query membership;
    /// they rely on `insert`'s return value).
    #[cfg(test)]
    #[inline]
    pub(crate) fn contains(&self, v: &u32) -> bool {
        let i = *v as usize;
        if i >= DENSE_SET_STAMP_LIMIT {
            return self.entries.contains(v);
        }
        i < self.stamps.len() && self.stamps[i] == self.epoch
    }

    #[inline]
    pub(crate) fn insert(&mut self, v: u32) -> bool {
        let i = v as usize;
        if i >= DENSE_SET_STAMP_LIMIT {
            if self.entries.contains(&v) {
                return false;
            }
            self.entries.push(v);
            return true;
        }
        if i >= self.stamps.len() {
            self.stamps.resize(i + 1, 0);
        }
        if self.stamps[i] == self.epoch {
            return false;
        }
        self.stamps[i] = self.epoch;
        self.entries.push(v);
        true
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            for s in self.stamps.iter_mut() {
                *s = 0;
            }
            self.epoch = 1;
        }
    }

    #[inline]
    pub(crate) fn iter(&self) -> std::slice::Iter<'_, u32> {
        self.entries.iter()
    }

    #[inline]
    pub(crate) fn extend<I>(&mut self, it: I)
    where
        I: IntoIterator,
        I::Item: std::borrow::Borrow<u32>,
    {
        use std::borrow::Borrow;
        for v in it {
            self.insert(*v.borrow());
        }
    }
}

impl<'a> IntoIterator for &'a DenseU32Set {
    type Item = &'a u32;
    type IntoIter = std::slice::Iter<'a, u32>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}
