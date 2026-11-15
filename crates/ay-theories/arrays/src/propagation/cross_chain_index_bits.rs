// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bitset the cross-chain filter keeps per array pair: one bit per entry
//! of the sorted select-index list.

/// Fixed-width bitset over the sorted select-index list.
#[derive(Clone)]
pub(super) struct IndexBits(Vec<u64>);

impl IndexBits {
    pub(super) fn empty(n: usize) -> Self {
        // One zeroed word per 64 indices. The reservation is a capacity hint
        // only: if it fails, the pushes grow the vector as they go.
        let words = n.div_ceil(64);
        let mut bits = Vec::new();
        let _ = bits.try_reserve_exact(words);
        for _ in 0..words {
            bits.push(0);
        }
        Self(bits)
    }
    pub(super) fn set(&mut self, pos: usize) {
        self.0[pos / 64] |= 1u64 << (pos % 64);
    }
    pub(super) fn get(&self, pos: usize) -> bool {
        self.0[pos / 64] & (1u64 << (pos % 64)) != 0
    }
    pub(super) fn and(&self, other: &IndexBits) -> IndexBits {
        IndexBits(self.0.iter().zip(&other.0).map(|(a, b)| a & b).collect())
    }
    pub(super) fn any(&self) -> bool {
        self.0.iter().any(|w| *w != 0)
    }
}
