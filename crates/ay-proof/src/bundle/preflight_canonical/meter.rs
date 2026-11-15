// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental charges for this index's own allocations and scalar operations.

use std::mem::size_of;

use super::*;

pub(super) struct CanonicalMeter<'a> {
    progress: Progress<'a>,
}

impl<'a> CanonicalMeter<'a> {
    pub(super) fn new(progress: Progress<'a>) -> Self {
        Self { progress }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    pub(super) fn map_lookup(&mut self, entries: usize) -> Result<(), ProofCheckError> {
        // BTree's fixed-width u64 keys have no payload-dependent comparison.
        let levels = add((usize::BITS - entries.leading_zeros()) as usize, 1)?;
        self.charge(mul(levels, 12)?, 0)
    }

    pub(super) fn map_entry<T>(&mut self, entries: usize) -> Result<(), ProofCheckError> {
        // alloc's B=6 node has 11 keys and 12 edges. A split can allocate one
        // sibling per level plus a root. This prices actual own-table height
        // conservatively; no assumption relates bucket count to live terms.
        let nodes = add((usize::BITS - entries.leading_zeros()) as usize, 2)?;
        let slots = mul(nodes, 32)?;
        self.charge(slots, mul(slots, add(size_of::<T>(), size_of::<usize>())?)?)
    }

    pub(super) fn vector_room<T>(&mut self, values: &mut Vec<T>) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if values.len() == values.capacity() {
            let capacity = mul(values.capacity().max(2), 2)?;
            let bytes = mul(capacity, size_of::<T>())?;
            self.charge(add(bytes, 1)?, bytes)?;
            values
                .try_reserve_exact(capacity - values.len())
                .map_err(|_| ProofCheckError::ResourceLimit)?;
        }
        Ok(())
    }

    pub(super) fn zero_limbs(&mut self, len: usize) -> Result<Vec<u32>, ProofCheckError> {
        let bytes = mul(len, size_of::<u32>())?;
        self.charge(add(len, 1)?, bytes)?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(len)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        values.resize(len, 0);
        Ok(values)
    }
}

pub(super) fn add(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

pub(super) fn mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}
