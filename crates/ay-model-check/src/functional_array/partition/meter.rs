// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::FunctionalArrayError;
use std::mem::size_of;

pub(super) struct Meter<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    requested: usize,
    refused: bool,
}

impl<'a> Meter<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            progress,
            requested: 0,
            refused: false,
        }
    }

    pub(super) fn offer(&mut self, work: usize, bytes: usize) -> bool {
        if self.refused {
            return false;
        }
        self.refused = true;
        let Some(total) = self.requested.checked_add(bytes) else {
            return false;
        };
        // The existing topology storage ceiling is shared across all captures
        // and refinement scratch, never multiplied or replenished per export.
        if total > 16 * 1024 * 1024 || !(self.progress)(work, bytes) {
            return false;
        }
        self.requested = total;
        self.refused = false;
        true
    }

    pub(super) fn pay(&mut self, work: usize) -> Result<(), FunctionalArrayError> {
        self.offer(work, 0)
            .then_some(())
            .ok_or(FunctionalArrayError::Resource)
    }

    pub(super) fn poll(&mut self) -> Result<(), FunctionalArrayError> {
        self.pay(0)
    }

    pub(super) fn refuse(&mut self) {
        self.refused = true;
    }

    pub(super) fn reserve<T>(
        &mut self,
        values: &mut Vec<T>,
        extra: usize,
    ) -> Result<(), FunctionalArrayError> {
        self.pay(64)?;
        let needed = values
            .len()
            .checked_add(extra)
            .ok_or(FunctionalArrayError::Resource)?;
        if needed <= values.capacity() {
            return Ok(());
        }
        let bytes = needed
            .checked_mul(size_of::<T>())
            .ok_or(FunctionalArrayError::Resource)?;
        let work = needed
            .checked_add(values.len())
            .and_then(|n| n.checked_mul(size_of::<T>()))
            .and_then(|n| n.checked_mul(4))
            .and_then(|n| n.checked_add(128))
            .ok_or(FunctionalArrayError::Resource)?;
        if !self.offer(work, bytes) {
            return Err(FunctionalArrayError::Resource);
        }
        values
            .try_reserve_exact(extra)
            .map_err(|_| FunctionalArrayError::Allocation)
    }
}
