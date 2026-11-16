// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared resource accounting for exact-query export, without proof authority.

use ay_core::TermId;
use ay_proof::ProofCheckError;
use std::mem::size_of;

pub(super) struct Control<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    refused: bool,
}

impl<'a> Control<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            progress,
            refused: false,
        }
    }

    /// Latch before invoking user code, including a callback panic caught by
    /// an inner operation. Refusal never calls the callback again.
    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.refused = true;
        if (self.progress)(work, bytes) {
            self.refused = false;
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    pub(super) fn run<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        self.charge(0, 0)?;
        let result = operation(self);
        if matches!(&result, Err(ProofCheckError::ResourceLimit)) {
            return self.refuse();
        }
        // #completed-check-accepted: consult the LATCH, not the caller. A
        // refusal the export observed stays final even behind an inner guard
        // that swallowed it; a stop that arrives after the export's last
        // callback cannot discard a bundle both strict re-checks accepted.
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        result
    }

    /// Retained export owns an original-clock publication boundary after
    /// operation-local source owners drop. This is not the legacy v3 check's
    /// completed-verdict contract: retained evidence must still be admitted
    /// under the caller's same sticky callback before it escapes this lane.
    pub(super) fn run_retained<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        let result = self.run(operation);
        // An observed refusal is already latched, so charge does not re-enter
        // user code. A late refusal drops the still-owned result on this exit.
        self.charge(0, 0)?;
        result
    }

    #[cfg(test)]
    pub(super) fn copy_ids(&mut self, source: &[TermId]) -> Result<Vec<TermId>, ProofCheckError> {
        let mut copied = self.reserve_ids(source.len())?;
        // reserve_ids prepaid both the complete traversal and output storage.
        copied.extend_from_slice(source);
        self.charge(0, 0)?;
        Ok(copied)
    }

    /// Preserve first-use order and reserve at most one output slot per input.
    /// Quadratic comparison work is explicit; no unpriced hash table is used.
    pub(super) fn ordered_unique_ids(
        &mut self,
        source: &[TermId],
    ) -> Result<Vec<TermId>, ProofCheckError> {
        let mut unique = self.reserve_ids(source.len())?;
        for &id in source {
            self.charge(1, 0)?;
            if !self.contains_id(&unique, id)? {
                unique.push(id);
            }
        }
        self.charge(0, 0)?;
        Ok(unique)
    }

    /// Pure membership, not authentication: empty input is vacuously included.
    pub(super) fn all_ids_in(
        &mut self,
        source: &[TermId],
        allowed: &[TermId],
    ) -> Result<bool, ProofCheckError> {
        self.charge(0, 0)?;
        for &id in source {
            self.charge(1, 0)?;
            if !self.contains_id(allowed, id)? {
                self.charge(0, 0)?;
                return Ok(false);
            }
        }
        self.charge(0, 0)?;
        Ok(true)
    }

    fn contains_id(&mut self, values: &[TermId], id: TermId) -> Result<bool, ProofCheckError> {
        for &candidate in values {
            self.charge(1, 0)?;
            if candidate == id {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn reserve_ids(&mut self, len: usize) -> Result<Vec<TermId>, ProofCheckError> {
        self.charge(1, 0)?;
        let Some(bytes) = len.checked_mul(size_of::<TermId>()) else {
            return self.refuse();
        };
        self.charge(len, bytes)?;
        let mut output = Vec::new();
        if output.try_reserve_exact(len).is_err() {
            return self.refuse();
        }
        Ok(output)
    }

    fn refuse<T>(&mut self) -> Result<T, ProofCheckError> {
        self.refused = true;
        Err(ProofCheckError::ResourceLimit)
    }
}

#[cfg(test)]
mod tests;
