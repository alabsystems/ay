// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed complete-arena equality; never a snapshot reconstruction.

use super::*;

impl TermStore {
    /// Compare every positional raw entry with a borrowed snapshot.
    ///
    /// Both operands' complete owned payloads are priced before each structural
    /// comparison, including unused and malformed entries. Existing copy-byte
    /// prices are added to work to cover byte scans; no bytes are allocated or
    /// charged. Excessive sort depth or checked accounting overflow refuses.
    /// Rational numerators AND denominators compare by raw representation:
    /// numerically equal alternative encodings do not match. Identical malformed
    /// encodings can match, but this authenticates neither terms nor proofs.
    pub fn snapshot_entries_match_with_progress(
        &self,
        entries: &[(TermData, Sort)],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, TermSnapshotError> {
        charge(progress, 1, 0)?;
        if self.len() != entries.len() {
            return Ok(false);
        }
        if entries.len() > u32::MAX as usize {
            return Err(TermSnapshotError::ResourceLimit);
        }
        for (id, (term, sort)) in self.term_ids().zip(entries) {
            charge(progress, 1, 0)?;
            let mut compare_progress = |work: usize, bytes: usize| {
                work.checked_add(bytes)
                    .is_some_and(|work| progress(work, 0))
            };
            meter_entry(self.get(id), self.sort(id), &mut compare_progress)?;
            meter_entry(term, sort, &mut compare_progress)?;
            if !raw_term_eq(self.get(id), term) || self.sort(id) != sort {
                charge(progress, 0, 0)?;
                return Ok(false);
            }
        }
        charge(progress, 0, 0)?;
        Ok(true)
    }
}

fn raw_term_eq(left: &TermData, right: &TermData) -> bool {
    match (left, right) {
        (TermData::Const(Constant::Rational(left)), TermData::Const(Constant::Rational(right))) => {
            // Ratio::eq performs division for some differing encodings. Snapshot
            // identity must not allocate, normalize, or divide by a malformed 0.
            left.0.numer() == right.0.numer() && left.0.denom() == right.0.denom()
        }
        _ => left == right,
    }
}

#[cfg(test)]
mod tests;
