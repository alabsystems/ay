// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Immutable source inspection after a full independent retained replay.
//! It exposes no proof steps, mutable snapshot or raw-v3 conversion.

use super::*;
use crate::DatatypeMemberSignature;
use ay_core::{Sort, TermData};

/// Borrowed typed data for binding an independently expected problem.
/// This view is not external-source authority: callers must compare every
/// original premise and the complete nominal/free declaration environment.
pub struct RetainedProofSourceView<'a> {
    snapshot: &'a SerializableProofBundle,
}

impl RetainedProofSourceView<'_> {
    /// Positional term count in this exact checked document.
    pub fn term_count(&self) -> usize {
        self.snapshot.term_entries.len()
    }

    /// Exact stored node and sort, without re-interning or printed text.
    pub fn term(&self, term: TermId) -> Option<(&TermData, &Sort)> {
        self.snapshot
            .term_entries
            .get(term.index())
            .map(|(node, sort)| (node, sort))
    }

    /// Compare one exact-id source entry without copying its payload. The
    /// comparison prices both complete borrowed payloads first, including
    /// rational equality work; it does not traverse child term handles.
    pub fn term_matches_with_resource_control(
        &self,
        term: TermId,
        expected: (&TermData, &Sort),
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, ProofCheckError> {
        let Some(actual) = self.term(term) else {
            return Ok(false);
        };
        super::super::preflight_canonical::borrowed_entries_equal(expected, actual, progress)
    }

    pub fn obligations(&self) -> &[TermId] {
        &self.snapshot.obligation_assertions
    }

    pub fn datatype_declarations(&self) -> &[(String, Vec<String>)] {
        &self.snapshot.datatype_declarations
    }

    pub fn constructor_selectors(&self) -> &[(String, Vec<String>)] {
        &self.snapshot.constructor_selectors
    }

    pub fn datatype_member_signatures(&self) -> &[DatatypeMemberSignature] {
        &self.snapshot.datatype_member_signatures
    }
}

impl RetainedProofBundle {
    /// Fully replay before inspecting immutable source data. The visitor must
    /// bind its independently obtained expected query, not trust serialized
    /// names, ids or digests. All visitor-owned copies and comparisons must
    /// debit the supplied callback, which shares the original retained owner.
    /// There is no proof-search fallback or replacement evidence on failure.
    ///
    /// The visitor may read source terms and typed datatype context but cannot
    /// detach proof steps from the mandatory v4 payload inventory. Arbitrary
    /// work performed by caller code is the caller's accounting responsibility.
    pub fn with_checked_source_view_with_resource_control<T>(
        &self,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
        inspect: impl FnOnce(
            RetainedProofSourceView<'_>,
            BundleReCheck,
            &mut dyn FnMut(usize, usize) -> bool,
        ) -> Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        let deadline = self.deadline.min(deadline);
        control::run(deadline, progress, |control| {
            let checked = self.replay(deadline, control)?;
            let (snapshot, _) = self.envelope.parts();
            let result = inspect(
                RetainedProofSourceView { snapshot },
                checked,
                &mut |work, bytes| control.charge(work, bytes).is_ok(),
            );
            control.charge(0, 0)?;
            result
        })
    }
}
