// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Zero-allocation lexical traversal under the original borrowed work owner.

use super::{AuthoredSourceError, Scanner, SourceToken};
use ay_core::original_query::WorkBudget;

/// An admitted borrowed traversal of the exact original source bytes.
///
/// No owned token collection, decoding, normalization or byte copy is made.
/// Each consumed byte and yielded token's metadata uses the SAME borrowed work
/// ledger. With `WorkBudget::with_admission`, the original owner receives those
/// actual work debits with zero storage bytes; this cursor owns no heap storage.
/// The compatibility budget still makes no separate storage-budget claim.
///
/// Tokens may be yielded before the whole source is lexically valid. Only a
/// successful `next_token() == Ok(None)` has scanned every byte and passed the
/// final original-owner poll. Neither partial tokens nor EOF establishes command
/// validity, typing, native-host policy, query equivalence or proof authority.
///
/// Errors are sticky for THIS cursor. Dropping it does not transfer a lexical
/// refusal to the external owner; a transaction must stop after refusal. Reusing
/// the same work adapter never resets its resource/cancellation/deadline latch.
pub struct SourceCursor<'source, 'work, 'owner> {
    scanner: Scanner<'source, 'work, 'owner>,
    token_count: usize,
    refusal: Option<AuthoredSourceError>,
}

impl<'source, 'work, 'owner> SourceCursor<'source, 'work, 'owner> {
    /// Begin without allocating, after polling the original borrowed owner.
    ///
    /// The caller retains the original absolute deadline and cumulative grant;
    /// construction does not replace the callback, renew credit or clear stops.
    pub fn new(
        original: &'source str,
        work: &'work mut WorkBudget<'owner>,
    ) -> Result<Self, AuthoredSourceError> {
        work.charge(0)?;
        Ok(Self {
            scanner: Scanner {
                input: original,
                at: 0,
                work,
            },
            token_count: 0,
            refusal: None,
        })
    }

    /// Borrow the unchanged COMPLETE input, not a successfully scanned prefix.
    pub fn original(&self) -> &'source str {
        self.scanner.input
    }

    /// Current byte position; reaching input length alone does not mean success.
    pub fn position(&self) -> usize {
        self.scanner.at
    }

    /// Tokens successfully yielded by this traversal; not complete-query coverage.
    pub fn token_count(&self) -> usize {
        self.token_count
    }

    /// Yield one exact lexical occurrence, or poll before reporting complete EOF.
    ///
    /// A refused suffix is never skipped and never becomes successful EOF.
    /// Long whitespace, comments, strings and identifiers poll per consumed byte.
    pub fn next_token(&mut self) -> Result<Option<SourceToken<'source>>, AuthoredSourceError> {
        if let Some(error) = &self.refusal {
            return Err(error.clone());
        }
        let result = self.scan_next();
        if let Err(error) = &result {
            self.refusal = Some(error.clone());
        }
        result
    }

    /// Price a borrowing parser's own bookkeeping through the SAME work ledger.
    ///
    /// No resource owner is exposed, duplicated or renewed. Refusal remains
    /// sticky even when callers attempt bookkeeping after a lexical error.
    pub(crate) fn charge_work(&mut self, units: usize) -> Result<(), AuthoredSourceError> {
        if let Some(error) = &self.refusal {
            return Err(error.clone());
        }
        let result = self
            .scanner
            .work
            .charge(units)
            .map_err(AuthoredSourceError::from);
        if let Err(error) = &result {
            self.refusal = Some(error.clone());
        }
        result
    }

    fn scan_next(&mut self) -> Result<Option<SourceToken<'source>>, AuthoredSourceError> {
        while self.scanner.at < self.scanner.input.len() {
            let byte = self.scanner.byte();
            if matches!(byte, b' ' | b'\t' | b'\n' | b'\r') {
                self.scanner.advance()?;
                continue;
            }
            if byte == b';' {
                self.scanner.comment()?;
                continue;
            }
            let start = self.scanner.at;
            let kind = self.scanner.token()?;
            self.scanner.work.charge(1)?;
            let count = self
                .token_count
                .checked_add(1)
                .ok_or_else(|| self.scanner.work.refuse_exhaustion())?;
            self.token_count = count;
            return Ok(Some(SourceToken {
                kind,
                raw: &self.scanner.input[start..self.scanner.at],
                span: start..self.scanner.at,
            }));
        }
        self.scanner.work.charge(0)?;
        Ok(None)
    }
}

#[cfg(test)]
mod tests;
