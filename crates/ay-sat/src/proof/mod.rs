// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT and LRAT proof generation for UNSAT certificates
//!
//! ## DRAT
//!
//! DRAT (Deletion Resolution Asymmetric Tautology) proofs provide a way to verify
//! that an UNSAT result is correct. Every learned clause and deletion is logged,
//! and can be verified by tools like drat-trim.
//!
//! ## LRAT
//!
//! LRAT (Linear Resolution Asymmetric Tautology) extends DRAT with clause IDs
//! and resolution hints. This enables linear-time proof checking (vs quadratic
//! for DRAT), making verification much faster for large proofs.
//!
//! ## Format
//!
//! **DRAT Text format:**
//! ```text
//! 1 2 -3 0        # add clause (1 OR 2 OR -3)
//! d 1 2 0         # delete clause (1 OR 2)
//! ```
//!
//! **DRAT Binary format:**
//! - 'a' byte (0x61) followed by literals then 0 for addition
//! - 'd' byte (0x64) followed by literals then 0 for deletion
//! - Literals encoded as LEB128-style variable-length integers
//!
//! **LRAT Text format:**
//! ```text
//! 4 1 2 0 1 2 3 0    # add clause 4: (1 OR 2) with hints 1,2,3
//! 5 d 1 2 0          # delete clauses 1 and 2 (latest ID is 5)
//! ```
//!
//! **LRAT Binary format:**
//! - 'a' byte followed by binary_id, binary_lits..., 0, binary_hints..., 0
//!
//! ## VeriPB
//!
//! VeriPB is a pseudo-Boolean proof checker on the official SAT-COMP 2026
//! checker menu whose `red` rule carries a substitution witness natively, so
//! AY's SR-witnessed symmetry steps are representable there without the
//! DSR-only `a`-line encoding that all DRAT-family checkers except `dsr-trim`
//! reject. See [`veripb`] for the rule mapping.
//! - 'd' byte followed by binary_ids..., 0

mod drat;
mod emission;
mod lrat;
mod output;
#[cfg(test)]
mod tests;
mod veripb;
#[cfg(all(test, unix))]
mod write_failure_tests;

pub use drat::DratWriter;
pub(crate) use emission::{bounded_emission_cancelled, is_bounded_emission_cancelled};
pub(crate) use lrat::LratBoundedResourceFailure;
pub use lrat::{LratWriter, MAX_LRAT_ORIGINAL_CLAUSES};
pub use output::ProofOutput;
pub(crate) use veripb::literal_key as veripb_literal_key;
pub use veripb::VeripbWriter;

use crate::literal::Literal;
use std::any::Any;
use std::io::{self, Write};

/// Type-erased writer that supports downcasting back to the original type.
///
/// Used by `ProofOutput` to erase the writer type parameter from `DratWriter`
/// and `LratWriter` while still allowing extraction of the underlying `Vec<u8>`
/// in tests (via `into_vec()`).
///
/// Every proof sink's bytes pass through here, so this is also where the first
/// write or flush failure is kept: the format writers latch a bare flag and go
/// silent after it, and without this the cause (for example "No space left on
/// device (os error 28)") would be lost before anyone could report it.
pub struct BoxedWriter {
    inner: Box<dyn WriteAndAny + Send>,
    first_error: Option<ProofWriteError>,
}

/// The first failure a proof sink reported, kept by [`BoxedWriter`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofWriteError {
    pub(crate) kind: io::ErrorKind,
    pub(crate) raw_os_error: Option<i32>,
    pub(crate) message: String,
}

impl std::fmt::Display for ProofWriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::fmt::Debug for BoxedWriter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoxedWriter").finish_non_exhaustive()
    }
}

/// Internal trait combining `Write` with `Any`-based downcasting.
trait WriteAndAny: Write + Send {
    fn into_any(self: Box<Self>) -> Box<dyn Any>;
}

impl<T: Write + Send + 'static> WriteAndAny for T {
    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

impl BoxedWriter {
    /// Wrap any writer into a `BoxedWriter`.
    pub fn new(writer: impl Write + Send + 'static) -> Self {
        Self {
            inner: Box::new(writer),
            first_error: None,
        }
    }

    /// The first write or flush failure the sink reported, if any.
    pub(crate) fn first_error(&self) -> Option<&ProofWriteError> {
        self.first_error.as_ref()
    }

    /// Keep the first real failure; `Interrupted` is retried by `write_all`
    /// and is not a failure of the sink.
    fn record<T>(&mut self, result: io::Result<T>) -> io::Result<T> {
        if let Err(error) = &result {
            if self.first_error.is_none() && error.kind() != io::ErrorKind::Interrupted {
                self.first_error = Some(ProofWriteError {
                    kind: error.kind(),
                    raw_os_error: error.raw_os_error(),
                    message: error.to_string(),
                });
            }
        }
        result
    }

    /// Attempt to extract a `Vec<u8>` from this writer.
    ///
    /// Returns `None` if the underlying writer is not a `Vec<u8>`.
    /// Panics are avoided — callers should use `.expect()` in test code.
    pub fn into_vec(self) -> Option<Vec<u8>> {
        self.into_typed::<Vec<u8>>()
    }

    /// Recover a crate-internal concrete writer after type erasure.
    ///
    /// Production proof consumers use this to retain ownership of bounded
    /// in-memory writers without a shared mutex on every emitted byte.
    pub(crate) fn into_typed<T: Write + Send + 'static>(self) -> Option<T> {
        self.inner
            .into_any()
            .downcast::<T>()
            .ok()
            .map(|boxed| *boxed)
    }
}

// Compile-time assertion: BoxedWriter must be Send for cross-thread use (#5891).
const _: () = {
    const fn assert_send<T: Send>() {}
    assert_send::<BoxedWriter>();
};

impl Write for BoxedWriter {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let result = self.inner.write(buf);
        self.record(result)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        let result = self.inner.flush();
        self.record(result)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        let result = self.inner.write_all(buf);
        self.record(result)
    }
}

/// Returns true if clause contains duplicate literals (same variable+polarity).
/// Only called from `debug_assert!()` — dead-code eliminated in release builds.
pub(super) fn has_duplicate_literal(clause: &[Literal]) -> bool {
    // O(n²) is acceptable for debug mode; SAT clauses are typically short.
    for i in 0..clause.len() {
        for j in (i + 1)..clause.len() {
            if clause[i] == clause[j] {
                return true;
            }
        }
    }
    false
}

/// Extension trait for literals to convert to DIMACS format
pub(super) trait ToDimacs {
    /// Convert to DIMACS format (1-indexed, negative for negated)
    fn to_dimacs(&self) -> i32;
}

impl ToDimacs for Literal {
    #[allow(clippy::use_self)] // Explicit type disambiguates inherent from trait method
    fn to_dimacs(&self) -> i32 {
        Literal::to_dimacs(*self)
    }
}
