// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Error types for the ay-bindings fallible API.
//!
//! Consumers that need to handle sort mismatches without panicking can use
//! the `try_*` variants of expression and constraint constructors, which
//! return `Result<T, SortError>` instead of panicking on sort violations.
//!
//! ## Migration from `catch_unwind`
//!
//! Before (catches panics from sort-checking asserts):
//! ```text
//! let result = std::panic::catch_unwind(|| {
//!     let sum = x.bvadd(y);
//!     program.assert(sum.eq(z));
//! });
//! ```
//!
//! After (explicit error handling):
//! ```text
//! let sum = x.try_bvadd(y)?;
//! program.try_assert(sum.try_eq(z)?)?;
//! ```

/// Error returned by `try_*` methods when a sort constraint is violated.
///
/// Every expression operation in ay-bindings has sort preconditions (e.g.,
/// `bvadd` requires both operands to be BitVec with matching widths). The
/// panicking API enforces these with `assert!`; the fallible `try_*` API
/// returns this error instead.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum SortError {
    /// A sort precondition was not met.
    ///
    /// `operation` names the method (e.g., `"bvadd"`),
    /// `expected` describes the required sort(s),
    /// `actual` describes what was provided.
    #[error("{operation}: expected {expected}, got {actual}")]
    Mismatch {
        operation: &'static str,
        expected: &'static str,
        actual: String,
    },
    /// A stack operation exceeded the available context depth.
    ///
    /// Returned by `try_pop` when `levels` exceeds the current context level.
    #[error("{operation}: cannot pop {requested} levels, only {available} available")]
    StackUnderflow {
        operation: &'static str,
        requested: u32,
        available: u32,
    },
}

impl SortError {
    /// Create a mismatch error for a unary operation.
    pub(crate) fn unary(
        operation: &'static str,
        expected: &'static str,
        actual: &crate::Sort,
    ) -> Self {
        Self::Mismatch {
            operation,
            expected,
            actual: actual.to_string(),
        }
    }

    /// Create a mismatch error for a binary operation.
    pub(crate) fn binary(
        operation: &'static str,
        expected: &'static str,
        left: &crate::Sort,
        right: &crate::Sort,
    ) -> Self {
        Self::Mismatch {
            operation,
            expected,
            actual: format!("{left} and {right}"),
        }
    }
}

#[cfg(test)]
#[path = "error_tests.rs"]
mod tests;
