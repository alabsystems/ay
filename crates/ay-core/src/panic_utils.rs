// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared panic classification and boundary helpers for ay consumers.
//!
//! This module provides the canonical producer-side API for handling ay solver
//! panics. Consumers (verification-consumer, deductive-checks, model-checker-consumer) previously duplicated this logic;
//! this module is the single source of truth.
//!
//! # Public API
//!
//! - [`panic_payload_to_string`] — extract a human-readable message from a
//!   caught panic payload.
//! - [`is_ay_panic_reason`] — classify whether a panic reason string
//!   originated from ay solver internals.
//! - [`catch_ay_panics`] — generic unwind boundary that catches ay panics and
//!   re-raises all others via `resume_unwind`.
//!
//! # Design
//!
//! The helpers are generic over the caller's return type. Consumers map ay
//! panics into their own result/error types via the `on_ay_panic` callback.
//! See the development design notes.

use std::any::Any;
use std::panic::{catch_unwind, resume_unwind, UnwindSafe};

/// Extract a human-readable message from a panic payload.
///
/// When using `catch_unwind`, the caught payload is an opaque
/// `Box<dyn Any + Send>`. This utility extracts the message string, handling
/// the two common payload types (`&str` and `String`).
///
/// Consolidates the pattern previously duplicated in ay-dpll, ay-bindings,
/// neural-verification-consumer, and model-checker-consumer (see issue #5344).
pub fn panic_payload_to_string(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

/// Returns `true` if the panic reason string matches known ay internal panic
/// patterns.
///
/// AY internal panics include sort mismatches, model validation errors, term
/// construction failures, theory conflict verification failures, and Farkas
/// semantic verification failures. These are gracefully degraded by consumers
/// rather than propagated as crashes.
///
/// Returns `false` for generic runtime panics (index out of bounds, assertion
/// failures, etc.) which represent programmer errors and should propagate.
///
/// # Matched patterns
///
/// - `"sort mismatch"` (case-insensitive)
/// - `"sortmismatch"` in compact form (whitespace-stripped, catches
///   thiserror Debug payloads like `SortMismatch { ... }`)
/// - `"expects bool, got"` (case-insensitive)
/// - `"BUG:"` with non-word boundary (rejects `"debug:"`, `"user_bug:"`)
/// - `"conflict verification failed"` (case-insensitive)
/// - `"farkas semantic verification failed"` (case-insensitive)
pub fn is_ay_panic_reason(reason: &str) -> bool {
    let reason_lower = reason.to_lowercase();
    let reason_compact: String = reason_lower
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect();
    reason_lower.contains("sort mismatch")
        || reason_compact.contains("sortmismatch")
        || reason_lower.contains("expects bool, got")
        || contains_bug_marker(&reason_lower)
        || reason_lower.contains("conflict verification failed")
        || reason_lower.contains("farkas semantic verification failed")
}

/// Generic unwind boundary that catches ay panics and re-raises all others.
///
/// Runs `f` inside `catch_unwind`. If `f` succeeds, returns the inner value
/// unchanged. If `f` panics with a ay-classified reason (per
/// [`is_ay_panic_reason`]), calls `on_ay_panic(reason_string)` and returns
/// its result. If the panic is not ay-classified, re-raises it via
/// `resume_unwind` so programmer errors propagate normally.
///
/// The return type is fully generic — consumers map ay panics into their own
/// result/error types via the `on_ay_panic` callback.
///
/// # Examples
///
/// ```
/// use ay_core::catch_ay_panics;
///
/// // Returns Ok for non-panicking closures
/// let result: Result<i32, String> = catch_ay_panics(|| Ok(42), Err);
/// assert_eq!(result, Ok(42));
/// ```
pub fn catch_ay_panics<T, F, G>(f: F, on_ay_panic: G) -> T
where
    F: FnOnce() -> T + UnwindSafe,
    G: FnOnce(String) -> T,
{
    match catch_unwind(f) {
        Ok(value) => value,
        Err(payload) => {
            let reason = panic_payload_to_string(&*payload);
            if is_ay_panic_reason(&reason) {
                on_ay_panic(reason)
            } else {
                resume_unwind(payload);
            }
        }
    }
}

/// Check whether a lowercased panic reason contains a `BUG:` marker from ay
/// internals.
///
/// Matches `"bug: ..."` at string start and `"... bug: ..."` with a non-word
/// boundary preceding it, but rejects embedded tokens like `"debug:"` or
/// `"user_bug:"` that contain `"bug:"` as a substring.
fn contains_bug_marker(reason_lower: &str) -> bool {
    reason_lower.match_indices("bug:").any(|(pos, _)| {
        if pos == 0 {
            return true;
        }
        reason_lower[..pos]
            .chars()
            .next_back()
            .is_some_and(|c| !c.is_alphanumeric() && c != '_')
    })
}

#[cfg(test)]
#[path = "panic_utils_tests.rs"]
mod tests;
