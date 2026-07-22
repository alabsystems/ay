// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Tests for the execute_direct panic-boundary helper (#6329).
//!
//! Verifies that `catch_execute_stage` correctly classifies panics:
//! - ay-internal panics (sort mismatch, BUG: markers, etc.) degrade to the
//!   caller-supplied fallback
//! - non-ay panics (index out of bounds, assertions) propagate via
//!   `resume_unwind`

use super::catch_execute_stage;

// ============================================================================
// Test 1: ay-classified panic is downgraded
// ============================================================================

#[test]
fn test_ay_sort_mismatch_panic_downgraded() {
    let result: Result<i32, String> = catch_execute_stage(
        || panic!("sort mismatch: expected Bool, got Int"),
        |reason| Err(reason),
    );
    assert!(result.is_err(), "ay panic should be caught and downgraded");
    let err = result.unwrap_err();
    assert!(
        err.contains("sort mismatch"),
        "should preserve panic message, got: {err}"
    );
}

#[test]
fn test_ay_conflict_verification_panic_downgraded() {
    let result: Result<i32, String> = catch_execute_stage(
        || panic!("Theory conflict verification failed in check(): invalid clause"),
        |reason| Err(reason),
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.contains("conflict verification failed"), "got: {err}");
}

#[test]
fn test_ay_farkas_panic_downgraded() {
    let result: Result<i32, String> = catch_execute_stage(
        || panic!("Farkas semantic verification failed: coefficients mismatch"),
        |reason| Err(reason),
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("Farkas semantic verification failed"),
        "got: {err}"
    );
}

// ============================================================================
// Test 2: non-ay panic propagates
// ============================================================================

#[test]
fn test_index_out_of_bounds_propagates() {
    let outer = std::panic::catch_unwind(|| {
        let _: Result<i32, String> = catch_execute_stage(
            || panic!("index out of bounds: the len is 3 but the index is 5"),
            |reason| Err(reason),
        );
    });
    assert!(
        outer.is_err(),
        "non-ay panics must propagate through catch_execute_stage"
    );
    let payload = outer.unwrap_err();
    let reason = ay_core::panic_payload_to_string(&*payload);
    assert!(
        reason.contains("index out of bounds"),
        "re-raised panic should preserve original message, got: {reason}"
    );
}

#[test]
fn test_assertion_failure_propagates() {
    let outer = std::panic::catch_unwind(|| {
        let _: Result<i32, String> =
            catch_execute_stage(|| panic!("assertion failed: x > 0"), |reason| Err(reason));
    });
    assert!(outer.is_err(), "assertion failures must propagate");
}

// ============================================================================
// Test 3: bug-marker boundary
// ============================================================================

#[test]
fn test_bug_marker_is_downgraded() {
    // "BUG:" prefix (non-word boundary) is a ay-internal marker
    let result: Result<i32, String> =
        catch_execute_stage(|| panic!("BUG: unexpected term kind"), |reason| Err(reason));
    assert!(result.is_err(), "BUG: panic should be downgraded");
    let err = result.unwrap_err();
    assert!(err.contains("BUG:"), "got: {err}");
}

#[test]
fn test_wrapped_bug_marker_is_downgraded() {
    let result: Result<i32, String> = catch_execute_stage(
        || panic!("wrapped bug: unexpected term kind"),
        |reason| Err(reason),
    );
    assert!(result.is_err(), "wrapped BUG: panic should be downgraded");
}

#[test]
fn test_debug_prefix_propagates() {
    // "debug:" contains "bug:" as substring but should NOT match (#1909)
    let outer = std::panic::catch_unwind(|| {
        let _: Result<i32, String> =
            catch_execute_stage(|| panic!("debug: some info"), |reason| Err(reason));
    });
    assert!(
        outer.is_err(),
        "debug-prefixed panics must propagate (not be treated as ay BUG:)"
    );
}

// ============================================================================
// Test 4: non-panicking closure passes through
// ============================================================================

#[test]
fn test_success_passes_through() {
    let result: Result<i32, String> = catch_execute_stage(|| Ok(42), |reason| Err(reason));
    assert_eq!(result, Ok(42));
}
