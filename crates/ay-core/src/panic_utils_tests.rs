// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::panic::AssertUnwindSafe;

// ========================================================================
// panic_payload_to_string tests
// ========================================================================

#[test]
fn test_payload_str() {
    let payload: Box<dyn Any + Send> = Box::new("sort mismatch");
    assert_eq!(panic_payload_to_string(&*payload), "sort mismatch");
}

#[test]
fn test_payload_string() {
    let payload: Box<dyn Any + Send> = Box::new(String::from("BUG: mk_eq failed"));
    assert_eq!(panic_payload_to_string(&*payload), "BUG: mk_eq failed");
}

#[test]
fn test_payload_non_string() {
    let payload: Box<dyn Any + Send> = Box::new(42i32);
    assert_eq!(panic_payload_to_string(&*payload), "unknown panic");
}

// ========================================================================
// is_ay_panic_reason tests — ported from deductive-checks and verification-consumer test corpus
// ========================================================================

#[test]
fn test_sort_mismatch() {
    assert!(is_ay_panic_reason(
        "sort mismatch: expected Bool, got BV(8)"
    ));
    assert!(is_ay_panic_reason("Sort Mismatch in term construction"));
    assert!(is_ay_panic_reason("SORT MISMATCH"));
}

#[test]
fn test_sort_mismatch_thiserror_debug() {
    // thiserror Debug payload shape from unwrap panic context
    assert!(is_ay_panic_reason(
        "called `Result::unwrap()` on an `Err` value: SortMismatch { operation: \"try_bvadd\", expected: \"BV\", got: [Bool, BitVec(BitVecSort { width: 8 })] }"
    ));
}

#[test]
fn test_expects_bool() {
    assert!(is_ay_panic_reason("expects Bool, got BV(32)"));
    assert!(is_ay_panic_reason("Term expects Bool, got Int"));
}

#[test]
fn test_bug_prefix() {
    assert!(is_ay_panic_reason(
        "BUG: mk_eq called with non-matching sorts"
    ));
    assert!(is_ay_panic_reason("BUG: unexpected term kind"));
    // BUG: prefixed by wrapper context
    assert!(is_ay_panic_reason(
        "api wrapper panic: BUG: mk_eq called with non-matching sorts"
    ));
}

#[test]
fn test_conflict_verification_failed() {
    assert!(is_ay_panic_reason(
        "Theory conflict verification failed in check(): invalid clause"
    ));
    assert!(is_ay_panic_reason(
        "Theory conflict verification failed in check_theory(): bad lemma"
    ));
    assert!(is_ay_panic_reason(
        "Theory conflict verification failed in incremental LRA: coefficients"
    ));
    assert!(is_ay_panic_reason(
        "Theory conflict verification failed in incremental LIA: bad bound"
    ));
    assert!(is_ay_panic_reason(
        "EUF conflict verification failed in incremental EUF: congruence mismatch"
    ));
}

#[test]
fn test_farkas_semantic_verification_failed() {
    assert!(is_ay_panic_reason(
        "Farkas semantic verification failed in check_theory(): coefficients mismatch"
    ));
    assert!(is_ay_panic_reason(
        "Farkas semantic verification failed in incremental LRA: bad coefficients"
    ));
    assert!(is_ay_panic_reason(
        "Farkas semantic verification failed: internal error"
    ));
    assert!(is_ay_panic_reason(
        "Farkas semantic verification failed in EUF: congruence"
    ));
}

#[test]
fn test_case_insensitive() {
    assert!(is_ay_panic_reason("EXPECTS BOOL, GOT BV(32)"));
    assert!(is_ay_panic_reason("Expects Bool, Got Int"));
    assert!(is_ay_panic_reason(
        "bug: mk_eq called with non-matching sorts"
    ));
    assert!(is_ay_panic_reason("Bug: unexpected term kind"));
    assert!(is_ay_panic_reason(
        "CONFLICT VERIFICATION FAILED in check()"
    ));
    assert!(is_ay_panic_reason(
        "Theory Conflict Verification Failed in check_theory()"
    ));
    assert!(is_ay_panic_reason(
        "FARKAS SEMANTIC VERIFICATION FAILED in check_theory()"
    ));
    assert!(is_ay_panic_reason(
        "farkas semantic verification failed in lra"
    ));
}

#[test]
fn test_non_ay_panics() {
    assert!(!is_ay_panic_reason("index out of bounds"));
    assert!(!is_ay_panic_reason("assertion failed"));
    assert!(!is_ay_panic_reason(
        "called `Option::unwrap()` on a `None` value"
    ));
    assert!(!is_ay_panic_reason("arithmetic overflow"));
}

#[test]
fn test_debug_prefix_rejected() {
    // #1909: "debug:" contains "bug:" as substring — must not match
    assert!(!is_ay_panic_reason("debug: some info"));
    assert!(!is_ay_panic_reason("debugging: sort issue"));
    assert!(!is_ay_panic_reason("debugging: sort issue in user code"));
    assert!(!is_ay_panic_reason("Debug: unexpected state"));
}

#[test]
fn test_user_bug_prefix_rejected() {
    assert!(!is_ay_panic_reason("user_bug: unexpected term kind"));
}

#[test]
fn test_empty_string() {
    assert!(!is_ay_panic_reason(""));
    assert!(!is_ay_panic_reason("   "));
}

// ========================================================================
// contains_bug_marker tests
// ========================================================================

#[test]
fn test_bug_marker_at_start() {
    assert!(contains_bug_marker("bug: unexpected term kind"));
}

#[test]
fn test_bug_marker_with_prefix() {
    assert!(contains_bug_marker(
        "wrapped error: bug: unexpected term kind"
    ));
    assert!(contains_bug_marker(
        "debug: wrapper context; bug: unexpected term kind"
    ));
    assert!(contains_bug_marker("debugging bug: prefix"));
}

#[test]
fn test_bug_marker_rejected() {
    assert!(!contains_bug_marker("user_bug: unexpected term kind"));
    assert!(!contains_bug_marker("debug: unexpected state"));
}

// ========================================================================
// catch_ay_panics tests
// ========================================================================

#[test]
fn test_catch_success() {
    let result: Result<i32, String> = catch_ay_panics(|| Ok(42), Err);
    assert_eq!(result, Ok(42));
}

#[test]
fn test_catch_ay_panic_converted() {
    let result: Result<i32, String> = catch_ay_panics(
        AssertUnwindSafe(|| {
            panic!("sort mismatch: expected Bool, got BV(8)");
        }),
        Err,
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.contains("sort mismatch"), "got: {err}");
}

#[test]
fn test_catch_ay_bug_panic_converted() {
    let result: Result<i32, String> = catch_ay_panics(
        AssertUnwindSafe(|| {
            panic!("BUG: mk_eq called with non-matching sorts");
        }),
        Err,
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.contains("BUG: mk_eq"), "got: {err}");
}

#[test]
fn test_catch_ay_conflict_panic_converted() {
    let result: Result<i32, String> = catch_ay_panics(
        AssertUnwindSafe(|| {
            panic!("LRA conflict verification failed in check()");
        }),
        Err,
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.contains("conflict verification failed"), "got: {err}");
}

#[test]
fn test_catch_ay_farkas_panic_converted() {
    let result: Result<i32, String> = catch_ay_panics(
        AssertUnwindSafe(|| {
            panic!("Farkas semantic verification failed: coefficients do not validate");
        }),
        Err,
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("Farkas semantic verification failed"),
        "got: {err}"
    );
}

#[test]
fn test_catch_non_ay_panic_reraises() {
    let outer_result = catch_unwind(|| {
        let _: Result<i32, String> = catch_ay_panics(
            AssertUnwindSafe(|| {
                panic!("index out of bounds: the len is 3 but the index is 5");
            }),
            Err,
        );
    });
    assert!(
        outer_result.is_err(),
        "non-ay panics must propagate through catch_ay_panics"
    );
    let payload = outer_result.unwrap_err();
    let reason = panic_payload_to_string(&*payload);
    assert!(
        reason.contains("index out of bounds"),
        "re-raised panic should preserve original message, got: {reason}"
    );
}

#[test]
fn test_catch_debug_prefix_reraises() {
    // Regression for #1909: "debug:" must not be treated as ay "BUG:" panic
    let outer_result = catch_unwind(|| {
        let _: Result<i32, String> = catch_ay_panics(
            AssertUnwindSafe(|| {
                panic!("debug: some info");
            }),
            Err,
        );
    });
    assert!(
        outer_result.is_err(),
        "debug-prefixed panics must propagate through catch_ay_panics"
    );
}

/// Prove the generic boundary works with non-Result return types (model-checker-consumer-style).
#[test]
fn test_catch_generic_return_type() {
    // Returns an Option instead of Result — verifies generic signature
    let result: Option<i32> = catch_ay_panics(
        AssertUnwindSafe(|| {
            panic!("sort mismatch: expected Int, got Bool");
        }),
        |_reason| None,
    );
    assert_eq!(result, None);
}

/// Non-panicking closure with a plain value (no Result/Option wrapper).
#[test]
fn test_catch_plain_value() {
    let result: i32 = catch_ay_panics(|| 42, |_| -1);
    assert_eq!(result, 42);
}
