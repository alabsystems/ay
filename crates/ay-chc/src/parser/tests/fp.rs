// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_fp_sort_rejected_with_dedicated_error_6768() {
    let input = r#"
            (set-logic HORN)
            (declare-fun Inv ((_ FloatingPoint 8 24)) Bool)
            (assert (forall ((x (_ FloatingPoint 8 24))) (Inv x)))
            (check-sat)
        "#;
    let result = ChcParser::parse(input);
    assert!(result.is_err(), "FP sort should be rejected by preflight");
    let err = result.unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("unsupported CHC floating-point input"),
        "error should use dedicated FP diagnostic, got: {msg}"
    );
    assert!(
        msg.contains("FloatingPoint"),
        "error should mention the triggering token, got: {msg}"
    );
}

#[test]
fn test_rounding_mode_rejected_with_dedicated_error_6768() {
    let input = r#"
            (set-logic HORN)
            (declare-fun Inv (Int) Bool)
            (assert (forall ((x Int)) (=> (= x (fp.to_sbv 32 roundNearestTiesToEven (fp #b0 #x3f #x000000))) (Inv x))))
            (check-sat)
        "#;
    let result = ChcParser::parse(input);
    assert!(
        result.is_err(),
        "rounding mode should be rejected by preflight"
    );
    let err = result.unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("unsupported CHC floating-point input"),
        "error should use dedicated FP diagnostic, got: {msg}"
    );
}

#[test]
fn test_fp_operation_rejected_with_dedicated_error_6768() {
    let input = r#"
            (set-logic HORN)
            (declare-fun Inv (Int) Bool)
            (assert (forall ((x Int)) (=> (= x 0) (Inv (fp.add roundNearestTiesToEven x 1)))))
            (check-sat)
        "#;
    let result = ChcParser::parse(input);
    assert!(result.is_err(), "fp.add should be rejected by preflight");
    let err = result.unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("unsupported CHC floating-point input"),
        "error should use dedicated FP diagnostic, got: {msg}"
    );
}

#[test]
fn test_supported_sorts_still_parse_after_fp_preflight_6768() {
    // Ensure the preflight does not reject valid Bool/Int/Real/BV/Array inputs.
    let input = r#"
            (set-logic HORN)
            (declare-fun Inv (Int Real (_ BitVec 32) (Array Int Int)) Bool)
            (declare-var x Int)
            (declare-var r Real)
            (declare-var b (_ BitVec 32))
            (declare-var a (Array Int Int))
            (rule (=> (and (= x 0) (= r 0.0)) (Inv x r b a)))
            (query Inv)
        "#;
    let result = ChcParser::parse(input);
    assert!(
        result.is_ok(),
        "supported sorts should still parse: {:?}",
        result.err()
    );
}

#[test]
fn test_fp_tokens_in_comments_ignored_by_preflight_6768() {
    // Regression: FP tokens inside SMT-LIB comments must not trigger rejection.
    // Prover (P1:2200) found this bug: check_unsupported_fp_tokens scanned raw
    // input before comment stripping, causing false positives.
    let input = r#"
(set-logic HORN)
; FloatingPoint RoundingMode roundNearestTiesToEven fp.add fp.to_real
; This comment mentions all FP tokens but should be ignored
(declare-rel Inv (Int))
(declare-var x Int)
(rule (=> (= x 0) (Inv x)))
(query Inv)
        "#;
    let result = ChcParser::parse(input);
    assert!(
        result.is_ok(),
        "FP tokens in comments should not trigger rejection: {:?}",
        result.err()
    );
}
