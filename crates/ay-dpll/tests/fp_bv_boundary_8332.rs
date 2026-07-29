// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Focused FP/BV boundary regressions for #8332.
//!
//! These are vulnerability-analysis shaped canaries: FP conversion results are
//! consumed by BV operations, and array-backed FP memory reads are reinterpreted
//! as raw IEEE-754 bits.

mod common;

use ntest::timeout;

#[test]
#[timeout(30_000)]
fn dsp_fp_to_ubv_result_feeds_bv_mask() {
    let smt = r#"
        (set-logic QF_BVFP)
        ; Float16 1.5 rounds to unsigned BV8 value 2 under RNE, so bit 0 is clear.
        (assert (not (=
            (bvand ((_ fp.to_ubv 8) RNE (fp #b0 #b01111 #b1000000000)) #x01)
            #x00)))
        (check-sat)
    "#;

    assert_eq!(
        common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ubv results must stay linked when consumed by BV operators"
    );
}

/// A stored NaN reads back as NaN through the QF_ABVFP store/select lowering.
///
/// The read-back is pinned with `fp.isNaN`, not with a bit-pattern: a
/// `(_ FloatingPoint 8 24)` has exactly ONE NaN element, so writing the
/// sign-set payload-1 encoding stores that element and nothing about the
/// original payload survives as a property of the *value*. `fp.to_ieee_bv` is
/// correspondingly unspecified on it (see `group_fp/fp_to_ieee_bv.rs`), so a
/// payload assertion here would test the encoder's scratch bits rather than
/// the lowering. Verified against z3 5.0.0, which likewise answers `sat` to
/// `(not (= (fp.to_ieee_bv <that NaN>) #xff800001))`.
#[test]
#[timeout(30_000)]
fn array_backed_fp_read_preserves_nan() {
    let smt = r#"
        (set-logic QF_ABVFP)
        (declare-const mem (Array (_ BitVec 32) (_ FloatingPoint 8 24)))
        (declare-const addr (_ BitVec 32))
        ; Negative NaN with a non-canonical payload: sign=1, exp=0xff, sig=1.
        (define-fun payload_nan () (_ FloatingPoint 8 24)
            (fp #b1 #b11111111 #b00000000000000000000001))
        (assert (not (fp.isNaN (select (store mem addr payload_nan) addr))))
        (check-sat)
    "#;

    assert_eq!(
        common::solve_vec(smt),
        vec!["unsat"],
        "QF_ABVFP store/select lowering must read back the stored NaN"
    );
}

/// The stored NaN is also the SAME element as every other NaN spelling, so a
/// read-back must be structurally equal to `(_ NaN 8 24)`.
#[test]
#[timeout(30_000)]
fn array_backed_fp_read_is_the_one_nan_element() {
    let smt = r#"
        (set-logic QF_ABVFP)
        (declare-const mem (Array (_ BitVec 32) (_ FloatingPoint 8 24)))
        (declare-const addr (_ BitVec 32))
        (define-fun payload_nan () (_ FloatingPoint 8 24)
            (fp #b1 #b11111111 #b00000000000000000000001))
        (assert (not (=
            (select (store mem addr payload_nan) addr)
            (_ NaN 8 24))))
        (check-sat)
    "#;

    assert_eq!(
        common::solve_vec(smt),
        vec!["unsat"],
        "all NaN encodings denote the one NaN element of the sort"
    );
}
