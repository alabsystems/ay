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

#[test]
#[timeout(30_000)]
fn array_backed_fp_read_preserves_nan_payload_bits() {
    let smt = r#"
        (set-logic QF_ABVFP)
        (declare-const mem (Array (_ BitVec 32) (_ FloatingPoint 8 24)))
        (declare-const addr (_ BitVec 32))
        ; Negative NaN with a non-canonical payload: sign=1, exp=0xff, sig=1.
        (define-fun payload_nan () (_ FloatingPoint 8 24)
            (fp #b1 #b11111111 #b00000000000000000000001))
        (assert (not (=
            (fp.to_ieee_bv (select (store mem addr payload_nan) addr))
            #xff800001)))
        (check-sat)
    "#;

    assert_eq!(
        common::solve_vec(smt),
        vec!["unsat"],
        "QF_ABVFP store/select lowering must preserve FP NaN payload bits"
    );
}
