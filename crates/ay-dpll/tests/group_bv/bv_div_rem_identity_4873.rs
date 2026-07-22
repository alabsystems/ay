// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for BV division-remainder identity (#4873).
//!
//! The identity `m = (bvsdiv m n) * n + (bvsrem m n)` (for n != 0) must
//! hold for all bitvector widths.  Before #4873, `bvsdiv` and `bvsrem`
//! built independent division circuits; the SAT solver could not discover
//! the identity within the split budget.  The fix shares one division
//! circuit between paired div/rem operations.

use ntest::timeout;

/// Signed division-remainder identity with 8-bit vectors.
/// bvsdiv(m,n)*n + bvsrem(m,n) == m  for n != 0
#[test]
#[timeout(30_000)]
fn test_bv_sdiv_srem_identity_8bit() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const m (_ BitVec 8))
        (declare-const n (_ BitVec 8))
        (assert (not (= n (_ bv0 8))))
        (assert (not (= m (bvadd (bvmul (bvsdiv m n) n) (bvsrem m n)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "signed div-rem identity (8-bit)");
}

/// Unsigned division-remainder identity with 8-bit vectors.
/// bvudiv(m,n)*n + bvurem(m,n) == m  for n != 0
#[test]
#[timeout(30_000)]
fn test_bv_udiv_urem_identity_8bit() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const m (_ BitVec 8))
        (declare-const n (_ BitVec 8))
        (assert (not (= n (_ bv0 8))))
        (assert (not (= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "unsigned div-rem identity (8-bit)");
}
