// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Adjacent concrete FP-only commutativity canary for ay#8870.

mod common;

use common::solve_vec;
use ntest::timeout;

const FP16_MUL_NEG_COMMUTATIVITY_CONCRETE: &str = r#"
    (set-logic QF_FP)
    (declare-const a (_ FloatingPoint 5 11))
    (assert (= a (fp #b0 #b01111 #b0000000000)))
    (assert (not (= (fp.mul RNE a (fp.neg a))
                    (fp.mul RNE (fp.neg a) a))))
    (check-sat)
"#;

#[test]
#[timeout(20_000)]
fn test_fp16_mul_neg_commutativity_concrete_unsat_8870() {
    let outputs = solve_vec(FP16_MUL_NEG_COMMUTATIVITY_CONCRETE);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Concrete FP16 mul/neg commutativity canary should remain definitively UNSAT"
    );
}
