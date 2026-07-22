// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #2885: BV operators must not be falsely detected as uninterpreted functions.
//!
//! Before the fix in 0ecfdd5b, `involves_uninterpreted_functions` was missing
//! all 27 BV operators. This caused formulas containing both arithmetic and BV
//! operations to be falsely classified as containing UF, preventing CEGQI from
//! handling them. These tests verify through the full executor API that mixed
//! arithmetic+BV quantified formulas are processed correctly.

use ntest::timeout;

/// A quantified formula mixing arithmetic and BV operators should not crash
/// or produce incorrect results. Before #2885, bvadd was falsely detected as
/// UF, which could affect CEGQI candidate selection.
#[test]
#[timeout(10000)]
fn test_bv_ops_do_not_block_cegqi_2885() {
    let smt = r#"
(set-logic ALL)
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (forall ((x Int)) (=> (>= x 0) (= (bvadd y z) (bvadd y z)))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    // The formula is valid (trivial BV equality). The solver may return SAT or
    // unknown (quantifier handling is incomplete), but must not return UNSAT
    // (which would be incorrect).
    assert!(
        !output.contains("unsat"),
        "Mixed arithmetic+BV valid formula must not be UNSAT, got: {output}"
    );
}

/// UF nested inside BV operations must still be detected. This ensures the
/// fix for BV operators didn't weaken UF detection for actual UFs.
#[test]
#[timeout(10000)]
fn test_uf_inside_bv_still_handled_2885() {
    let smt = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (forall ((x Int)) (=> (>= x 0) (= (bvadd (f y) z) z))))
(check-sat)
"#;
    // Satisfiable: z=0x00, f(y)=0x00 is a valid model. Z3 confirms sat.
    let output = crate::common::solve(smt);
    assert!(
        output.starts_with("sat"),
        "UF inside BV quantified formula is SAT (z=0, f(y)=0), got: {output}"
    );
}

/// Nested BV operators (bvshl inside bvult) should not trigger false UF detection.
#[test]
#[timeout(10000)]
fn test_nested_bv_ops_not_detected_as_uf_2885() {
    let smt = r#"
(set-logic ALL)
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (forall ((x Int)) (=> (>= x 0) (bvult (bvshl y z) (bvnot y)))))
(check-sat)
"#;
    // Satisfiable: x is unused, so body reduces to bvult(bvshl(y,z), bvnot(y)).
    // y=0x01, z=0x00 satisfies: bvshl(1,0)=1 < bvnot(1)=0xFE. Z3 confirms sat.
    let output = crate::common::solve(smt);
    assert!(
        output.starts_with("sat"),
        "Nested BV ops quantified formula is SAT (y=1,z=0), got: {output}"
    );
}
