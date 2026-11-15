// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn unsigned_prefix_agrees_with_carry_and_checked_small_constant_domain() {
    for width in [1, 4, 8] {
        let a = BvExpr::leaf("a", width);
        let b = BvExpr::leaf("b", width);
        let prefix = BvExpr::Ult(Box::new(a.clone()), Box::new(b.clone()));
        let carry = BvExpr::not(BvExpr::carry_out_sub(a, b));
        let proof = export_bv_blast_proof_expr(&prefix, &carry).unwrap();
        proof.validate().unwrap();
    }
    for a in 0..8 {
        for b in 0..8 {
            let prefix = BvExpr::Ult(
                Box::new(BvExpr::const_val(a, 3)),
                Box::new(BvExpr::const_val(b, 3)),
            );
            let expected = BvExpr::const_val(u128::from(a < b), 1);
            export_bv_blast_proof_expr(&prefix, &expected)
                .unwrap()
                .validate()
                .unwrap();
        }
    }
}

#[test]
fn unsigned_prefix_reversal_and_width_mismatch_have_no_certificate() {
    let a = BvExpr::leaf("a", 4);
    let b = BvExpr::leaf("b", 4);
    let forward = BvExpr::Ult(Box::new(a.clone()), Box::new(b.clone()));
    let reversed = BvExpr::Ult(Box::new(b), Box::new(a));
    assert!(matches!(
        export_bv_blast_proof_expr(&forward, &reversed),
        Err(BvExprExportError::NoRefutation)
    ));
    let malformed = BvExpr::Ult(
        Box::new(BvExpr::leaf("a", 4)),
        Box::new(BvExpr::leaf("b", 3)),
    );
    assert!(matches!(
        export_bv_blast_proof_expr(&malformed, &BvExpr::const_val(1, 1)),
        Err(BvExprExportError::WidthMismatch { .. })
    ));
}
