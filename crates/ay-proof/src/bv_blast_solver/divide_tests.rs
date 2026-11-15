// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The divider against SMT-LIB's definition, exhaustively at small widths,
//! and on symbolic identities that hold for every divisor, zero included.

use super::super::*;

fn proves(lhs: &BvExpr, rhs: &BvExpr) -> bool {
    match export_bv_blast_proof_expr(lhs, rhs) {
        Ok(_) => true,
        Err(BvExprExportError::NoRefutation) => false,
        Err(other) => panic!("the divider must decide small queries: {other:?}"),
    }
}

/// SMT-LIB `bvudiv`/`bvurem`: a zero divisor gives all ones and the dividend.
fn reference(x: u128, d: u128, width: u32) -> (u128, u128) {
    if d == 0 {
        ((1 << width) - 1, x)
    } else {
        (x / d, x % d)
    }
}

#[test]
fn every_small_quotient_and_remainder_is_the_smt_lib_value() {
    for width in 1..=4u32 {
        let modulus = 1u128 << width;
        for x in 0..modulus {
            for d in 0..modulus {
                let (quotient, remainder) = reference(x, d, width);
                let (lx, ld) = (BvExpr::const_val(x, width), BvExpr::const_val(d, width));
                let division = BvExpr::udiv(lx.clone(), ld.clone());
                let modulo = BvExpr::urem(lx, ld);
                assert!(proves(&division, &BvExpr::const_val(quotient, width)));
                assert!(proves(&modulo, &BvExpr::const_val(remainder, width)));
                let wrong = (quotient + 1) % modulus;
                assert!(!proves(&division, &BvExpr::const_val(wrong, width)));
                let wrong = (remainder + 1) % modulus;
                assert!(!proves(&modulo, &BvExpr::const_val(wrong, width)));
            }
        }
    }
}

#[test]
fn symbolic_division_identities_hold_for_every_divisor() {
    let width = 6;
    let x = BvExpr::leaf("x", width);
    let d = BvExpr::leaf("d", width);
    // `(x / d) * d + x % d = x`, zero divisor included: `(#b1..1 * 0) + x`.
    let recombined = BvExpr::add(
        BvExpr::mul(BvExpr::udiv(x.clone(), d.clone()), d.clone()),
        BvExpr::urem(x.clone(), d.clone()),
    );
    assert!(proves(&recombined, &x));
    let one = BvExpr::const_val(1, width);
    let zero = BvExpr::const_val(0, width);
    assert!(proves(&BvExpr::udiv(x.clone(), one), &x));
    assert!(proves(&BvExpr::urem(x.clone(), zero.clone()), &x));
    assert!(proves(
        &BvExpr::udiv(x.clone(), zero),
        &BvExpr::const_val((1 << width) - 1, width)
    ));
    // ... and a false one is refused.
    assert!(!proves(&BvExpr::udiv(x.clone(), d), &x));
}
