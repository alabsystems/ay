// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Products by a non-power-of-two literal (`constant_product.rs`) against the
//! shift-and-add spellings compilers emit for them.

use super::*;

/// `x * c` against `(x << shift) ± x` at `width`.
fn shift_identity(width: u32, constant: u128, shift: u32, subtract: bool) -> Option<String> {
    let mut f = Fixture::new();
    let x = f.bv("x", width);
    let literal = f.terms.mk_bitvec(BigInt::from(constant), width);
    let product = f.op("bvmul", &[literal, x], width);
    let amount = f.constant(shift, width);
    let shifted = f.op("bvshl", &[x, amount], width);
    let other = f.op(
        if subtract { "bvsub" } else { "bvadd" },
        &[shifted, x],
        width,
    );
    let equality = f.equals(product, other);
    let assertion = f.not(equality);
    f.refute(assertion)
}

/// external-codegen's `ConstMul_Shift_Sub_I64` and `StrengthReduce` rows.
#[test]
fn a_constant_product_matches_its_shift_and_subtract_spelling() {
    for (width, shift) in [(64_u32, 7_u32), (64, 63), (32, 5)] {
        let constant = (1_u128 << shift) - 1;
        let document = shift_identity(width, constant, shift, true)
            .unwrap_or_else(|| panic!("x * (2^{shift} - 1) at {width} bits"));
        assert_complete(&document);
        assert!(document.contains(":rule poly_simp"), "{document}");
    }
}

/// `x * 17 == (x << 4) + x` and `x * (2^32 + 1) == (x << 32) + x`.
#[test]
fn a_constant_product_matches_its_shift_and_add_spelling() {
    for (width, constant, shift) in [(32_u32, 17_u128, 4_u32), (64, (1 << 32) + 1, 32)] {
        let document = shift_identity(width, constant, shift, false)
            .unwrap_or_else(|| panic!("x * {constant} at {width} bits"));
        assert_complete(&document);
    }
}

/// A wrong constant is refused: `x * 126` is not `(x << 7) - x`.
#[test]
fn a_wrong_constant_product_is_never_certified() {
    assert!(shift_identity(64, 126, 7, true).is_none());
}
