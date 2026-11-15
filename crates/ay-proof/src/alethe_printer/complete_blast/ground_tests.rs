// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A ground `bvashr` amount is re-spelled through `evaluate` (`ground.rs`).

use super::*;

/// external-codegen's `narrow i8 and -> i32-carried wasm and + renormalize`: the
/// renormalizing shift pair masks its amount, `(bvand 24 31)`. Before the
/// amount was evaluated, the `bvashr` fell outside the consumer's admitted
/// domain, became an opaque word, and the true lemma was refused as
/// satisfiable.
#[test]
fn a_masked_constant_arithmetic_shift_amount_is_evaluated_and_blasted() {
    let mut f = Fixture::new();
    let a = f.bv("narrow_a", 8);
    let b = f.bv("narrow_b", 8);
    let both = f.op("bvand", &[a, b], 8);
    let left = f.indexed("sign_extend", vec![24], both, 32);
    let wide_a = f.indexed("sign_extend", vec![24], a, 32);
    let wide_b = f.indexed("sign_extend", vec![24], b, 32);
    let wide = f.op("bvand", &[wide_a, wide_b], 32);
    let twenty_four = f.constant(24, 32);
    let mask = f.constant(31, 32);
    let amount = f.op("bvand", &[twenty_four, mask], 32);
    let raised = f.op("bvshl", &[wide, amount], 32);
    let right = f.op("bvashr", &[raised, amount], 32);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    let document = f
        .refute(assertion)
        .expect("a masked constant amount is admissible once evaluated");
    assert_complete(&document);
    assert!(document.contains(":rule bitblast_ashr"), "{document}");
    // The amount is discharged by the checker's own evaluation, to 24.
    assert!(
        document.contains(" #b00000000000000000000000000011000)) :rule evaluate)"),
        "{document}"
    );
}

/// A symbolic amount is not ground: it stays outside the admitted domain and
/// the lemma is declined, never evaluated.
#[test]
fn a_symbolic_arithmetic_shift_amount_is_never_evaluated() {
    let mut f = Fixture::new();
    let x = f.bv("x", 8);
    let y = f.bv("y", 8);
    let shifted = f.op("bvashr", &[x, y], 8);
    let equality = f.equals(shifted, shifted);
    let assertion = f.not(equality);
    if let Some(document) = f.refute(assertion) {
        assert!(!document.contains(":rule evaluate"), "{document}");
        assert!(!document.contains(":rule bitblast_ashr"), "{document}");
    }
}
