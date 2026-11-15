// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ring lane (`Normalizer::ring_identity`, see `ring_tests`) against
//! exhaustive evaluation.

use super::*;

/// Polynomial identities over `Z/(2^w)`: every answer agrees with exhaustive
/// evaluation at small widths, in both directions — an accepted equality holds
/// at every point, and the refused ones fail somewhere.
#[test]
fn polynomial_answers_match_exhaustive_small_domains() {
    for width in [2u32, 3, 4] {
        let modulus = 1u128 << width;
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        let y = terms.mk_var("y", Sort::bitvec(width));
        let three = constant(&mut terms, 3 % modulus, width);
        let xy = app(&mut terms, "bvmul", x, y, width);
        let yx = app(&mut terms, "bvmul", y, x, width);
        let x_plus_y = app(&mut terms, "bvadd", x, y, width);
        let square = app(&mut terms, "bvmul", x_plus_y, x_plus_y, width);
        let xx = app(&mut terms, "bvmul", x, x, width);
        let yy = app(&mut terms, "bvmul", y, y, width);
        let two_xy = app(&mut terms, "bvadd", xy, yx, width);
        let expanded = app(&mut terms, "bvadd", xx, two_xy, width);
        let expanded = app(&mut terms, "bvadd", expanded, yy, width);
        let x3y = app(&mut terms, "bvmul", three, xy, width);
        let y3x = app(&mut terms, "bvmul", yx, three, width);
        let cases: Vec<(TermId, TermId, &dyn Fn(u128, u128) -> (u128, u128))> = vec![
            (xy, yx, &|a, b| (a * b, b * a)),
            (square, expanded, &|a, b| {
                ((a + b) * (a + b), a * a + 2 * a * b + b * b)
            }),
            (x3y, y3x, &|a, b| (3 * a * b, 3 * b * a)),
            (xy, xx, &|a, b| (a * b, a * a)),
            (square, xx, &|a, b| ((a + b) * (a + b), a * a)),
        ];
        for (left, right, value) in cases {
            let equality = eq(&mut terms, left, right);
            let accepted = check(&terms, &[equality], &mut |_, _| true).unwrap();
            let holds = (0..modulus).all(|a| {
                (0..modulus).all(|b| {
                    let (l, r) = value(a, b);
                    l % modulus == r % modulus
                })
            });
            assert!(!accepted || holds, "{width}-bit: accepted a false identity");
            if !holds {
                assert!(!accepted);
            }
        }
    }
}

#[test]
fn only_literal_constant_products_are_scaled() {
    let width = 8;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    // 255 * x wraps to -x.
    let all_ones = constant(&mut terms, 255, width);
    let product = app(&mut terms, "bvmul", all_ones, x, width);
    let negation = terms.mk_app(Symbol::named("bvneg"), [x], Sort::bitvec(width));
    let equality = eq(&mut terms, product, negation);
    assert!(check(&terms, &[equality], &mut |_, _| true).unwrap());
    // A zero product keeps its dedicated multiplier-circuit certificate.
    let zero = constant(&mut terms, 0, width);
    let product = app(&mut terms, "bvmul", x, zero, width);
    let equality = eq(&mut terms, product, zero);
    assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
    // A product of two non-literals is one opaque atom of the affine form, so
    // commutativity is the ring lane's (`ring_tests`); a computed constant
    // operand is linear and stays unscaled.
    let xy = app(&mut terms, "bvmul", x, y, width);
    let yx = app(&mut terms, "bvmul", y, x, width);
    let equality = eq(&mut terms, xy, yx);
    assert!(check(&terms, &[equality], &mut |_, _| true).unwrap());
    let one = constant(&mut terms, 1, width);
    let two = app(&mut terms, "bvadd", one, one, width);
    let computed = app(&mut terms, "bvmul", two, x, width);
    let doubled = app(&mut terms, "bvadd", x, x, width);
    let equality = eq(&mut terms, computed, doubled);
    assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
}
