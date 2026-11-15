// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The wire lane ([`check`]) against Carcara's `poly_simp` normal form.

use super::*;

fn app(terms: &mut TermStore, op: &str, a: TermId, b: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), [a, b], Sort::bitvec(width))
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn constant(terms: &mut TermStore, value: u128, width: u32) -> TermId {
    terms.mk_bitvec(value.into(), width)
}

/// Carcara's `poly_simp` expands every product this lane keeps as one atom and
/// merges commuted factors, so a coefficient can wrap to zero INSIDE or ACROSS
/// such atoms, where the affine form never sees it. Measured on carcara 1.1.0:
/// the three identities below are `invalid` under `poly_simp` (the first is
/// the everyday `-(x*y) + y*x`), and AY printed each as a `poly_simp` step it
/// labelled `trust_free=yes carcara_surface=supported`.
#[test]
fn a_wraparound_hidden_in_products_is_not_a_wire_identity() {
    let width = 8;
    let mut terms = TermStore::new();
    let [x, y, z] = ["x", "y", "z"].map(|name| terms.mk_var(name, Sort::bitvec(width)));
    let minus_one = constant(&mut terms, 0xff, width);
    let half = constant(&mut terms, 0x80, width);
    let xy = app(&mut terms, "bvmul", x, y, width);
    let yx = app(&mut terms, "bvmul", y, x, width);
    let minus_xy = app(&mut terms, "bvmul", minus_one, xy, width);
    let commuted_left = app(&mut terms, "bvadd", minus_xy, yx, width);
    let negated_xy = terms.mk_app(Symbol::named("bvneg"), [xy], Sort::bitvec(width));
    let commuted_right = app(&mut terms, "bvadd", yx, negated_xy, width);
    let doubled = app(&mut terms, "bvadd", x, x, width);
    let even_product = app(&mut terms, "bvmul", doubled, y, width);
    let scaled = app(&mut terms, "bvmul", half, even_product, width);
    let scaled_left = app(&mut terms, "bvadd", scaled, z, width);
    let swapped = app(&mut terms, "bvmul", even_product, half, width);
    let scaled_right = app(&mut terms, "bvadd", z, swapped, width);
    let half_y = app(&mut terms, "bvmul", half, y, width);
    let inner = app(&mut terms, "bvmul", doubled, half_y, width);
    let inner_left = app(&mut terms, "bvadd", inner, z, width);
    let inner_right = app(&mut terms, "bvadd", z, inner, width);
    for (left, right) in [
        (commuted_left, commuted_right),
        (scaled_left, scaled_right),
        (inner_left, inner_right),
    ] {
        let equality = eq(&mut terms, left, right);
        assert!(check_native(&terms, &[equality], &mut |_, _| true).unwrap());
        assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
        assert!(!crate::recognize_arith_poly_simp(&terms, &[equality]));
    }
    // Carcara reduces the constant term without keeping it, and it keeps no
    // monomial of a product with an odd coefficient: both replay (`valid`).
    let one = constant(&mut terms, 1, width);
    let x_minus_one = app(&mut terms, "bvadd", x, minus_one, width);
    let back = app(&mut terms, "bvadd", x_minus_one, one, width);
    let three = constant(&mut terms, 3, width);
    let two = constant(&mut terms, 2, width);
    let three_xy = app(&mut terms, "bvmul", three, xy, width);
    let tripled_left = app(&mut terms, "bvadd", three_xy, z, width);
    let xy_two = app(&mut terms, "bvmul", xy, two, width);
    let xy_plus = app(&mut terms, "bvadd", xy, xy_two, width);
    let tripled_right = app(&mut terms, "bvadd", z, xy_plus, width);
    for (left, right) in [(back, x), (tripled_left, tripled_right)] {
        let equality = eq(&mut terms, left, right);
        assert!(check(&terms, &[equality], &mut |_, _| true).unwrap());
        assert!(crate::recognize_arith_poly_simp(&terms, &[equality]));
    }
}
