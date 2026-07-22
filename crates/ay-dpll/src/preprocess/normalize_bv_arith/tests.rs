// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

fn add_all(terms: &mut TermStore, values: &[TermId]) -> TermId {
    values[1..]
        .iter()
        .fold(values[0], |sum, &value| terms.mk_bvadd(vec![sum, value]))
}

#[test]
fn test_normalize_commutative_bvadd() {
    let mut terms = TermStore::new();

    // Create (bvadd a b) and (bvadd b a)
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let add_ab = terms.mk_bvadd(vec![a, b]);
    let add_ba = terms.mk_bvadd(vec![b, a]);

    // Before normalization, they may differ
    // (depends on whether mk_bvadd canonicalizes)

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, add_ab);
    pass.cache.clear(); // Clear cache to test independent normalization
    let norm_ba = pass.normalize(&mut terms, add_ba);

    // After normalization, they should be identical
    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvadd a b) and (bvadd b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_commutative_bvmul() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let mul_ab = terms.mk_bvmul(vec![a, b]);
    let mul_ba = terms.mk_bvmul(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, mul_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, mul_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvmul a b) and (bvmul b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_associative_bvadd() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));

    // (bvadd (bvadd a b) c)
    let add_ab = terms.mk_bvadd(vec![a, b]);
    let left_assoc = terms.mk_bvadd(vec![add_ab, c]);

    // (bvadd a (bvadd b c))
    let add_bc = terms.mk_bvadd(vec![b, c]);
    let right_assoc = terms.mk_bvadd(vec![a, add_bc]);

    let mut pass = NormalizeBvArith::new();
    let norm_left = pass.normalize(&mut terms, left_assoc);
    pass.cache.clear();
    let norm_right = pass.normalize(&mut terms, right_assoc);

    assert_eq!(
        norm_left, norm_right,
        "Associativity: ((a+b)+c) and (a+(b+c)) should normalize to same term"
    );
}

#[test]
fn test_normalize_deeply_nested() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));
    let d = terms.mk_var("d", Sort::bitvec(8));

    // ((a + b) + (c + d))
    let add_ab = terms.mk_bvadd(vec![a, b]);
    let add_cd = terms.mk_bvadd(vec![c, d]);
    let nested = terms.mk_bvadd(vec![add_ab, add_cd]);

    // (((d + c) + b) + a) - different nesting and order
    let add_dc = terms.mk_bvadd(vec![d, c]);
    let add_dcb = terms.mk_bvadd(vec![add_dc, b]);
    let other = terms.mk_bvadd(vec![add_dcb, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_nested = pass.normalize(&mut terms, nested);
    pass.cache.clear();
    let norm_other = pass.normalize(&mut terms, other);

    assert_eq!(
        norm_nested, norm_other,
        "Deeply nested should normalize to same term"
    );
}

#[test]
fn test_normalize_idempotent() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let add_ab = terms.mk_bvadd(vec![a, b]);

    let mut pass = NormalizeBvArith::new();
    let norm1 = pass.normalize(&mut terms, add_ab);
    pass.cache.clear();
    let norm2 = pass.normalize(&mut terms, norm1);

    assert_eq!(norm1, norm2, "Normalization should be idempotent");
}

#[test]
fn test_normalize_preserves_constants() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let const_5 = terms.mk_bitvec(BigInt::from(5), 8);
    let add = terms.mk_bvadd(vec![const_5, a]);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, add);

    // The normalized form should still contain both operands
    // (constant folding is done by mk_bvadd, not by normalization)
    match terms.get(normalized) {
        TermData::App(sym, args) if sym.name() == "bvadd" => {
            assert_eq!(args.len(), 2);
            // Args should be sorted by TermId
            assert!(args[0].index() <= args[1].index());
        }
        _ => panic!("Expected bvadd application"),
    }
}

#[test]
fn test_pass_apply() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let add_ba = terms.mk_bvadd(vec![b, a]); // b + a

    let mut assertions = vec![add_ba];
    let mut pass = NormalizeBvArith::new();

    // Apply pass
    let _modified = pass.apply(&mut terms, &mut assertions);

    // Note: might not modify if a < b in TermId ordering
    // The key is that it's deterministic
    assert_eq!(assertions.len(), 1);
}

#[test]
fn test_normalize_nested_in_equality() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));

    // (= (bvadd b a) c)
    let add_ba = terms.mk_bvadd(vec![b, a]);
    let eq = terms.mk_eq(add_ba, c);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, eq);

    // The equality should have normalized children
    if let TermData::App(sym, args) = terms.get(normalized) {
        assert_eq!(sym.name(), "=");
        assert_eq!(args.len(), 2);
        // The bvadd inside should be normalized
    }
}

#[test]
fn test_modular_linear_fingerprint_closes_external_codegen_faulhaber_identity() {
    let mut terms = TermStore::new();
    let width = 64;
    let acc = terms.mk_var("acc", Sort::bitvec(width));
    let a2 = terms.mk_var("a2", Sort::bitvec(width));
    let a1 = terms.mk_var("a1", Sort::bitvec(width));
    let a0 = terms.mk_var("a0", Sort::bitvec(width));
    let two = terms.mk_bitvec(BigInt::from(2u8), width);
    let three = terms.mk_bitvec(BigInt::from(3u8), width);
    let four = terms.mk_bitvec(BigInt::from(4u8), width);
    let five = terms.mk_bitvec(BigInt::from(5u8), width);

    let two_a1 = terms.mk_bvmul(vec![two, a1]);
    let four_a2 = terms.mk_bvmul(vec![four, a2]);
    let lhs = add_all(&mut terms, &[two_a1, four_a2, a0, a0, a0, a1, a2, acc]);
    let three_a0 = terms.mk_bvmul(vec![three, a0]);
    let three_a1 = terms.mk_bvmul(vec![three, a1]);
    let five_a2 = terms.mk_bvmul(vec![five, a2]);
    let rhs = add_all(&mut terms, &[three_a0, three_a1, five_a2, acc]);
    let equality = terms.mk_eq(lhs, rhs);
    let negated = terms.mk_not(equality);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, negated);
    let false_term = terms.mk_bool(false);
    assert_eq!(normalized, false_term);
}

#[test]
fn test_modular_linear_fingerprint_matches_exhaustive_small_width_oracle() {
    // 3*(x-y) + 5*y + 7 == 3*x + 2*y + 7 in every Z/2^w. This exercises
    // add, subtract, sparse constant multiplication, mul2concat shifts,
    // constants, coefficient merging, and modular wraparound.
    for width in 1u32..=6 {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        let y = terms.mk_var("y", Sort::bitvec(width));
        let two = terms.mk_bitvec(BigInt::from(2u8), width);
        let three = terms.mk_bitvec(BigInt::from(3u8), width);
        let five = terms.mk_bitvec(BigInt::from(5u8), width);
        let seven = terms.mk_bitvec(BigInt::from(7u8), width);

        let x_minus_y = terms.mk_bvsub(vec![x, y]);
        let three_diff = terms.mk_bvmul(vec![three, x_minus_y]);
        let five_y = terms.mk_bvmul(vec![five, y]);
        let lhs = add_all(&mut terms, &[three_diff, five_y, seven]);
        let three_x = terms.mk_bvmul(vec![three, x]);
        let two_y = terms.mk_bvmul(vec![two, y]);
        let rhs = add_all(&mut terms, &[three_x, two_y, seven]);
        let equality = terms.mk_eq(lhs, rhs);

        let mut pass = NormalizeBvArith::new();
        let normalized = pass.normalize(&mut terms, equality);
        let true_term = terms.mk_bool(true);
        assert_eq!(normalized, true_term, "fingerprint missed width {width}");

        // Independent ring oracle: do not reuse TermStore substitution or BV
        // builders, because those are part of the implementation under test.
        let modulus = 1u64 << width;
        for x_value in 0..modulus {
            for y_value in 0..modulus {
                let difference = (x_value + modulus - y_value) % modulus;
                let concrete_lhs = (3 * difference + 5 * y_value + 7) % modulus;
                let concrete_rhs = (3 * x_value + 2 * y_value + 7) % modulus;
                assert_eq!(
                    concrete_lhs, concrete_rhs,
                    "oracle mismatch at width={width}, x={x_value}, y={y_value}"
                );
            }
        }
    }
}

#[test]
fn test_modular_linear_fingerprint_handles_raw_constant_mul_and_shift() {
    let mut terms = TermStore::new();
    let width = 16;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let three = terms.mk_bitvec(BigInt::from(3u8), width);
    // Deliberately bypass mk_bvmul: importer/internal callers may hand the pass
    // a raw term, and literal multiplication must still be recognized.
    let raw_three_x = terms.mk_app(Symbol::named("bvmul"), [three, x], Sort::bitvec(width));
    let four = terms.mk_bitvec(BigInt::from(4u8), width);
    let four_x = terms.mk_bvmul(vec![x, four]);
    let four_x_minus_x = terms.mk_bvsub(vec![four_x, x]);
    let equality = terms.mk_eq(raw_three_x, four_x_minus_x);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, equality);
    let true_term = terms.mk_bool(true);
    assert_eq!(normalized, true_term);
}

#[test]
fn test_poly_fingerprint_closes_distributive_identity() {
    // Deliberately flipped from the historical
    // test_modular_linear_fingerprint_keeps_nonlinear_products_opaque pin:
    // the polynomial normal form now soundly distributes variable products,
    // so x*(y+z) = x*y + x*z folds to true.
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    let z = terms.mk_var("z", Sort::bitvec(width));

    let y_plus_z = terms.mk_bvadd(vec![y, z]);
    let lhs = terms.mk_bvmul(vec![x, y_plus_z]);
    let xy = terms.mk_bvmul(vec![x, y]);
    let xz = terms.mk_bvmul(vec![x, z]);
    let rhs = terms.mk_bvadd(vec![xy, xz]);
    let equality = terms.mk_eq(lhs, rhs);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, equality);
    let true_term = terms.mk_bool(true);
    assert_eq!(
        normalized, true_term,
        "polynomial fingerprint must close the distributive identity"
    );
}

#[test]
fn test_poly_fingerprint_closes_square_of_sum_identity() {
    // The qfbv-gen gap probe: (x+y)^2 = x^2 + 2xy + y^2 in Z/2^w.
    for width in [1u32, 8, 16, 32, 64] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        let y = terms.mk_var("y", Sort::bitvec(width));
        let two = terms.mk_bitvec(BigInt::from(2u8), width);

        let x_plus_y = terms.mk_bvadd(vec![x, y]);
        let lhs = terms.mk_bvmul(vec![x_plus_y, x_plus_y]);
        let xx = terms.mk_bvmul(vec![x, x]);
        let xy = terms.mk_bvmul(vec![x, y]);
        let two_xy = terms.mk_bvmul(vec![two, xy]);
        let yy = terms.mk_bvmul(vec![y, y]);
        let rhs = add_all(&mut terms, &[xx, two_xy, yy]);
        let equality = terms.mk_eq(lhs, rhs);
        let negated = terms.mk_not(equality);

        let mut pass = NormalizeBvArith::new();
        let normalized = pass.normalize(&mut terms, negated);
        let false_term = terms.mk_bool(false);
        assert_eq!(
            normalized, false_term,
            "square-of-sum identity missed at width {width}"
        );
    }
}

#[test]
fn test_poly_fingerprint_rejects_square_of_sum_near_misses() {
    // Wrong-fact twins of the square-of-sum identity must NOT fold: the
    // polynomials differ formally ((x+y)^2 vs x^2+xy+y^2 and vs
    // x^2+2xy+y^2+1), so the fold must decline and leave bit-blasting to
    // decide. Folding either to true would be a wrong verdict.
    let width = 8;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    let two = terms.mk_bitvec(BigInt::from(2u8), width);
    let one = terms.mk_bitvec(BigInt::one(), width);

    let x_plus_y = terms.mk_bvadd(vec![x, y]);
    let lhs = terms.mk_bvmul(vec![x_plus_y, x_plus_y]);
    let xx = terms.mk_bvmul(vec![x, x]);
    let xy = terms.mk_bvmul(vec![x, y]);
    let yy = terms.mk_bvmul(vec![y, y]);

    // Missing coefficient: x^2 + xy + y^2.
    let missing_coeff = add_all(&mut terms, &[xx, xy, yy]);
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms,
        lhs,
        missing_coeff,
        width
    ));

    // Off-by-one constant: x^2 + 2xy + y^2 + 1.
    let two_xy = terms.mk_bvmul(vec![two, xy]);
    let off_by_one = add_all(&mut terms, &[xx, two_xy, yy, one]);
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, lhs, off_by_one, width
    ));
}

#[test]
fn test_poly_fingerprint_matches_exhaustive_ring_oracle_small_widths() {
    // (x+y)*(x-y) = x^2 - y^2 in every Z/2^w: fold must fire, and an
    // independent brute-force ring oracle confirms the identity semantically.
    for width in 1u32..=4 {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        let y = terms.mk_var("y", Sort::bitvec(width));
        let x_plus_y = terms.mk_bvadd(vec![x, y]);
        let x_minus_y = terms.mk_bvsub(vec![x, y]);
        let lhs = terms.mk_bvmul(vec![x_plus_y, x_minus_y]);
        let xx = terms.mk_bvmul(vec![x, x]);
        let yy = terms.mk_bvmul(vec![y, y]);
        let rhs = terms.mk_bvsub(vec![xx, yy]);
        let equality = terms.mk_eq(lhs, rhs);

        let mut pass = NormalizeBvArith::new();
        let normalized = pass.normalize(&mut terms, equality);
        let true_term = terms.mk_bool(true);
        assert_eq!(
            normalized, true_term,
            "difference-of-squares missed at width {width}"
        );

        // Independent ring oracle: every fold the fingerprint performs must
        // agree with brute-force evaluation over all assignments.
        let modulus = 1u64 << width;
        for x_value in 0..modulus {
            for y_value in 0..modulus {
                let sum = (x_value + y_value) % modulus;
                let difference = (x_value + modulus - y_value) % modulus;
                let concrete_lhs = (sum * difference) % modulus;
                let concrete_rhs =
                    (x_value * x_value % modulus + modulus - y_value * y_value % modulus) % modulus;
                assert_eq!(
                    concrete_lhs, concrete_rhs,
                    "oracle mismatch at width={width}, x={x_value}, y={y_value}"
                );
            }
        }
    }
}

#[test]
fn test_poly_fingerprint_width_one_folds_even_coefficients_soundly() {
    // At width 1, 2xy = 0, so (x+y)^2 = x^2 + y^2 IS an identity mod 2 and
    // the canonical form (which drops the wrapped-to-zero 2xy monomial) must
    // close it. Verified against the exhaustive mod-2 oracle.
    let width = 1;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    let x_plus_y = terms.mk_bvadd(vec![x, y]);
    let lhs = terms.mk_bvmul(vec![x_plus_y, x_plus_y]);
    let xx = terms.mk_bvmul(vec![x, x]);
    let yy = terms.mk_bvmul(vec![y, y]);
    let rhs = terms.mk_bvadd(vec![xx, yy]);
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms, lhs, rhs, width
    ));
    for x_value in 0u64..2 {
        for y_value in 0u64..2 {
            let concrete_lhs = ((x_value + y_value) * (x_value + y_value)) % 2;
            let concrete_rhs = (x_value * x_value + y_value * y_value) % 2;
            assert_eq!(concrete_lhs, concrete_rhs);
        }
    }

    // Same equality at width 8 is NOT an identity (x=y=1 gives 4 vs 2) and
    // must not fold.
    let wide = 8;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(wide));
    let y = terms.mk_var("y", Sort::bitvec(wide));
    let x_plus_y = terms.mk_bvadd(vec![x, y]);
    let lhs = terms.mk_bvmul(vec![x_plus_y, x_plus_y]);
    let xx = terms.mk_bvmul(vec![x, x]);
    let yy = terms.mk_bvmul(vec![y, y]);
    let rhs = terms.mk_bvadd(vec![xx, yy]);
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, lhs, rhs, wide
    ));
}

#[test]
fn test_poly_fingerprint_declines_width_one_semantic_only_identity() {
    // x*x = x holds semantically at width 1 but the FORMAL polynomials
    // (x^2 vs x) differ, so the fold must decline — bit-blasting decides it.
    // This pins the one-sidedness of the conclusion: mismatch proves nothing.
    let width = 1;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let xx = terms.mk_bvmul(vec![x, x]);
    assert!(!NormalizeBvArith::modular_poly_equal(&terms, xx, x, width));
}

#[test]
fn test_poly_fingerprint_wrapping_and_zero_drop_canonicity() {
    let width = 4;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let zero = terms.mk_bitvec(BigInt::zero(), width);
    let xx = terms.mk_app(Symbol::named("bvmul"), [x, x], Sort::bitvec(width));

    // Coefficient product 8*2 = 16 = 2^4 wraps to 0: 8*(2*x^2) = 0 in Z/16.
    // The wrapped monomial must be DROPPED (not kept with coefficient 0) or
    // canonicity breaks.
    let two = terms.mk_bitvec(BigInt::from(2u8), width);
    let eight = terms.mk_bitvec(BigInt::from(8u8), width);
    let two_xx = terms.mk_app(Symbol::named("bvmul"), [two, xx], Sort::bitvec(width));
    let sixteen_xx = terms.mk_app(Symbol::named("bvmul"), [eight, two_xx], Sort::bitvec(width));
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms, sixteen_xx, zero, width
    ));

    // Addition wrap: 8x^2 + 8x^2 = 16x^2 = 0 in Z/16 (2^(w-1) + 2^(w-1)).
    let eight_xx = terms.mk_app(Symbol::named("bvmul"), [eight, xx], Sort::bitvec(width));
    let doubled = terms.mk_app(
        Symbol::named("bvadd"),
        [eight_xx, eight_xx],
        Sort::bitvec(width),
    );
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms, doubled, zero, width
    ));

    // Near-miss twin: 15x^2 is NOT the zero polynomial in Z/16.
    let fifteen = terms.mk_bitvec(BigInt::from(15u8), width);
    let fifteen_xx = terms.mk_app(Symbol::named("bvmul"), [fifteen, xx], Sort::bitvec(width));
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, fifteen_xx, zero, width
    ));
}

#[test]
fn test_poly_fingerprint_degree_cap_fails_closed() {
    let width = 8;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));

    // x^8 is exactly at the degree cap and stays recognizable.
    let mut power8 = x;
    for _ in 0..7 {
        power8 = terms.mk_app(Symbol::named("bvmul"), [power8, x], Sort::bitvec(width));
    }
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms, power8, power8, width
    ));

    // x^9 exceeds BV_POLY_MAX_DEGREE: the fingerprint declines entirely,
    // even against itself. Sound: bit-blasting decides.
    let power9 = terms.mk_app(Symbol::named("bvmul"), [power8, x], Sort::bitvec(width));
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, power9, power9, width
    ));
}

#[test]
fn test_poly_fingerprint_product_precharge_fails_closed() {
    // (v0+..+v255) * (u0+..+u255): the |P|*|Q| = 65536 cross-product
    // pre-charge exceeds the remaining coefficient-op budget and must
    // decline BEFORE doing any expansion work.
    let width = 16;
    let mut terms = TermStore::new();
    let left_vars: Vec<TermId> = (0..256)
        .map(|i| terms.mk_var(format!("v{i}"), Sort::bitvec(width)))
        .collect();
    let right_vars: Vec<TermId> = (0..256)
        .map(|i| terms.mk_var(format!("u{i}"), Sort::bitvec(width)))
        .collect();
    let left_sum = add_all(&mut terms, &left_vars);
    let right_sum = add_all(&mut terms, &right_vars);
    let product = terms.mk_app(
        Symbol::named("bvmul"),
        [left_sum, right_sum],
        Sort::bitvec(width),
    );
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, product, product, width
    ));
}

#[test]
fn test_poly_fingerprint_keeps_division_and_shift_ops_opaque() {
    // Ring semantics must NEVER be assigned to division/signed/symbolic-shift
    // ops. bvudiv "distributivity" is a non-identity: (x+y)/2 != x/2 + y/2
    // at x=y=1. The subtrees are opaque atoms, formally distinct: no fold.
    let width = 8;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    let two = terms.mk_bitvec(BigInt::from(2u8), width);
    let x_plus_y = terms.mk_bvadd(vec![x, y]);
    let lhs = terms.mk_app(
        Symbol::named("bvudiv"),
        [x_plus_y, two],
        Sort::bitvec(width),
    );
    let x_half = terms.mk_app(Symbol::named("bvudiv"), [x, two], Sort::bitvec(width));
    let y_half = terms.mk_app(Symbol::named("bvudiv"), [y, two], Sort::bitvec(width));
    let rhs = terms.mk_bvadd(vec![x_half, y_half]);
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, lhs, rhs, width
    ));

    // bvashr x 1 vs bvudiv x 2: differ on "negative" x; both opaque, no fold.
    let one = terms.mk_bitvec(BigInt::one(), width);
    let ashr = terms.mk_app(Symbol::named("bvashr"), [x, one], Sort::bitvec(width));
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, ashr, x_half, width
    ));

    // But a product CONTAINING an opaque atom is still exact over the atom:
    // (x/2 + y) * (x/2 + y) = (x/2)^2 + 2*(x/2)*y + y^2 must fold.
    let half_plus_y = terms.mk_bvadd(vec![x_half, y]);
    let square = terms.mk_bvmul(vec![half_plus_y, half_plus_y]);
    let half_sq = terms.mk_bvmul(vec![x_half, x_half]);
    let half_y = terms.mk_bvmul(vec![x_half, y]);
    let two_half_y = terms.mk_bvmul(vec![two, half_y]);
    let yy = terms.mk_bvmul(vec![y, y]);
    let expanded = add_all(&mut terms, &[half_sq, two_half_y, yy]);
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms, square, expanded, width
    ));
}

#[test]
fn test_modular_linear_fingerprint_rejects_non_shift_concat_lookalike() {
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));
    // concat(extract(x,6,1), 00) is not x<<2; the exact mul2concat pattern is
    // extract(x,5,0). Treating this lookalike as a shift would be unsound.
    let wrong_extract = terms.mk_bvextract(6, 1, x);
    let low_zero = terms.mk_bitvec(BigInt::zero(), 2);
    let lookalike = terms.mk_bvconcat(vec![wrong_extract, low_zero]);
    let four = terms.mk_bitvec(BigInt::from(4u8), width);
    let true_shift = terms.mk_bvmul(vec![x, four]);
    let equality = terms.mk_eq(lookalike, true_shift);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, equality);
    let true_term = terms.mk_bool(true);
    assert_ne!(normalized, true_term);
}

#[test]
fn test_modular_linear_fingerprint_rejects_near_miss_coefficient() {
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let three = terms.mk_bitvec(BigInt::from(3u8), width);
    let four = terms.mk_bitvec(BigInt::from(4u8), width);
    let three_x = terms.mk_app(Symbol::named("bvmul"), [three, x], Sort::bitvec(width));
    let four_x = terms.mk_app(Symbol::named("bvmul"), [four, x], Sort::bitvec(width));

    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, three_x, four_x, width
    ));
}

#[test]
fn test_modular_linear_fingerprint_shift_edges_and_variable_shift() {
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let variable_shift = terms.mk_var("shift", Sort::bitvec(width));
    let zero = terms.mk_bitvec(BigInt::zero(), width);

    for shift in [0u8, 7, 8, 9] {
        let amount = terms.mk_bitvec(BigInt::from(shift), width);
        let shifted = terms.mk_app(Symbol::named("bvshl"), [x, amount], Sort::bitvec(width));
        let expected = if u32::from(shift) >= width {
            zero
        } else {
            let coefficient = terms.mk_bitvec(BigInt::one() << shift, width);
            terms.mk_app(
                Symbol::named("bvmul"),
                [coefficient, x],
                Sort::bitvec(width),
            )
        };
        assert!(NormalizeBvArith::modular_poly_equal(
            &terms, shifted, expected, width
        ));
    }

    let symbolic_shift = terms.mk_app(
        Symbol::named("bvshl"),
        [x, variable_shift],
        Sort::bitvec(width),
    );
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms,
        symbolic_shift,
        x,
        width
    ));
}

#[test]
fn test_modular_linear_fingerprint_negative_and_wrapping_coefficients() {
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let two = terms.mk_bitvec(BigInt::from(2u8), width);
    let all_ones = terms.mk_bitvec(BigInt::from(255u16), width);
    let neg_x = terms.mk_app(Symbol::named("bvneg"), [x], Sort::bitvec(width));
    let minus_one_x = terms.mk_app(Symbol::named("bvmul"), [all_ones, x], Sort::bitvec(width));
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms,
        neg_x,
        minus_one_x,
        width
    ));

    // (255 + 2) * x = 257*x = x modulo 256.
    let two_x = terms.mk_app(Symbol::named("bvmul"), [two, x], Sort::bitvec(width));
    let wrapped = terms.mk_app(
        Symbol::named("bvadd"),
        [minus_one_x, two_x],
        Sort::bitvec(width),
    );
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms, wrapped, x, width
    ));
}

#[test]
fn test_modular_linear_fingerprint_exact_concat_and_malformed_sort() {
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));

    // concat(extract(x,5,0), 00) is the constructor's x * 4 form and must
    // fingerprint identically to 4*x.
    let high = terms.mk_bvextract(5, 0, x);
    let low = terms.mk_bitvec(BigInt::zero(), 2);
    let shifted = terms.mk_app(Symbol::named("concat"), [high, low], Sort::bitvec(width));
    let four = terms.mk_bitvec(BigInt::from(4u8), width);
    let four_x = terms.mk_app(Symbol::named("bvmul"), [four, x], Sort::bitvec(width));
    assert!(NormalizeBvArith::modular_poly_equal(
        &terms, shifted, four_x, width
    ));

    // Correct indices with a forged five-bit stored result sort. The child
    // widths no longer sum to the claimed concat width; the concat must stay
    // an opaque atom rather than impersonate the shift form.
    let malformed_high = terms.mk_app(Symbol::indexed("extract", vec![5, 0]), [x], Sort::bitvec(5));
    let malformed = terms.mk_app(
        Symbol::named("concat"),
        [malformed_high, low],
        Sort::bitvec(width),
    );
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, malformed, four_x, width
    ));
}

#[test]
fn test_modular_linear_fingerprint_budgets_fail_closed() {
    let mut terms = TermStore::new();
    let width = 16;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let mut expanded = x;
    // Conceptually 4096 leaves plus 4095 adds, but only twelve stored DAG
    // levels. Traversal must stop at the shared node work bound.
    for _ in 0..12 {
        expanded = terms.mk_app(
            Symbol::named("bvadd"),
            [expanded, expanded],
            Sort::bitvec(width),
        );
    }
    let coefficient = terms.mk_bitvec(BigInt::from(4096u16), width);
    let compact = terms.mk_app(
        Symbol::named("bvmul"),
        [coefficient, x],
        Sort::bitvec(width),
    );
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, expanded, compact, width
    ));

    let wide_width = BV_LINEAR_MAX_WIDTH + 1;
    let wide = terms.mk_var("wide", Sort::bitvec(wide_width));
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms, wide, wide, wide_width
    ));

    let constant = terms.mk_bitvec(BigInt::one(), width);
    let modulus = BigInt::one() << width;
    let mut exhausted = BvLinearBudget {
        nodes: 1,
        coefficient_ops: 0,
    };
    assert!(
        NormalizeBvArith::poly_fingerprint(&terms, constant, width, &modulus, &mut exhausted)
            .is_none()
    );
}

#[test]
fn test_modular_linear_fingerprint_rejects_noncanonical_negative_shift() {
    let width = 8;
    let entries = vec![
        (
            TermData::Const(Constant::BitVec {
                value: BigInt::one(),
                width,
            }),
            Sort::bitvec(width),
        ),
        (
            TermData::Const(Constant::BitVec {
                value: -BigInt::one(),
                width,
            }),
            Sort::bitvec(width),
        ),
        (
            TermData::App(Symbol::named("bvshl"), vec![TermId::new(0), TermId::new(1)]),
            Sort::bitvec(width),
        ),
        (
            TermData::Const(Constant::BitVec {
                value: BigInt::zero(),
                width,
            }),
            Sort::bitvec(width),
        ),
    ];
    let terms = TermStore::from_entries(entries, None, None, 0);
    assert!(!NormalizeBvArith::modular_poly_equal(
        &terms,
        TermId::new(2),
        TermId::new(3),
        width
    ));
}

#[test]
fn test_normalize_preserves_indexed_builtin_lookalikes() {
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    let bad = terms.mk_app(
        Symbol::indexed("bvadd", vec![7]),
        [x, y],
        Sort::bitvec(width),
    );
    let good = terms.mk_app(Symbol::named("bvadd"), [x, y], Sort::bitvec(width));
    let equality = terms.mk_app(Symbol::named("="), [bad, good], Sort::Bool);

    let mut pass = NormalizeBvArith::new();
    let normalized_bad = pass.normalize(&mut terms, bad);
    assert_eq!(normalized_bad, bad);
    pass.cache.clear();
    let normalized_equality = pass.normalize(&mut terms, equality);
    let true_term = terms.mk_bool(true);
    assert_ne!(normalized_equality, true_term);

    let indexed_equality = terms.mk_app(Symbol::indexed("=", vec![0]), [x, x], Sort::Bool);
    pass.cache.clear();
    assert_eq!(
        pass.normalize(&mut terms, indexed_equality),
        indexed_equality
    );
}

#[test]
fn test_normalize_preserves_malformed_commutative_apps_without_panicking() {
    let mut terms = TermStore::new();
    let width = 8;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    let predicate = terms.mk_var("p", Sort::Bool);
    let mut malformed = Vec::new();
    for name in ["bvadd", "bvmul", "bvand", "bvor", "bvxor"] {
        malformed.push(terms.mk_app(
            Symbol::named(name),
            Vec::<TermId>::new(),
            Sort::bitvec(width),
        ));
        malformed.push(terms.mk_app(Symbol::named(name), [x], Sort::bitvec(width)));
        malformed.push(terms.mk_app(Symbol::named(name), [x, y, x], Sort::bitvec(width)));
        malformed.push(terms.mk_app(Symbol::named(name), [x, predicate], Sort::bitvec(width)));
    }

    let mut pass = NormalizeBvArith::new();
    for raw in malformed {
        pass.cache.clear();
        assert_eq!(pass.normalize(&mut terms, raw), raw);
    }
}

#[test]
fn test_normalize_commutative_bvand() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let and_ab = terms.mk_bvand(vec![a, b]);
    let and_ba = terms.mk_bvand(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, and_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, and_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvand a b) and (bvand b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_commutative_bvor() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let or_ab = terms.mk_bvor(vec![a, b]);
    let or_ba = terms.mk_bvor(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, or_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, or_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvor a b) and (bvor b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_commutative_bvxor() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let xor_ab = terms.mk_bvxor(vec![a, b]);
    let xor_ba = terms.mk_bvxor(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, xor_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, xor_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvxor a b) and (bvxor b a) should normalize to same term"
    );
}

#[test]
fn test_bvsub_not_normalized() {
    // bvsub is NOT commutative: a - b != b - a
    // The pass should NOT normalize bvsub
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let sub_ab = terms.mk_bvsub(vec![a, b]);
    let sub_ba = terms.mk_bvsub(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, sub_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, sub_ba);

    // They should remain different (not normalized to same form)
    assert_ne!(
        norm_ab, norm_ba,
        "bvsub should NOT be normalized (non-commutative)"
    );
}

#[test]
fn test_rebuilds_constant_bv_guards_inside_ite() {
    let mut terms = TermStore::new();

    let zero = terms.mk_bitvec(BigInt::from(0u8), 8);
    let one = terms.mk_bitvec(BigInt::from(1u8), 8);
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let guard = terms.mk_app(Symbol::named("bvult"), vec![zero, one], Sort::Bool);
    let ite = terms.mk_ite(guard, x, y);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, ite);

    assert_eq!(
        normalized, x,
        "constant BV guards parsed as raw apps must fold so surrounding ITEs collapse"
    );
}

#[test]
fn test_equality_rebuild_keeps_ite_side_structural_11936() {
    let mut terms = TermStore::new();

    let cond = terms.mk_var("cond", Sort::Bool);
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let ite = terms.mk_ite(cond, a, b);
    let eq = terms.mk_eq_coerce_no_ite_expand(ite, a);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, eq);

    let TermData::App(sym, args) = terms.get(normalized) else {
        panic!(
            "NormalizeBvArith should keep equality structural, got {:?}",
            terms.get(normalized)
        );
    };
    assert_eq!(sym.name(), "=");
    assert_eq!(args.len(), 2);
    assert!(
        args.contains(&ite),
        "ITE side should remain under structural equality"
    );
    assert!(
        args.contains(&a),
        "branch value should remain equality side"
    );
}

#[test]
fn test_equality_rebuild_keeps_bool_ite_to_false_structural_11936() {
    let mut terms = TermStore::new();

    let cond = terms.mk_var("cond", Sort::Bool);
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let ite = terms.mk_ite(cond, a, b);
    let false_term = terms.mk_bool(false);
    let eq = terms.mk_app(Symbol::named("="), vec![ite, false_term], Sort::Bool);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, eq);

    let TermData::App(sym, args) = terms.get(normalized) else {
        panic!(
            "NormalizeBvArith should keep Boolean ITE equality structural, got {:?}",
            terms.get(normalized)
        );
    };
    assert_eq!(sym.name(), "=");
    assert_eq!(args.len(), 2);
    assert!(
        args.contains(&ite),
        "Boolean ITE side should remain under structural equality"
    );
    assert!(
        args.contains(&false_term),
        "false side should remain equality side"
    );
}

#[test]
fn test_flatten_left_deep_bvand_does_not_overflow() {
    let mut terms = TermStore::new();

    let first = terms.mk_var("x0", Sort::bitvec(8));
    let mut acc = first;
    let mut last = first;

    for i in 1..30_000 {
        last = terms.mk_var(format!("x{i}"), Sort::bitvec(8));
        acc = terms.mk_bvand(vec![acc, last]);
    }

    let TermData::App(sym, args) = terms.get(acc).clone() else {
        panic!("expected left-deep bvand application");
    };

    let mut operands = Vec::new();
    NormalizeBvArith::flatten_op(&terms, sym.name(), 8, &args, &mut operands);

    assert_eq!(operands.len(), 30_000);
    assert_eq!(operands.first(), Some(&first));
    assert_eq!(operands.last(), Some(&last));
}
