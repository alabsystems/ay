// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the REAL Real-Closed-Field / algebraic-number C API (`rcf.rs`,
//! `algebraic.rs`, `engine_local.rs`), backed by the exact `ay_nra` engine.
//!
//! Exercises the whole √2 story end-to-end: build √2 as a root of `x^2 - 2`, do
//! exact field arithmetic and GCD-certified comparisons on it, introspect its
//! defining polynomial / interval / Thom sign conditions, and confirm the
//! transcendental / infinitesimal surface stays honest divergence.

use std::ffi::{CStr, CString};

use super::super::*;

unsafe fn ctx() -> Z3_context {
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

#[test]
fn rcf_rational_caps_caller_text_before_bigint_parsing() {
    unsafe {
        let c = ctx();
        let boundary = CString::new(format!("1{}", "0".repeat(MAX_FFI_NUMERAL_TEXT_BYTES - 1)))
            .expect("boundary rational contains no NUL");
        assert!(!Z3_rcf_mk_rational(c, boundary.as_ptr()).is_null());

        let oversized = CString::new("1".repeat(MAX_FFI_NUMERAL_TEXT_BYTES + 1))
            .expect("oversized rational contains no NUL");
        assert!(Z3_rcf_mk_rational(c, oversized.as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        Z3_del_context(c);
    }
}

/// √2 as the positive root of `x^2 - 2` via `Z3_rcf_mk_roots`, with the two
/// roots (ascending: -√2, √2).
unsafe fn sqrt2_via_roots(c: Z3_context) -> (Z3_rcf_num, Z3_rcf_num) {
    unsafe {
        // Coefficients low-to-high: -2 + 0*x + 1*x^2.
        let coeffs = [
            Z3_rcf_mk_small_int(c, -2),
            Z3_rcf_mk_small_int(c, 0),
            Z3_rcf_mk_small_int(c, 1),
        ];
        let mut roots: [Z3_rcf_num; 3] = [ptr::null_mut(); 3];
        let n = Z3_rcf_mk_roots(c, 3, coeffs.as_ptr(), roots.as_mut_ptr());
        assert_eq!(n, 2, "x^2 - 2 has exactly two real roots");
        // `c` is a valid context per this helper's own safety contract (the
        // enclosing unsafe block covers this call).
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        (roots[0], roots[1]) // (-√2, √2)
    }
}

#[test]
fn rcf_sqrt2_arithmetic_and_order() {
    unsafe {
        let c = ctx();
        let (neg_sqrt2, sqrt2) = sqrt2_via_roots(c);

        // Classification: √2 is a genuine algebraic, not a rational.
        assert!(Z3_rcf_is_algebraic(c, sqrt2));
        assert!(!Z3_rcf_is_rational(c, sqrt2));

        // √2 * √2 == 2 exactly (collapses to the rational 2, GCD-certified eq).
        let two = Z3_rcf_mk_small_int(c, 2);
        let sq = Z3_rcf_mul(c, sqrt2, sqrt2);
        assert!(Z3_rcf_eq(c, sq, two));
        assert!(Z3_rcf_is_rational(c, sq));

        // √2 + (−√2) == 0.
        let sum = Z3_rcf_add(c, sqrt2, neg_sqrt2);
        let zero = Z3_rcf_mk_small_int(c, 0);
        assert!(Z3_rcf_eq(c, sum, zero));
        // ...and via explicit negation too.
        let sum2 = Z3_rcf_add(c, sqrt2, Z3_rcf_neg(c, sqrt2));
        assert!(Z3_rcf_eq(c, sum2, zero));

        // √2 ≈ 1.414: √2 < 3/2 (TRUE), √2 < 7/5 (FALSE), √2 > 7/5 (TRUE).
        let three_halves = Z3_rcf_mk_rational(c, c"3/2".as_ptr());
        let seven_fifths = Z3_rcf_mk_rational(c, c"7/5".as_ptr());
        assert!(Z3_rcf_lt(c, sqrt2, three_halves));
        assert!(!Z3_rcf_lt(c, sqrt2, seven_fifths));
        assert!(Z3_rcf_gt(c, sqrt2, seven_fifths));
        assert!(Z3_rcf_ge(c, sqrt2, sqrt2));
        assert!(Z3_rcf_le(c, sqrt2, sqrt2));
        assert!(Z3_rcf_neq(c, sqrt2, neg_sqrt2));

        // Decimal literal parsing: 1.5 == 3/2.
        let one_point_five = Z3_rcf_mk_rational(c, c"1.5".as_ptr());
        assert!(Z3_rcf_eq(c, one_point_five, three_halves));

        Z3_del_context(c);
    }
}

#[test]
fn rcf_sqrt2_div_inv_power() {
    unsafe {
        let c = ctx();
        let (_, sqrt2) = sqrt2_via_roots(c);
        let two = Z3_rcf_mk_small_int(c, 2);

        // (√2)^2 == 2.
        let p2 = Z3_rcf_power(c, sqrt2, 2);
        assert!(Z3_rcf_eq(c, p2, two));

        // 1/√2 * √2 == 1.
        let inv = Z3_rcf_inv(c, sqrt2);
        let one = Z3_rcf_mk_small_int(c, 1);
        assert!(Z3_rcf_eq(c, Z3_rcf_mul(c, inv, sqrt2), one));

        // 2 / √2 == √2.
        let div = Z3_rcf_div(c, two, sqrt2);
        assert!(Z3_rcf_eq(c, div, sqrt2));

        // 1/0 fails closed (EXCEPTION + null), never a fabricated value.
        let zero = Z3_rcf_mk_small_int(c, 0);
        let bad = Z3_rcf_inv(c, zero);
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        Z3_del_context(c);
    }
}

#[test]
fn compact_algebraic_exponents_are_bounded_before_work() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let two_ast = Z3_mk_numeral(c, c"2".as_ptr(), real);

        assert_eq!(Z3_algebraic_power(c, two_ast, u32::MAX), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_algebraic_root(c, two_ast, u32::MAX), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        let two_rcf = Z3_rcf_mk_small_int(c, 2);
        assert!(Z3_rcf_power(c, two_rcf, u32::MAX).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        Z3_del_context(c);
    }
}

#[test]
fn rcf_sqrt2_introspection() {
    unsafe {
        let c = ctx();
        let (_, sqrt2) = sqrt2_via_roots(c);

        // Defining polynomial x^2 - 2: coefficients [-2, 0, 1] low-to-high.
        assert_eq!(Z3_rcf_num_coefficients(c, sqrt2), 3);
        let c0 = Z3_rcf_coefficient(c, sqrt2, 0);
        let c1 = Z3_rcf_coefficient(c, sqrt2, 1);
        let c2 = Z3_rcf_coefficient(c, sqrt2, 2);
        assert!(Z3_rcf_eq(c, c0, Z3_rcf_mk_small_int(c, -2)));
        assert!(Z3_rcf_eq(c, c1, Z3_rcf_mk_small_int(c, 0)));
        assert!(Z3_rcf_eq(c, c2, Z3_rcf_mk_small_int(c, 1)));

        // root-obj rendering (z3 parity).
        let s = Z3_rcf_num_to_string(c, sqrt2, true, false);
        assert!(!s.is_null());
        assert_eq!(
            CStr::from_ptr(s)
                .to_str()
                .expect("RCF root-object rendering must be valid UTF-8"),
            "(root-obj (+ (^ x 2) (- 2)) 2)"
        );

        // Decimal rendering (approximate, marked with '?').
        let d = Z3_rcf_num_to_decimal_string(c, sqrt2, 4);
        assert!(!d.is_null());
        let dtext = CStr::from_ptr(d)
            .to_str()
            .expect("RCF decimal rendering must be valid UTF-8");
        assert_eq!(dtext, "1.4142?", "got {dtext}");

        // Isolating interval: open, finite, lower < upper, both bracket √2.
        let mut lo_inf = true;
        let mut lo_open = false;
        let mut hi_inf = true;
        let mut hi_open = false;
        let mut lo: Z3_rcf_num = ptr::null_mut();
        let mut hi: Z3_rcf_num = ptr::null_mut();
        let ok = Z3_rcf_interval(
            c,
            sqrt2,
            &raw mut lo_inf,
            &raw mut lo_open,
            &raw mut lo,
            &raw mut hi_inf,
            &raw mut hi_open,
            &raw mut hi,
        );
        assert_eq!(ok, 1);
        assert!(!lo_inf && !hi_inf && lo_open && hi_open);
        assert!(!lo.is_null() && !hi.is_null());
        assert!(Z3_rcf_lt(c, lo, sqrt2));
        assert!(Z3_rcf_lt(c, sqrt2, hi));

        // Numerator/denominator on a rational.
        let mut num: Z3_rcf_num = ptr::null_mut();
        let mut den: Z3_rcf_num = ptr::null_mut();
        let three_quarters = Z3_rcf_mk_rational(c, c"3/4".as_ptr());
        Z3_rcf_get_numerator_denominator(c, three_quarters, &raw mut num, &raw mut den);
        assert!(Z3_rcf_eq(c, num, Z3_rcf_mk_small_int(c, 3)));
        assert!(Z3_rcf_eq(c, den, Z3_rcf_mk_small_int(c, 4)));

        Z3_del_context(c);
    }
}

#[test]
fn rcf_sqrt2_thom_sign_conditions() {
    unsafe {
        let c = ctx();
        let (neg_sqrt2, sqrt2) = sqrt2_via_roots(c);

        // Defining poly degree 2 → exactly one Thom condition (sign of p' = 2x).
        assert_eq!(Z3_rcf_num_sign_conditions(c, sqrt2), 1);
        // p'(√2) = 2√2 > 0, p'(−√2) = −2√2 < 0 → the two roots are distinguished.
        assert_eq!(Z3_rcf_sign_condition_sign(c, sqrt2, 0), 1);
        assert_eq!(Z3_rcf_sign_condition_sign(c, neg_sqrt2, 0), -1);
        // p' = 2x has coefficients [0, 2].
        assert_eq!(Z3_rcf_num_sign_condition_coefficients(c, sqrt2, 0), 2);
        let coeff1 = Z3_rcf_sign_condition_coefficient(c, sqrt2, 0, 1);
        assert!(Z3_rcf_eq(c, coeff1, Z3_rcf_mk_small_int(c, 2)));

        // A rational has no sign conditions.
        let rat = Z3_rcf_mk_rational(c, c"5/1".as_ptr());
        assert_eq!(Z3_rcf_num_sign_conditions(c, rat), 0);

        Z3_del_context(c);
    }
}

#[test]
fn rcf_transcendental_infinitesimal_now_real() {
    unsafe {
        let c = ctx();
        let (_, sqrt2) = sqrt2_via_roots(c);

        // Constructors are now REAL symbolic elements (see rcf_ext_tests.rs
        // for the full behavioral suite).
        assert!(!Z3_rcf_mk_pi(c).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_rcf_mk_e(c).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_rcf_mk_infinitesimal(c).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        // Classification over an ALGEBRAIC value answers exactly (√2 is
        // neither transcendental nor infinitesimal): false + Z3_OK.
        assert!(!Z3_rcf_is_transcendental(c, sqrt2));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_rcf_is_infinitesimal(c, sqrt2));
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        // Name / extension-index accessors on a NON-extension operand violate
        // z3's precondition: null / 0 + EXCEPTION (honest, never fabricated).
        assert!(Z3_rcf_transcendental_name(c, sqrt2).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(Z3_rcf_infinitesimal_name(c, sqrt2).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert_eq!(Z3_rcf_extension_index(c, sqrt2), 0);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        Z3_del_context(c);
    }
}

#[test]
fn algebraic_layer_root_and_bounds() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let two = Z3_mk_numeral(c, c"2".as_ptr(), real);

        // Z3_algebraic_root(2, 2) = √2 (the exact 2nd root of x^2 - 2).
        let r = Z3_algebraic_root(c, two, 2);
        assert_ne!(r, 0);
        assert!(Z3_algebraic_is_value(c, r));
        assert!(Z3_algebraic_is_pos(c, r));
        assert_eq!(Z3_algebraic_get_i(c, r), 2);

        // Defining polynomial coefficients [-2, 0, 1].
        let poly = Z3_algebraic_get_poly(c, r);
        assert_eq!(Z3_ast_vector_size(c, poly), 3);
        let coeff = |i| {
            let a = Z3_ast_vector_get(c, poly, i);
            CStr::from_ptr(Z3_ast_to_string(c, a))
                .to_str()
                .expect("algebraic coefficient rendering must be valid UTF-8")
                .to_string()
        };
        assert_eq!(coeff(0), "(- 2)");
        assert_eq!(coeff(2), "1");

        // r*r == 2, and r + (−r) == 0, over the algebraic AST layer.
        assert!(Z3_algebraic_eq(c, Z3_algebraic_mul(c, r, r), two));
        let neg = Z3_algebraic_sub(c, Z3_mk_numeral(c, c"0".as_ptr(), real), r);
        assert!(Z3_algebraic_is_neg(c, neg));

        // Isolating-interval endpoints refined to precision 10: lo < √2 < hi.
        let lo = Z3_get_algebraic_number_lower(c, r, 10);
        let hi = Z3_get_algebraic_number_upper(c, r, 10);
        assert_ne!(lo, 0);
        assert_ne!(hi, 0);
        // Both bounds are rational numerals bracketing √2 (lo^2 < 2 < hi^2).
        assert!(Z3_algebraic_lt(c, Z3_algebraic_mul(c, lo, lo), two));
        assert!(Z3_algebraic_gt(c, Z3_algebraic_mul(c, hi, hi), two));

        // Compact precision arguments must be bounded before constructing
        // `2^precision` or entering a precision-sized refinement loop.
        assert_eq!(Z3_get_algebraic_number_lower(c, r, u32::MAX), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_get_algebraic_number_upper(c, r, u32::MAX), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        Z3_del_context(c);
    }
}

#[test]
fn algebraic_handles_are_authenticated_to_their_context() {
    unsafe {
        let local = ctx();
        let foreign = ctx();
        let local_real = Z3_mk_real_sort(local);
        let foreign_real = Z3_mk_real_sort(foreign);

        // Deliberately store different exact values at the same arena index.
        // Without a context salt the foreign sqrt(2) handle would alias the
        // local sqrt(3) value.
        let local_three = Z3_mk_numeral(local, c"3".as_ptr(), local_real);
        let foreign_two = Z3_mk_numeral(foreign, c"2".as_ptr(), foreign_real);
        let local_sqrt3 = Z3_algebraic_root(local, local_three, 2);
        let foreign_sqrt2 = Z3_algebraic_root(foreign, foreign_two, 2);
        assert_ne!(local_sqrt3, 0);
        assert_ne!(foreign_sqrt2, 0);
        assert_eq!(
            local_sqrt3 & TAGGED_AST_INDEX_MASK,
            foreign_sqrt2 & TAGGED_AST_INDEX_MASK,
            "fixture must exercise colliding algebraic-arena indices"
        );
        assert_ne!(local_sqrt3, foreign_sqrt2);

        assert!(!Z3_algebraic_is_value(local, foreign_sqrt2));
        assert!(!Z3_algebraic_is_pos(local, foreign_sqrt2));
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert!(Z3_ast_to_string(local, foreign_sqrt2).is_null());
        assert!(Z3_algebraic_is_pos(local, local_sqrt3));

        // AST vectors are heterogeneous Z3 containers, so authenticated
        // algebraic handles must round-trip just like term ASTs. A foreign
        // tagged handle must still fail closed instead of aliasing the local
        // arena entry with the same index.
        let values = Z3_mk_ast_vector(local);
        Z3_ast_vector_push(local, values, local_sqrt3);
        assert_eq!(Z3_ast_vector_get(local, values, 0), local_sqrt3);
        Z3_ast_vector_push(local, values, foreign_sqrt2);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert_eq!(Z3_ast_vector_size(local, values), 1);
        Z3_ast_vector_set(local, values, 0, foreign_sqrt2);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert_eq!(Z3_ast_vector_get(local, values, 0), local_sqrt3);

        Z3_del_context(foreign);
        Z3_del_context(local);
    }
}

#[test]
fn rcf_del_and_null_handles_are_sound() {
    unsafe {
        let c = ctx();
        // del of a real handle: bookkeeping no-op, no error.
        let v = Z3_rcf_mk_small_int(c, 7);
        Z3_rcf_del(c, v);
        // Predicates on a null handle: sound false + EXCEPTION, never a verdict.
        assert!(!Z3_rcf_is_rational(c, ptr::null_mut()));
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        // Arithmetic on a null operand: null + EXCEPTION.
        assert!(Z3_rcf_add(c, ptr::null_mut(), v).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        Z3_del_context(c);
    }
}
