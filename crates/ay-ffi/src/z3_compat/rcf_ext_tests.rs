// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the REAL transcendental (π, e) and infinitesimal RCF extensions
//! (`rcf.rs` + `rcf_series.rs`).
//!
//! Every `true`/`false`/ordering asserted here is EXACT: enclosure-refined
//! strict orderings against provably-distinct values, exact coefficient
//! identity for equalities, and the lexicographic ℚ((ε)) order for
//! infinitesimals. Unsupported mixes must raise `Z3_EXCEPTION` with a sound
//! null/false sentinel — never a guess.

use std::ffi::CStr;

use super::super::*;

unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn rat(c: Z3_context, s: &CStr) -> Z3_rcf_num {
    let h = unsafe { Z3_rcf_mk_rational(c, s.as_ptr()) };
    assert!(!h.is_null());
    h
}

/// √2 as the positive root of `x^2 - 2`.
unsafe fn sqrt2(c: Z3_context) -> Z3_rcf_num {
    unsafe {
        let coeffs = [
            Z3_rcf_mk_small_int(c, -2),
            Z3_rcf_mk_small_int(c, 0),
            Z3_rcf_mk_small_int(c, 1),
        ];
        let mut roots: [Z3_rcf_num; 3] = [ptr::null_mut(); 3];
        let n = Z3_rcf_mk_roots(c, 3, coeffs.as_ptr(), roots.as_mut_ptr());
        assert_eq!(n, 2);
        roots[1]
    }
}

#[test]
fn pi_and_e_order_against_rationals() {
    unsafe {
        let c = ctx();
        let pi = Z3_rcf_mk_pi(c);
        let e = Z3_rcf_mk_e(c);
        assert!(!pi.is_null() && !e.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        // π > 3 and π < 22/7 (the classic Archimedes bracket).
        assert!(Z3_rcf_gt(c, pi, Z3_rcf_mk_small_int(c, 3)));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_rcf_lt(c, pi, rat(c, c"22/7")));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // Tighter: 3.14159 < π < 3.1416.
        assert!(Z3_rcf_gt(c, pi, rat(c, c"3.14159")));
        assert!(Z3_rcf_lt(c, pi, rat(c, c"3.1416")));

        // 2 < e < 3, and tighter: 2.71828 < e < 2.71829.
        assert!(Z3_rcf_lt(c, e, Z3_rcf_mk_small_int(c, 3)));
        assert!(Z3_rcf_gt(c, e, Z3_rcf_mk_small_int(c, 2)));
        assert!(Z3_rcf_gt(c, e, rat(c, c"2.71828")));
        assert!(Z3_rcf_lt(c, e, rat(c, c"2.71829")));

        // e < π (mixed-kind comparison separates under refinement).
        assert!(Z3_rcf_lt(c, e, pi));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_rcf_neq(c, e, pi));

        // π > √2 (transcendental vs algebraic, exact separation).
        let s2 = sqrt2(c);
        assert!(Z3_rcf_gt(c, pi, s2));
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        Z3_del_context(c);
    }
}

#[test]
fn pi_linear_form_arithmetic_is_exact_and_bounded() {
    unsafe {
        let c = ctx();
        let pi = Z3_rcf_mk_pi(c);
        let one = Z3_rcf_mk_small_int(c, 1);
        let two = Z3_rcf_mk_small_int(c, 2);

        // π + 1 ∈ (4.14, 4.15); 2·e ∈ (5.43, 5.44).
        let pi1 = Z3_rcf_add(c, pi, one);
        assert!(!pi1.is_null());
        assert!(Z3_rcf_gt(c, pi1, rat(c, c"4.14")));
        assert!(Z3_rcf_lt(c, pi1, rat(c, c"4.15")));
        let e = Z3_rcf_mk_e(c);
        let e2 = Z3_rcf_mul(c, two, e);
        assert!(!e2.is_null());
        assert!(Z3_rcf_gt(c, e2, rat(c, c"5.43")));
        assert!(Z3_rcf_lt(c, e2, rat(c, c"5.44")));

        // Exact symbolic identities: (π + 1) − 1 == π; π − π == 0 (coefficient
        // identity, no numeric proximity anywhere).
        let back = Z3_rcf_sub(c, pi1, one);
        assert!(Z3_rcf_eq(c, back, pi));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let zero = Z3_rcf_sub(c, pi, pi);
        assert!(Z3_rcf_is_rational(c, zero));
        assert!(Z3_rcf_eq(c, zero, Z3_rcf_mk_small_int(c, 0)));

        // Classification is exact: π is transcendental, not rational, not
        // algebraic — and so is π + 1.
        assert!(Z3_rcf_is_transcendental(c, pi));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_rcf_is_rational(c, pi));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_rcf_is_algebraic(c, pi));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_rcf_is_infinitesimal(c, pi));
        assert!(Z3_rcf_is_transcendental(c, pi1));

        // Symbolic rendering.
        let txt = CStr::from_ptr(Z3_rcf_num_to_string(c, pi, false, false))
            .to_str()
            .expect("pi rendering must be valid UTF-8")
            .to_string();
        assert_eq!(txt, "pi");
        let txt1 = CStr::from_ptr(Z3_rcf_num_to_string(c, pi1, false, false))
            .to_str()
            .expect("pi-plus-one rendering must be valid UTF-8")
            .to_string();
        assert_eq!(txt1, "(+ 1 pi)");

        Z3_del_context(c);
    }
}

#[test]
fn unsupported_transcendental_operations_error_honestly() {
    unsafe {
        let c = ctx();
        let pi = Z3_rcf_mk_pi(c);
        let e = Z3_rcf_mk_e(c);

        // π + e: mixed transcendentals → EXCEPTION + null, never a guess.
        assert!(Z3_rcf_add(c, pi, e).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        // π·π (quadratic), 1/π (not a linear form), π² via power.
        assert!(Z3_rcf_mul(c, pi, pi).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(Z3_rcf_inv(c, pi).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(Z3_rcf_power(c, pi, 2).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        // ...but π⁰ = 1 and π¹ = π stay real.
        assert!(Z3_rcf_eq(
            c,
            Z3_rcf_power(c, pi, 0),
            Z3_rcf_mk_small_int(c, 1)
        ));
        assert!(Z3_rcf_eq(c, Z3_rcf_power(c, pi, 1), pi));

        // Algebraic + transcendental: outside the linear form → EXCEPTION.
        let s2 = sqrt2(c);
        assert!(Z3_rcf_add(c, s2, pi).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(Z3_rcf_mul(c, s2, pi).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        // Defining-polynomial introspection has no meaning for π → EXCEPTION.
        assert_eq!(Z3_rcf_num_coefficients(c, pi), 0);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        Z3_del_context(c);
    }
}

#[test]
fn infinitesimal_order_is_the_exact_lex_order() {
    unsafe {
        let c = ctx();
        let eps = Z3_rcf_mk_infinitesimal(c);
        assert!(!eps.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let zero = Z3_rcf_mk_small_int(c, 0);

        // ε > 0, and ε < q for every positive rational q (a few samples,
        // including very small ones).
        assert!(Z3_rcf_gt(c, eps, zero));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        for q in [c"1", c"1/2", c"1/1000", c"1/1000000000000", c"3.0"] {
            let q = rat(c, q);
            assert!(
                Z3_rcf_lt(c, eps, q),
                "eps must be below every positive rational"
            );
            assert_eq!(Z3_get_error_code(c), Z3_OK);
        }

        // ε ≠ 0 and −ε < 0 < ε.
        assert!(Z3_rcf_neq(c, eps, zero));
        let neg = Z3_rcf_neg(c, eps);
        assert!(Z3_rcf_lt(c, neg, zero));
        assert!(Z3_rcf_lt(c, neg, eps));

        // ε² > 0 and ε² < ε (higher-order terms are smaller).
        let eps2 = Z3_rcf_mul(c, eps, eps);
        assert!(!eps2.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_rcf_gt(c, eps2, zero));
        assert!(Z3_rcf_lt(c, eps2, eps));

        // 1 + ε sits strictly between 1 and every rational above 1.
        let one = Z3_rcf_mk_small_int(c, 1);
        let one_eps = Z3_rcf_add(c, one, eps);
        assert!(Z3_rcf_gt(c, one_eps, one));
        assert!(Z3_rcf_lt(c, one_eps, rat(c, c"1.000001")));

        // Exact identities: ε − ε == 0; ε + ε == 2·ε.
        assert!(Z3_rcf_eq(c, Z3_rcf_sub(c, eps, eps), zero));
        let two_eps = Z3_rcf_mul(c, Z3_rcf_mk_small_int(c, 2), eps);
        assert!(Z3_rcf_eq(c, Z3_rcf_add(c, eps, eps), two_eps));

        // Classification is exact.
        assert!(Z3_rcf_is_infinitesimal(c, eps));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_rcf_is_rational(c, eps));
        assert!(!Z3_rcf_is_algebraic(c, eps));
        assert!(!Z3_rcf_is_transcendental(c, eps));
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        Z3_del_context(c);
    }
}

#[test]
fn one_over_eps_is_exact_in_the_laurent_representation() {
    unsafe {
        let c = ctx();
        let eps = Z3_rcf_mk_infinitesimal(c);
        let one = Z3_rcf_mk_small_int(c, 1);

        // 1/ε is representable (Laurent exponent −1) and CORRECT: it exceeds
        // every rational, and (1/ε)·ε == 1 exactly.
        let inv = Z3_rcf_inv(c, eps);
        assert!(!inv.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        for q in [c"1000000", c"1000000000000"] {
            assert!(
                Z3_rcf_gt(c, inv, rat(c, q)),
                "1/eps must exceed every rational"
            );
        }
        assert!(Z3_rcf_eq(c, Z3_rcf_mul(c, inv, eps), one));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // Same via division.
        let div = Z3_rcf_div(c, one, eps);
        assert!(Z3_rcf_eq(c, div, inv));

        // 1/(1 + ε) is an INFINITE series → honest EXCEPTION, never truncated.
        let one_eps = Z3_rcf_add(c, one, eps);
        assert!(Z3_rcf_inv(c, one_eps).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        Z3_del_context(c);
    }
}

#[test]
fn unsupported_infinitesimal_mixes_error_honestly() {
    unsafe {
        let c = ctx();
        let eps = Z3_rcf_mk_infinitesimal(c);
        let eps2 = Z3_rcf_mk_infinitesimal(c); // a DIFFERENT generator
        let pi = Z3_rcf_mk_pi(c);
        let s2 = sqrt2(c);

        // Two different infinitesimal generators do not mix.
        assert!(Z3_rcf_add(c, eps, eps2).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(Z3_rcf_mul(c, eps, eps2).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(!Z3_rcf_lt(c, eps, eps2));
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        // ε does not mix with π or with a genuine algebraic in arithmetic.
        assert!(Z3_rcf_add(c, eps, pi).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(Z3_rcf_add(c, eps, s2).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        // ...but ORDERING against π and algebraics is exact and real:
        // ε < √2 and ε < π (standard parts 0 vs positive reals).
        assert!(Z3_rcf_lt(c, eps, s2));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_rcf_lt(c, eps, pi));
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        Z3_del_context(c);
    }
}

#[test]
fn extension_names_and_indices_are_real() {
    unsafe {
        let c = ctx();
        let pi = Z3_rcf_mk_pi(c);
        let e = Z3_rcf_mk_e(c);
        let eps_a = Z3_rcf_mk_infinitesimal(c);
        let eps_b = Z3_rcf_mk_infinitesimal(c);

        // Tower indices: π = 1, e = 2, infinitesimals from 3 in creation order.
        assert_eq!(Z3_rcf_extension_index(c, pi), 1);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_rcf_extension_index(c, e), 2);
        assert_eq!(Z3_rcf_extension_index(c, eps_a), 3);
        assert_eq!(Z3_rcf_extension_index(c, eps_b), 4);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // A rational violates the precondition → EXCEPTION + 0.
        assert_eq!(Z3_rcf_extension_index(c, Z3_rcf_mk_small_int(c, 7)), 0);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        // Names.
        let pi_name = CStr::from_ptr(Z3_get_symbol_string(c, Z3_rcf_transcendental_name(c, pi)))
            .to_str()
            .expect("pi symbol name must be valid UTF-8")
            .to_string();
        assert_eq!(pi_name, "pi");
        let e_name = CStr::from_ptr(Z3_get_symbol_string(c, Z3_rcf_transcendental_name(c, e)))
            .to_str()
            .expect("e symbol name must be valid UTF-8")
            .to_string();
        assert_eq!(e_name, "e");
        let eps_name = CStr::from_ptr(Z3_get_symbol_string(c, Z3_rcf_infinitesimal_name(c, eps_a)))
            .to_str()
            .expect("infinitesimal symbol name must be valid UTF-8")
            .to_string();
        assert_eq!(eps_name, "eps!3");
        // Wrong-kind name queries violate the precondition.
        assert!(Z3_rcf_infinitesimal_name(c, pi).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(Z3_rcf_transcendental_name(c, eps_a).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        Z3_del_context(c);
    }
}

#[test]
fn decimal_strings_match_known_digits() {
    unsafe {
        let c = ctx();
        let pi = Z3_rcf_mk_pi(c);
        let e = Z3_rcf_mk_e(c);
        let eps = Z3_rcf_mk_infinitesimal(c);

        let dec = |h: Z3_rcf_num, prec: u32| -> String {
            let p = Z3_rcf_num_to_decimal_string(c, h, prec);
            assert!(!p.is_null());
            CStr::from_ptr(p)
                .to_str()
                .expect("RCF decimal rendering must be valid UTF-8")
                .to_string()
        };

        // Known truncated digits, with the display-only `?` marker.
        assert_eq!(dec(pi, 10), "3.1415926535?");
        assert_eq!(dec(e, 5), "2.71828?");
        assert_eq!(dec(pi, 0), "3?");

        // ε truncates to exact zeros; 1/2 − ε dips just below the grid point.
        assert_eq!(dec(eps, 3), "0.000?");
        let half_minus_eps = Z3_rcf_sub(c, rat(c, c"1/2"), eps);
        assert_eq!(dec(half_minus_eps, 3), "0.499?");
        let half_plus_eps = Z3_rcf_add(c, rat(c, c"1/2"), eps);
        assert_eq!(dec(half_plus_eps, 3), "0.500?");

        // 1/ε has infinite magnitude → honest EXCEPTION.
        let inv = Z3_rcf_inv(c, eps);
        assert!(Z3_rcf_num_to_decimal_string(c, inv, 3).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);

        Z3_del_context(c);
    }
}

#[test]
fn decimal_string_rejects_unbounded_precision_before_allocating() {
    unsafe {
        let c = ctx();
        let one_third = rat(c, c"1/3");
        assert!(Z3_rcf_num_to_decimal_string(c, one_third, u32::MAX).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        Z3_del_context(c);
    }
}

#[test]
fn transcendental_interval_is_a_rigorous_enclosure() {
    unsafe {
        let c = ctx();
        let pi = Z3_rcf_mk_pi(c);
        let mut lo_inf = true;
        let mut lo_open = false;
        let mut hi_inf = true;
        let mut hi_open = false;
        let mut lo: Z3_rcf_num = ptr::null_mut();
        let mut hi: Z3_rcf_num = ptr::null_mut();
        let ok = Z3_rcf_interval(
            c,
            pi,
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
        // The endpoints genuinely bracket π: lo < π < hi, and lo > 3, hi < 22/7.
        assert!(Z3_rcf_lt(c, lo, pi));
        assert!(Z3_rcf_gt(c, hi, pi));
        assert!(Z3_rcf_gt(c, lo, Z3_rcf_mk_small_int(c, 3)));
        assert!(Z3_rcf_lt(c, hi, rat(c, c"22/7")));

        Z3_del_context(c);
    }
}
