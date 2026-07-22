// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the accessor long-tail (`getters_ext.rs`, Track B Wave G).
//!
//! Each real accessor is checked for the exact value AY's engine backs, and
//! each honest-divergence accessor is checked to return its sound sentinel AND
//! set the documented error code — never a fabricated value.

use std::ffi::CStr;

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
fn numeral_numerator_denominator() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        // 22/7
        let r = Z3_mk_numeral(c, c"22/7".as_ptr(), real);
        let num = Z3_get_numerator(c, r);
        let den = Z3_get_denominator(c, r);
        assert_ne!(num, 0);
        assert_ne!(den, 0);
        let ns = CStr::from_ptr(Z3_get_numeral_string(c, num))
            .to_str()
            .expect("numerator numeral string must be valid UTF-8");
        let ds = CStr::from_ptr(Z3_get_numeral_string(c, den))
            .to_str()
            .expect("denominator numeral string must be valid UTF-8");
        assert_eq!(ns, "22");
        assert_eq!(ds, "7");

        // An integer numeral: denominator is 1.
        let int = Z3_mk_int_sort(c);
        let i = Z3_mk_int(c, 5, int);
        let iden = Z3_get_denominator(c, i);
        let ids = CStr::from_ptr(Z3_get_numeral_string(c, iden))
            .to_str()
            .expect("integer denominator string must be valid UTF-8");
        assert_eq!(ids, "1");

        Z3_del_context(c);
    }
}

#[test]
fn numeral_double_and_small() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let r = Z3_mk_numeral(c, c"3/4".as_ptr(), real);
        assert!((Z3_get_numeral_double(c, r) - 0.75).abs() < 1e-9);

        let mut n: i64 = 0;
        let mut d: i64 = 0;
        assert!(Z3_get_numeral_rational_int64(c, r, &raw mut n, &raw mut d));
        assert_eq!((n, d), (3, 4));

        let mut n2: i64 = 0;
        let mut d2: i64 = 0;
        assert!(Z3_get_numeral_small(c, r, &raw mut n2, &raw mut d2));
        assert_eq!((n2, d2), (3, 4));

        // Non-numeral: false, error set for _small.
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        assert!(!Z3_get_numeral_small(c, x, &raw mut n2, &raw mut d2));
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        Z3_del_context(c);
    }
}

#[test]
fn numeral_binary_string_for_bv() {
    unsafe {
        let c = ctx();
        let bv8 = Z3_mk_bv_sort(c, 8);
        let v = Z3_mk_int(c, 5, bv8);
        let s = Z3_get_numeral_binary_string(c, v);
        assert!(!s.is_null());
        let bits = CStr::from_ptr(s)
            .to_str()
            .expect("bit-vector numeral string must be valid UTF-8");
        // libz3 renders the VALUE in minimal binary — it does NOT zero-pad to
        // the bit-vector width (measured: `bv8 5` → "101", not "00000101").
        assert_eq!(bits, "101");

        // Any non-negative integral numeral renders, `Int` included (libz3:
        // `int 5` → "101"); it is not a bit-vector-only getter.
        let int = Z3_mk_int_sort(c);
        let i = Z3_mk_int(c, 5, int);
        let s = Z3_get_numeral_binary_string(c, i);
        assert!(!s.is_null());
        assert_eq!(
            CStr::from_ptr(s)
                .to_str()
                .expect("integer binary numeral string must be valid UTF-8"),
            "101"
        );

        // A negative value has no binary rendering → null + INVALID_ARG.
        let neg = Z3_mk_int(c, -5, int);
        assert!(Z3_get_numeral_binary_string(c, neg).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        Z3_del_context(c);
    }
}

#[test]
fn term_depth() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        // leaf constant → depth 1
        assert_eq!(Z3_get_depth(c, x), 1);
        // Use an uninterpreted unary function (not flattened/normalized like
        // arithmetic) so nesting depth is exactly structural.
        let dom = [int];
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            1,
            dom.as_ptr(),
            int,
        );
        // (f x) → depth 2
        let fx_args = [x];
        let fx = Z3_mk_app(c, f, 1, fx_args.as_ptr());
        assert_eq!(Z3_get_depth(c, fx), 2);
        // (f (f x)) → depth 3
        let ffx_args = [fx];
        let ffx = Z3_mk_app(c, f, 1, ffx_args.as_ptr());
        assert_eq!(Z3_get_depth(c, ffx), 3);
        Z3_del_context(c);
    }
}

#[test]
fn sort_predicates_and_structure() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let seq = Z3_mk_seq_sort(c, int);
        let re = Z3_mk_re_sort(c, seq);
        let string = Z3_mk_string_sort(c);

        assert!(Z3_is_seq_sort(c, seq));
        assert!(!Z3_is_seq_sort(c, int));
        assert!(Z3_is_re_sort(c, re));
        assert!(!Z3_is_re_sort(c, seq));
        assert!(Z3_is_string_sort(c, string));
        assert!(Z3_is_seq_sort(c, string)); // a string is a sequence
        assert!(!Z3_is_char_sort(c, int)); // AY has no char sort

        // seq basis = element sort (int)
        let basis = Z3_get_seq_sort_basis(c, seq);
        assert!(!basis.is_null());
        assert_eq!(Z3_get_sort_kind(c, basis), Z3_INT_SORT);

        // re basis = String (monomorphic regex)
        let rbasis = Z3_get_re_sort_basis(c, re);
        assert!(!rbasis.is_null());
        assert_eq!(Z3_get_sort_kind(c, rbasis), Z3_SEQ_SORT);

        Z3_del_context(c);
    }
}

#[test]
fn array_arity_divergences() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let arr = Z3_mk_array_sort(c, int, int);
        assert_eq!(Z3_get_array_arity(c, arr), 1);
        let d0 = Z3_get_array_sort_domain_n(c, arr, 0);
        assert!(!d0.is_null());
        assert_eq!(Z3_get_sort_kind(c, d0), Z3_INT_SORT);
        // idx >= 1 is out of range (single-index arrays)
        assert!(Z3_get_array_sort_domain_n(c, arr, 1).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_IOB);

        // An Int is not a finite-domain sort: false, and the out-param is zeroed
        // (measured against libz3, which writes 0 rather than leaving the
        // caller's value in place). Relation sorts do not exist → sound sentinel.
        let mut sz: u64 = 123;
        assert!(!Z3_get_finite_domain_sort_size(c, int, &raw mut sz));
        assert_eq!(sz, 0);
        assert_eq!(Z3_get_relation_arity(c, int), 0);

        Z3_del_context(c);
    }
}

#[test]
fn registry_enumerators() {
    unsafe {
        let c = ctx();
        let nt = Z3_get_num_tactics(c);
        assert!(nt >= 12, "expected the curated tactic set, got {nt}");
        let name0 = CStr::from_ptr(Z3_get_tactic_name(c, 0))
            .to_str()
            .expect("registered tactic name must be valid UTF-8");
        assert!(!name0.is_empty());
        // out of range → null + IOB
        assert!(Z3_get_tactic_name(c, nt).is_null());

        let ns = Z3_get_num_simplifiers(c);
        assert!(ns >= 1);
        assert!(!Z3_get_simplifier_name(c, 0).is_null());

        Z3_del_context(c);
    }
}

#[test]
fn func_decl_id_stable_and_distinct() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let dom = [int, int];
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            2,
            dom.as_ptr(),
            int,
        );
        let g = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"g".as_ptr()),
            2,
            dom.as_ptr(),
            int,
        );
        let idf = Z3_get_func_decl_id(c, f);
        let idg = Z3_get_func_decl_id(c, g);
        assert_ne!(idf, idg);
        Z3_del_context(c);
    }
}

#[test]
fn divergence_sentinels_never_fabricate() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);

        // No algebraic numbers / as-array nodes / lambdas in AY.
        assert!(!Z3_is_algebraic_number(c, x));
        assert!(!Z3_is_as_array(c, x));
        assert!(!Z3_is_lambda(c, x));
        assert!(Z3_get_as_array_func_decl(c, x).is_null());

        // Quantifier id/skid attributes are not stored.
        assert!(Z3_get_quantifier_id(c, x).is_null());
        assert!(Z3_get_quantifier_skolem_id(c, x).is_null());

        // Well-sortedness: any live term is well-sorted by construction.
        assert!(Z3_is_well_sorted(c, x));

        Z3_del_context(c);
    }
}
