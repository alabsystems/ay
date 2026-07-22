// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Track B batch 2: `mk_ext.rs`, `fpa_ext.rs`, `propagate.rs`.
//!
//! Real builders are checked to produce well-sorted non-null terms; divergence
//! functions are checked to return a sound sentinel + documented error code.

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
fn fpa_sort_aliases_have_right_bits() {
    unsafe {
        let c = ctx();
        let s16 = Z3_mk_fpa_sort_16(c);
        let s32 = Z3_mk_fpa_sort_32(c);
        let s64 = Z3_mk_fpa_sort_64(c);
        let s128 = Z3_mk_fpa_sort_128(c);
        assert_eq!(
            (Z3_fpa_get_ebits(c, s16), Z3_fpa_get_sbits(c, s16)),
            (5, 11)
        );
        assert_eq!(
            (Z3_fpa_get_ebits(c, s32), Z3_fpa_get_sbits(c, s32)),
            (8, 24)
        );
        assert_eq!(
            (Z3_fpa_get_ebits(c, s64), Z3_fpa_get_sbits(c, s64)),
            (11, 53)
        );
        assert_eq!(
            (Z3_fpa_get_ebits(c, s128), Z3_fpa_get_sbits(c, s128)),
            (15, 113)
        );
        // ebits/sbits on a non-FP sort → sound sentinel.
        let int = Z3_mk_int_sort(c);
        assert_eq!(Z3_fpa_get_ebits(c, int), 0);
        Z3_del_context(c);
    }
}

#[test]
fn mk_real_builders_are_well_sorted() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let a = Z3_mk_const(c, Z3_mk_string_symbol(c, c"a".as_ptr()), int);
        let b = Z3_mk_const(c, Z3_mk_string_symbol(c, c"b".as_ptr()), int);
        // divides: (t1 | t2) is a Bool
        let div = Z3_mk_divides(c, a, b);
        assert_ne!(div, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, div)), Z3_BOOL_SORT);

        // bit2bool: bit 0 of an 8-bit value is a Bool
        let bv8 = Z3_mk_bv_sort(c, 8);
        let v = Z3_mk_int(c, 5, bv8);
        let bit = Z3_mk_bit2bool(c, 0, v);
        assert_ne!(bit, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, bit)), Z3_BOOL_SORT);
        Z3_del_context(c);
    }
}

#[test]
fn mk_tuple_sort_roundtrip() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let real = Z3_mk_real_sort(c);
        let field_names = [
            Z3_mk_string_symbol(c, c"fst".as_ptr()),
            Z3_mk_string_symbol(c, c"snd".as_ptr()),
        ];
        let field_sorts = [int, real];
        let mut mk_decl: Z3_func_decl = ptr::null_mut();
        let mut proj: [Z3_func_decl; 2] = [ptr::null_mut(); 2];
        let tup = Z3_mk_tuple_sort(
            c,
            Z3_mk_string_symbol(c, c"Pair".as_ptr()),
            2,
            field_names.as_ptr(),
            field_sorts.as_ptr(),
            &raw mut mk_decl,
            proj.as_mut_ptr(),
        );
        assert!(!tup.is_null());
        // The Wave G getter should now report 2 fields for this tuple.
        assert_eq!(Z3_get_tuple_sort_num_fields(c, tup), 2);
        assert!(!mk_decl.is_null());
        Z3_del_context(c);
    }
}

#[test]
fn mk_char_sort_is_real() {
    unsafe {
        let c = ctx();
        // The char sort is now REAL: it reports Z3_CHAR_SORT and is_char_sort.
        let s = Z3_mk_char_sort(c);
        assert!(!s.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_get_sort_kind(c, s), Z3_CHAR_SORT);
        assert!(Z3_is_char_sort(c, s));
        // The two char↔BV bridges are REAL (width 18, pinned against libz3
        // 4.16.0 — see feasible_tier_tests for the solve-level suite).
        let lit = Z3_mk_char(c, 65);
        assert_ne!(lit, 0);
        assert_ne!(Z3_mk_char_to_bv(c, lit), 0, "to_bv is a REAL BV18 term");
        // from_bv demands a BV18 argument; a Char argument is a sort error in
        // BOTH libs ("expected bit-vector sort argument with 18").
        assert_eq!(Z3_mk_char_from_bv(c, lit), 0);
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}

#[test]
fn user_propagator_registration_is_real() {
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        // Registering a user propagator is now REAL (sound final-check loop;
        // see propagate_tests.rs for the behavioral suite): init succeeds.
        Z3_solver_propagate_init(c, s, ptr::null_mut(), None, None, None);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // And the param descrs are a real queryable list.
        let pd = Z3_solver_get_param_descrs(c, s);
        assert!(!pd.is_null());
        Z3_del_context(c);
    }
}
