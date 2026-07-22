// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the group-A numeral-introspection and sort-structure getters.
//!
//! Every expected value below is the value libz3 4.15.4 returns for the same
//! call (verified by the twin build of `capi_numeral_sortstruct_consumer.c`
//! and an out-of-band probe): numerator/denominator of 3/4 are Int numerals
//! "3"/"4", `Z3_get_numeral_double(3/4)` is 0.75, binary of BV 10 is "1010",
//! `Z3_mk_array_sort_n([Int, Bool], Real)` has arity 2 with those domains, etc.

use std::ffi::{c_uint, CStr, CString};
use std::ptr;

use crate::z3_compat::*;

/// Fresh context; caller frees via `Z3_del_context`.
unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn num_str(c: Z3_context, a: Z3_ast) -> String {
    // SAFETY: the returned pointer is a context-owned NUL-terminated string.
    unsafe {
        let p = Z3_get_numeral_string(c, a);
        assert!(!p.is_null(), "expected a numeral string");
        CStr::from_ptr(p)
            .to_str()
            .expect("numeral string must be valid UTF-8")
            .to_string()
    }
}

#[test]
fn numerator_denominator_of_real_and_int() {
    // SAFETY: all handles are created and used within one context lifetime.
    unsafe {
        let c = ctx();
        let r = Z3_mk_real(c, 3, 4);
        assert_eq!(num_str(c, Z3_get_numerator(c, r)), "3");
        assert_eq!(num_str(c, Z3_get_denominator(c, r)), "4");
        // The numerator is an Int-sorted numeral, as in libz3.
        let num_sort = Z3_get_sort(c, Z3_get_numerator(c, r));
        assert_eq!(Z3_get_sort_kind(c, num_sort), Z3_INT_SORT);

        let neg = {
            let s = CString::new("-7/2").expect("negative rational literal has no NUL byte");
            Z3_mk_numeral(c, s.as_ptr(), Z3_mk_real_sort(c))
        };
        assert_eq!(num_str(c, Z3_get_numerator(c, neg)), "-7");
        assert_eq!(num_str(c, Z3_get_denominator(c, neg)), "2");

        let i5 = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
        assert_eq!(num_str(c, Z3_get_numerator(c, i5)), "5");
        assert_eq!(num_str(c, Z3_get_denominator(c, i5)), "1");

        // Non-numeral: null, never a fabricated value.
        let sym = Z3_mk_string_symbol(c, c"x".as_ptr());
        let x = Z3_mk_const(c, sym, Z3_mk_real_sort(c));
        assert_eq!(Z3_get_numerator(c, x), 0);
        Z3_del_context(c);
    }
}

#[test]
fn numeral_double_matches_exact_rational() {
    // SAFETY: all handles live within one context.
    unsafe {
        let c = ctx();
        let r = Z3_mk_real(c, 3, 4);
        assert_eq!(Z3_get_numeral_double(c, r), 0.75);
        let i5 = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
        assert_eq!(Z3_get_numeral_double(c, i5), 5.0);
        let third = Z3_mk_real(c, 1, 3);
        assert_eq!(Z3_get_numeral_double(c, third), 1.0 / 3.0);
        // BV numeral: libz3 raises Z3_INVALID_ARG and returns 0.0.
        let s = CString::new("10").expect("bit-vector numeral literal has no NUL byte");
        let bv = Z3_mk_numeral(c, s.as_ptr(), Z3_mk_bv_sort(c, 8));
        assert_eq!(Z3_get_numeral_double(c, bv), 0.0);
        Z3_del_context(c);
    }
}

#[test]
fn numeral_rational_int64_and_small() {
    // SAFETY: all handles live within one context.
    unsafe {
        let c = ctx();
        let (mut n, mut d) = (0i64, 0i64);
        let r = Z3_mk_real(c, 3, 4);
        assert!(Z3_get_numeral_rational_int64(c, r, &raw mut n, &raw mut d));
        assert_eq!((n, d), (3, 4));
        let i5 = Z3_mk_int64(c, -5, Z3_mk_int_sort(c));
        assert!(Z3_get_numeral_small(c, i5, &raw mut n, &raw mut d));
        assert_eq!((n, d), (-5, 1));
        // BV numerals report (value, 1), as libz3 does.
        let s = CString::new("10").expect("bit-vector numeral literal has no NUL byte");
        let bv = Z3_mk_numeral(c, s.as_ptr(), Z3_mk_bv_sort(c, 8));
        assert!(Z3_get_numeral_rational_int64(c, bv, &raw mut n, &raw mut d));
        assert_eq!((n, d), (10, 1));
        // Non-numeral: false.
        let sym = Z3_mk_string_symbol(c, c"y".as_ptr());
        let y = Z3_mk_const(c, sym, Z3_mk_int_sort(c));
        assert!(!Z3_get_numeral_rational_int64(c, y, &raw mut n, &raw mut d));
        Z3_del_context(c);
    }
}

#[test]
fn numeral_binary_string() {
    // SAFETY: all handles live within one context.
    unsafe {
        let c = ctx();
        let s = CString::new("10").expect("bit-vector numeral literal has no NUL byte");
        let bv = Z3_mk_numeral(c, s.as_ptr(), Z3_mk_bv_sort(c, 8));
        let p = Z3_get_numeral_binary_string(c, bv);
        assert_eq!(
            CStr::from_ptr(p)
                .to_str()
                .expect("bit-vector binary rendering must be valid UTF-8"),
            "1010"
        );
        let z = CString::new("0").expect("zero bit-vector literal has no NUL byte");
        let bv0 = Z3_mk_numeral(c, z.as_ptr(), Z3_mk_bv_sort(c, 4));
        let p0 = Z3_get_numeral_binary_string(c, bv0);
        assert_eq!(
            CStr::from_ptr(p0)
                .to_str()
                .expect("zero bit-vector rendering must be valid UTF-8"),
            "0"
        );
        // Non-negative Int numerals are also in libz3's domain: 5 -> "101".
        let i5 = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
        let p5 = Z3_get_numeral_binary_string(c, i5);
        assert_eq!(
            CStr::from_ptr(p5)
                .to_str()
                .expect("integer binary rendering must be valid UTF-8"),
            "101"
        );
        // Negative Int: null.
        let m = Z3_mk_int(c, -5, Z3_mk_int_sort(c));
        assert!(Z3_get_numeral_binary_string(c, m).is_null());
        Z3_del_context(c);
    }
}

#[test]
fn string_contents_and_lstring() {
    // SAFETY: all handles live within one context; the contents buffer is
    // sized to the reported length.
    unsafe {
        let c = ctx();
        let lit = CString::new("hive").expect("string literal has no NUL byte");
        let s = Z3_mk_string(c, lit.as_ptr());
        let len = Z3_get_string_length(c, s);
        assert_eq!(len, 4);
        let mut buf = vec![0; len as usize];
        Z3_get_string_contents(c, s, len, buf.as_mut_ptr());
        assert_eq!(buf, vec![104, 105, 118, 101]); // h i v e
        let mut blen: c_uint = 999;
        let p = Z3_get_lstring(c, s, &raw mut blen);
        assert_eq!(blen, 4);
        assert_eq!(
            CStr::from_ptr(p)
                .to_str()
                .expect("string literal readback must be valid UTF-8"),
            "hive"
        );
        // Non-literal: libz3 returns a non-null EMPTY string, sets INVALID_ARG
        // and leaves *length untouched (measured). The error code is the signal,
        // not the pointer — returning null instead would segfault a consumer
        // doing strlen() on the result, which is valid against libz3.
        let sym = Z3_mk_string_symbol(c, c"sv".as_ptr());
        let v = Z3_mk_const(c, sym, Z3_mk_string_sort(c));
        let mut vlen: c_uint = 999;
        let q = Z3_get_lstring(c, v, &raw mut vlen);
        assert!(!q.is_null());
        assert_eq!(
            CStr::from_ptr(q)
                .to_str()
                .expect("non-literal string sentinel must be valid UTF-8"),
            ""
        );
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(vlen, 999);
        Z3_del_context(c);
    }
}

#[test]
fn array_sort_n_arity_and_domains() {
    // SAFETY: all handles live within one context.
    unsafe {
        let c = ctx();
        let int_s = Z3_mk_int_sort(c);
        let bool_s = Z3_mk_bool_sort(c);
        let real_s = Z3_mk_real_sort(c);
        let doms = [int_s, bool_s];
        let arr2 = Z3_mk_array_sort_n(c, 2, doms.as_ptr(), real_s);
        assert!(!arr2.is_null());
        assert_eq!(Z3_get_array_arity(c, arr2), 2);
        assert_eq!(
            Z3_get_sort_kind(c, Z3_get_array_sort_domain_n(c, arr2, 0)),
            Z3_INT_SORT
        );
        assert_eq!(
            Z3_get_sort_kind(c, Z3_get_array_sort_domain_n(c, arr2, 1)),
            Z3_BOOL_SORT
        );
        assert!(Z3_get_array_sort_domain_n(c, arr2, 2).is_null());
        // 1-D array: arity 1, domain_n(0) == domain.
        let arr1 = Z3_mk_array_sort(c, bool_s, int_s);
        assert_eq!(Z3_get_array_arity(c, arr1), 1);
        assert_eq!(
            Z3_get_sort_kind(c, Z3_get_array_sort_domain_n(c, arr1, 0)),
            Z3_BOOL_SORT
        );
        // Non-array: 0 / null.
        assert_eq!(Z3_get_array_arity(c, int_s), 0);
        assert!(Z3_get_array_sort_domain_n(c, int_s, 0).is_null());
        Z3_del_context(c);
    }
}

#[test]
fn seq_and_re_sort_basis() {
    // SAFETY: all handles live within one context.
    unsafe {
        let c = ctx();
        let int_s = Z3_mk_int_sort(c);
        let seq_int = Z3_mk_seq_sort(c, int_s);
        let basis = Z3_get_seq_sort_basis(c, seq_int);
        assert_eq!(Z3_get_sort_kind(c, basis), Z3_INT_SORT);
        // String sort: a string is a sequence of characters, so the basis is the
        // Char sort — the same answer libz3 gives.
        let str_basis = Z3_get_seq_sort_basis(c, Z3_mk_string_sort(c));
        assert!(!str_basis.is_null());
        assert_eq!(Z3_get_sort_kind(c, str_basis), Z3_CHAR_SORT);
        // Regex basis is the String sort (AY regexes are string regexes).
        let re = Z3_mk_re_sort(c, Z3_mk_string_sort(c));
        let re_basis = Z3_get_re_sort_basis(c, re);
        assert_eq!(Z3_get_sort_kind(c, re_basis), Z3_SEQ_SORT);
        // Non-seq / non-re: null.
        assert!(Z3_get_seq_sort_basis(c, int_s).is_null());
        assert!(Z3_get_re_sort_basis(c, int_s).is_null());
        Z3_del_context(c);
    }
}

#[test]
fn finite_domain_sort_size_zero_and_false_for_non_fd_sorts() {
    // SAFETY: all handles live within one context.
    unsafe {
        let c = ctx();
        let mut sz: u64 = 123;
        assert!(!Z3_get_finite_domain_sort_size(
            c,
            Z3_mk_int_sort(c),
            &raw mut sz
        ));
        assert_eq!(sz, 0);
        assert!(!Z3_get_finite_domain_sort_size(
            c,
            ptr::null_mut(),
            &raw mut sz
        ));
        Z3_del_context(c);
    }
}

#[test]
fn tuple_sort_introspection_via_single_ctor_datatype() {
    // SAFETY: constructor descriptors are freed via Z3_del_constructor; all
    // other handles are context-owned.
    unsafe {
        let c = ctx();
        let int_s = Z3_mk_int_sort(c);
        let real_s = Z3_mk_real_sort(c);
        let fnames = [
            Z3_mk_string_symbol(c, c"fst".as_ptr()),
            Z3_mk_string_symbol(c, c"snd".as_ptr()),
        ];
        let fsorts = [int_s, real_s];
        let refs: [c_uint; 2] = [0, 0];
        let ctor = Z3_mk_constructor(
            c,
            Z3_mk_string_symbol(c, c"mk-pair".as_ptr()),
            Z3_mk_string_symbol(c, c"is-pair".as_ptr()),
            2,
            fnames.as_ptr(),
            fsorts.as_ptr(),
            refs.as_ptr(),
        );
        let mut ctors = [ctor];
        let pair = Z3_mk_datatype(
            c,
            Z3_mk_string_symbol(c, c"Pair".as_ptr()),
            1,
            ctors.as_mut_ptr(),
        );
        assert!(!pair.is_null());
        assert_eq!(Z3_get_tuple_sort_num_fields(c, pair), 2);

        let f0 = Z3_get_tuple_sort_field_decl(c, pair, 0);
        let f0_name = Z3_get_symbol_string(c, Z3_get_decl_name(c, f0));
        assert_eq!(
            CStr::from_ptr(f0_name)
                .to_str()
                .expect("first tuple field name must be valid UTF-8"),
            "fst"
        );
        assert_eq!(Z3_get_sort_kind(c, Z3_get_range(c, f0)), Z3_INT_SORT);

        let f1 = Z3_get_tuple_sort_field_decl(c, pair, 1);
        let f1_name = Z3_get_symbol_string(c, Z3_get_decl_name(c, f1));
        assert_eq!(
            CStr::from_ptr(f1_name)
                .to_str()
                .expect("second tuple field name must be valid UTF-8"),
            "snd"
        );
        assert!(Z3_get_tuple_sort_field_decl(c, pair, 2).is_null());

        let mk = Z3_get_tuple_sort_mk_decl(c, pair);
        let mk_name = Z3_get_symbol_string(c, Z3_get_decl_name(c, mk));
        assert_eq!(
            CStr::from_ptr(mk_name)
                .to_str()
                .expect("tuple constructor name must be valid UTF-8"),
            "mk-pair"
        );
        assert_eq!(Z3_get_arity(c, mk), 2);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_range(c, mk)), Z3_DATATYPE_SORT);

        // The mk decl is REAL: applying it builds a term of the datatype sort.
        let args = [
            Z3_mk_int(c, 1, int_s),
            Z3_mk_numeral(c, c"1/2".as_ptr(), real_s),
        ];
        let t = Z3_mk_app(c, mk, 2, args.as_ptr());
        assert_ne!(t, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, t)), Z3_DATATYPE_SORT);

        // Non-tuple sorts report 0 / null.
        assert_eq!(Z3_get_tuple_sort_num_fields(c, int_s), 0);
        assert!(Z3_get_tuple_sort_mk_decl(c, int_s).is_null());

        Z3_del_constructor(c, ctor);
        Z3_del_context(c);
    }
}
