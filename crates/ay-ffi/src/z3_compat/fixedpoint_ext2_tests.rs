// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Track B batch 3b: fixedpoint (CHC) + model-construction C-API.

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
fn model_const_interp_roundtrip() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // A user-built model with an explicit interpretation for a 0-ary decl.
        let m = Z3_mk_model(c);
        assert!(!m.is_null());
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"k".as_ptr()),
            0,
            ptr::null(),
            int,
        );
        let seven = Z3_mk_int(c, 7, int);
        Z3_add_const_interp(c, m, f, seven);
        // Read it back.
        let got = Z3_model_get_const_interp(c, m, f);
        assert_eq!(
            got, seven,
            "const interp must read back the value it was given"
        );
        Z3_del_context(c);
    }
}

#[test]
fn fixedpoint_assert_and_get_assertions() {
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        let t = Z3_mk_true(c);
        Z3_fixedpoint_assert(c, fp, t);
        let asserts = Z3_fixedpoint_get_assertions(c, fp);
        assert!(!asserts.is_null());
        assert!(
            Z3_ast_vector_size(c, asserts) >= 1,
            "asserted axiom must be retained"
        );
        Z3_del_context(c);
    }
}

#[test]
fn fixedpoint_reason_unknown_is_sound() {
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        // Before any query, reason-unknown is a (possibly empty) non-null string,
        // never a fabricated verdict.
        let r = Z3_fixedpoint_get_reason_unknown(c, fp);
        assert!(!r.is_null());
        Z3_del_context(c);
    }
}
