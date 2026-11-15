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

/// Parse `script` through `Z3_fixedpoint_from_string`, run its first
/// query, and return `Z3_fixedpoint_query`'s verdict.
///
/// # Safety
/// Test-local helper; owns its context for the call's duration.
unsafe fn query_via_script(script: &std::ffi::CStr) -> i32 {
    // SAFETY: all handles created and consumed inside this call.
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        let q = Z3_fixedpoint_from_string(c, fp, script.as_ptr());
        assert!(
            !q.is_null(),
            "script must parse: err {}",
            Z3_get_error_code(c)
        );
        assert_eq!(Z3_ast_vector_size(c, q), 1);
        let verdict = Z3_fixedpoint_query(c, fp, Z3_ast_vector_get(c, q, 0));
        Z3_del_context(c);
        verdict
    }
}

/// The SMT-LIB2 fixedpoint script dialect end-to-end: reachable and
/// unreachable queries match the z3 CLI's sat/unsat polarity for the
/// same scripts (libz3's own `from_string` segfaults on these inputs,
/// so the CLI is the oracle).
#[test]
fn fixedpoint_from_string_parses_and_queries() {
    // SAFETY: test-scope helper; see above.
    unsafe {
        // R = {0,1,2,3}: (query R) is reachable.
        assert_eq!(
            query_via_script(c"(declare-rel R (Int))(declare-var x Int)(rule (R 0))(rule (=> (and (R x) (< x 3)) (R (+ x 1))))(query R)"),
            Z3_L_TRUE
        );
        // No initiation fact: R is empty, query unreachable.
        assert_eq!(
            query_via_script(c"(declare-rel R (Int))(declare-var x Int)(rule (=> (and (R x) (< x 3)) (R (+ x 1))))(query R)"),
            Z3_L_FALSE
        );
        // Ground query beyond the reachable set (max 3).
        assert_eq!(
            query_via_script(c"(declare-rel R (Int))(declare-var x Int)(rule (R 0))(rule (=> (and (R x) (< x 3)) (R (+ x 1))))(query (R 4))"),
            Z3_L_FALSE
        );
    }
}

/// A malformed or unelaboratable script fails with `Z3_PARSER_ERROR`
/// and a null vector, adding nothing (a later good script still works
/// on the same handle).
#[test]
fn fixedpoint_from_string_rejects_bad_scripts() {
    // SAFETY: test-scope unsafe block; handles owned here.
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        assert!(Z3_fixedpoint_from_string(c, fp, c"hello world".as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        assert!(Z3_fixedpoint_from_string(c, fp, c"(rule (S 0))".as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        let q = Z3_fixedpoint_from_string(
            c,
            fp,
            c"(declare-rel R (Int))(rule (R 0))(query R)".as_ptr(),
        );
        assert!(!q.is_null());
        assert_eq!(
            Z3_fixedpoint_query(c, fp, Z3_ast_vector_get(c, q, 0)),
            Z3_L_TRUE
        );
        Z3_del_context(c);
    }
}

/// `Z3_fixedpoint_from_file` reads and parses a script file; a missing
/// file is `Z3_PARSER_ERROR` + null (z3's shapes).
#[test]
fn fixedpoint_from_file_parses() {
    // SAFETY: test-scope unsafe block; handles owned here.
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        assert!(Z3_fixedpoint_from_file(c, fp, c"/nonexistent/ay-fp-test.smt2".as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        let path = std::env::temp_dir().join("ay_fp_from_file_test.smt2");
        std::fs::write(&path, "(declare-rel R (Int))(rule (R 0))(query R)").expect("write script");
        let cpath = std::ffi::CString::new(path.to_string_lossy().into_owned()).expect("path");
        let q = Z3_fixedpoint_from_file(c, fp, cpath.as_ptr());
        assert!(!q.is_null(), "err {}", Z3_get_error_code(c));
        assert_eq!(
            Z3_fixedpoint_query(c, fp, Z3_ast_vector_get(c, q, 0)),
            Z3_L_TRUE
        );
        let _ = std::fs::remove_file(&path);
        Z3_del_context(c);
    }
}
