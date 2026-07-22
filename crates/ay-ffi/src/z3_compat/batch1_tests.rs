// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Track B batch 1: `algebraic.rs`, `misc_ext.rs`, `rcf.rs`.
//!
//! Focuses on the SEMANTIC (real) functions — exact rational arithmetic, term
//! translation, SMT-LIB evaluation — and confirms the honest-divergence
//! functions return their sound sentinel + documented error code.

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

// ---- algebraic (exact over the rational subset) ----

#[test]
fn algebraic_is_value_and_sign() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let five = Z3_mk_int(c, 5, int);
        let neg = Z3_mk_int(c, -3, int);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        assert!(Z3_algebraic_is_value(c, five));
        assert!(!Z3_algebraic_is_value(c, x));
        assert_eq!(Z3_algebraic_sign(c, five), 1);
        assert_eq!(Z3_algebraic_sign(c, neg), -1);
        assert!(Z3_algebraic_is_pos(c, five));
        assert!(Z3_algebraic_is_neg(c, neg));
        Z3_del_context(c);
    }
}

#[test]
fn algebraic_exact_arithmetic() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let three_q = Z3_mk_numeral(c, c"3/4".as_ptr(), real);
        let one_q = Z3_mk_numeral(c, c"1/4".as_ptr(), real);
        // Compare exact VALUES (AY renders integer-valued reals as "n/1", a
        // global rendering convention — the value, not its spelling, is the test).
        let val = |a: Z3_ast| Z3_get_numeral_double(c, a);
        assert!((val(Z3_algebraic_add(c, three_q, one_q)) - 1.0).abs() < 1e-12);
        assert!((val(Z3_algebraic_sub(c, three_q, one_q)) - 0.5).abs() < 1e-12);
        assert!((val(Z3_algebraic_mul(c, three_q, one_q)) - 0.1875).abs() < 1e-12);
        assert!((val(Z3_algebraic_div(c, three_q, one_q)) - 3.0).abs() < 1e-12);
        // The results are genuine numerals (values, never fabricated handles).
        assert!(Z3_algebraic_is_value(
            c,
            Z3_algebraic_add(c, three_q, one_q)
        ));
        Z3_del_context(c);
    }
}

#[test]
fn algebraic_comparisons() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let half = Z3_mk_numeral(c, c"1/2".as_ptr(), real);
        let tq = Z3_mk_numeral(c, c"3/4".as_ptr(), real);
        assert!(Z3_algebraic_lt(c, half, tq));
        assert!(Z3_algebraic_gt(c, tq, half));
        assert!(Z3_algebraic_le(c, half, half));
        assert!(Z3_algebraic_ge(c, half, half));
        assert!(Z3_algebraic_eq(c, half, half));
        assert!(Z3_algebraic_neq(c, half, tq));
        Z3_del_context(c);
    }
}

#[test]
fn algebraic_root_is_sqrt2() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let two = Z3_mk_numeral(c, c"2".as_ptr(), real);
        // sqrt(2): now REAL over ay-nra — the exact 2nd root of x^2 - 2.
        let r = Z3_algebraic_root(c, two, 2);
        assert_ne!(r, 0);
        assert!(Z3_algebraic_is_value(c, r));
        assert!(Z3_algebraic_is_pos(c, r));
        // r*r == 2 exactly (GCD-certified).
        assert!(Z3_algebraic_eq(c, Z3_algebraic_mul(c, r, r), two));
        // A perfect square collapses to a rational: sqrt(4) == 2.
        let four = Z3_mk_numeral(c, c"4".as_ptr(), real);
        let two_again = Z3_algebraic_root(c, four, 2);
        assert!(Z3_algebraic_eq(c, two_again, two));
        Z3_del_context(c);
    }
}

// ---- misc_ext ----

#[test]
fn app_to_ast_identity() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        assert_eq!(Z3_app_to_ast(c, x), x);
        Z3_del_context(c);
    }
}

#[test]
fn translate_across_contexts() {
    unsafe {
        let src = ctx();
        let dst = ctx();
        let int = Z3_mk_int_sort(src);
        let x = Z3_mk_const(src, Z3_mk_string_symbol(src, c"x".as_ptr()), int);
        let args = [x, x];
        let sum = Z3_mk_add(src, 2, args.as_ptr());
        let translated = Z3_translate(src, sum, dst);
        assert_ne!(translated, 0);
        // Rendered form should match across contexts.
        let s_src = CStr::from_ptr(Z3_ast_to_string(src, sum))
            .to_str()
            .expect("source AST rendering must be valid UTF-8")
            .to_string();
        let s_dst = CStr::from_ptr(Z3_ast_to_string(dst, translated))
            .to_str()
            .expect("translated AST rendering must be valid UTF-8")
            .to_string();
        assert_eq!(s_src, s_dst);

        // Translation also installs the exact public declaration identity in
        // the target. Recreating x must reuse the translated leaf, while the
        // next fresh constant remains distinct.
        let translated_x = Z3_get_app_arg(dst, translated, 0);
        let dst_int = Z3_mk_int_sort(dst);
        let remade_x = Z3_mk_const(dst, Z3_mk_string_symbol(dst, c"x".as_ptr()), dst_int);
        assert_eq!(remade_x, translated_x);
        let y = Z3_mk_const(dst, Z3_mk_string_symbol(dst, c"y".as_ptr()), dst_int);
        assert_ne!(y, 0);
        assert_ne!(y, translated_x);
        Z3_del_context(src);
        Z3_del_context(dst);
    }
}

#[test]
fn translate_rejects_target_private_identity_collision() {
    unsafe {
        let src = ctx();
        let dst = ctx();

        // Both contexts allocate private constant identity zero independently,
        // but attach different public symbols. The semantic DAG copier would
        // otherwise intern these as the same target node.
        let dst_int = Z3_mk_int_sort(dst);
        let dst_x = Z3_mk_const(dst, Z3_mk_string_symbol(dst, c"x".as_ptr()), dst_int);
        let src_int = Z3_mk_int_sort(src);
        let src_y = Z3_mk_const(src, Z3_mk_string_symbol(src, c"y".as_ptr()), src_int);

        assert_eq!(Z3_translate(src, src_y, dst), 0);
        assert_eq!(Z3_get_error_code(dst), Z3_INVALID_USAGE);
        let error = CStr::from_ptr(Z3_get_error_msg(dst, Z3_INVALID_USAGE))
            .to_str()
            .expect("Z3 error message must be valid UTF-8");
        assert!(error.contains("cross-context translation metadata conflict"));

        // Collision preflight is atomic with respect to public metadata.
        assert_eq!(
            CStr::from_ptr(Z3_ast_to_string(dst, dst_x))
                .to_str()
                .expect("target AST rendering must be valid UTF-8"),
            "x"
        );

        Z3_del_context(src);
        Z3_del_context(dst);
    }
}

#[test]
fn eval_smtlib2_runs_a_script() {
    unsafe {
        let c = ctx();
        let script = c"(declare-const x Int)(assert (> x 5))(check-sat)";
        let out = Z3_eval_smtlib2_string(c, script.as_ptr());
        assert!(!out.is_null());
        let text = CStr::from_ptr(out)
            .to_str()
            .expect("SMT-LIB evaluation output must be valid UTF-8");
        assert!(text.contains("sat"), "expected sat in output, got: {text}");
        Z3_del_context(c);
    }
}

#[test]
fn parse_smtlib2_string_returns_assertion_vector() {
    unsafe {
        let c = ctx();
        // Two declared assertions + an ignored query command. Exercise the
        // C ABI z3py drives: parse -> ast_vector_size -> ast_vector_get ->
        // ast_to_string per element.
        let script = c"(declare-const x Int)(assert (> x 5))(assert (< x 10))(check-sat)";
        let vec = Z3_parse_smtlib2_string(
            c,
            script.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert!(!vec.is_null(), "parse returned a null vector");
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "well-formed parse must be Z3_OK"
        );
        let n = Z3_ast_vector_size(c, vec);
        assert_eq!(n, 2, "expected exactly the two top-level assertions");

        let mut rendered = String::new();
        for i in 0..n {
            let a = Z3_ast_vector_get(c, vec, i);
            assert_ne!(a, 0, "assertion {i} decoded to a null AST");
            let s = Z3_ast_to_string(c, a);
            assert!(!s.is_null(), "ast_to_string returned null for element {i}");
            let text = CStr::from_ptr(s)
                .to_str()
                .expect("parsed assertion rendering must be valid UTF-8");
            assert!(!text.is_empty(), "element {i} rendered empty");
            rendered.push_str(text);
            rendered.push('\n');
        }
        // The parsed ASTs must carry the same variable and literal bounds the
        // text stated; a dropped/mis-parsed assertion would lose one of these.
        assert!(rendered.contains('x'), "missing var x: {rendered}");
        assert!(rendered.contains('5'), "missing bound 5: {rendered}");
        assert!(rendered.contains("10"), "missing bound 10: {rendered}");

        // Syntax error: an unbalanced form must NOT crash — it must set the
        // error code and return an empty (size-0) vector, matching stock z3's
        // fail-closed behavior.
        let bad = c"(declare-const x Int (assert (> x 5))";
        let bad_vec = Z3_parse_smtlib2_string(
            c,
            bad.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert!(
            !bad_vec.is_null(),
            "even on error the vector handle is non-null"
        );
        // Read the error code FIRST: like stock z3, subsequent successful calls
        // (e.g. Z3_ast_vector_size) reset the context error state on entry.
        assert_ne!(
            Z3_get_error_code(c),
            Z3_OK,
            "syntax error must set the context error code"
        );
        assert_eq!(
            Z3_ast_vector_size(c, bad_vec),
            0,
            "syntax error yields no assertions"
        );

        Z3_del_context(c);
    }
}

#[test]
fn params_to_string_renders() {
    unsafe {
        let c = ctx();
        let p = Z3_mk_params(c);
        Z3_params_set_bool(c, p, Z3_mk_string_symbol(c, c"foo".as_ptr()), true);
        let s = Z3_params_to_string(c, p);
        assert!(!s.is_null());
        let text = CStr::from_ptr(s)
            .to_str()
            .expect("parameter rendering must be valid UTF-8");
        assert!(text.contains("foo"), "got: {text}");
        Z3_del_context(c);
    }
}

#[test]
fn misc_divergences() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // sort_to_ast: REAL now — a value-canonical TAGGED handle (never 0,
        // never a term id). See capi_handle_tests.rs for the full suite.
        let sort_ast = Z3_sort_to_ast(c, int);
        assert_ne!(sort_ast, 0, "sort_to_ast must return a real handle");
        assert_eq!(
            sort_ast & HANDLE_TAG_MASK,
            SORT_AST_TAG,
            "sort ast must carry the sort tag"
        );
        // model_extrapolate: REAL now (see bounded_gap_tests); a null model
        // is still an honest 0 + INVALID_ARG.
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        assert_eq!(Z3_model_extrapolate(c, ptr::null_mut(), x), 0);
        Z3_del_context(c);
    }
}

// ---- rcf (REAL: exact engine + symbolic transcendental extension) ----

#[test]
fn rcf_pi_real_and_null_handles_sound() {
    unsafe {
        let c = ctx();
        // π is now a REAL symbolic transcendental element (exact linear form;
        // see rcf_ext_tests.rs for the full behavioral suite).
        let pi = Z3_rcf_mk_pi(c);
        assert!(!pi.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_rcf_is_transcendental(c, pi));
        assert!(!Z3_rcf_is_rational(c, pi));
        // predicates on a (null) rcf number: sound false, never a fabricated verdict.
        assert!(!Z3_rcf_is_rational(c, ptr::null_mut()));
        Z3_del_context(c);
    }
}
