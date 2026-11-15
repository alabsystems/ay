// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression battery for the round-3 verification of the Z3 C API (z3py 5.1.0
//! against AY's dylib), first part: every SMT-LIB text a parse entry point
//! accepts binds its names to the context's declarations (set-logic,
//! set-option, define-fun, define-sort, declare-sort, define-fun-rec,
//! datatypes, quoted names, caller-named sorts and declarations), and a
//! rejected text leaves the context usable. `solver_model_r4b_tests` holds
//! the rest.

use std::ffi::{CStr, CString};

use super::solver_model_scope_tests::{evaluates_true, mk_ctx, named_const};
use super::*;

unsafe fn from_string(c: Z3_context, s: Z3_solver, text: &str) {
    let text = CString::new(text).expect("test text has no NUL");
    // SAFETY: live context and solver; `text` outlives the call.
    unsafe { Z3_solver_from_string(c, s, text.as_ptr()) }
}

unsafe fn error_message(c: Z3_context) -> String {
    // SAFETY: live context.
    unsafe {
        CStr::from_ptr(Z3_get_error_msg(c, Z3_get_error_code(c)))
            .to_string_lossy()
            .into_owned()
    }
}

/// The verify-3 R1/R2 texts: each prefix keeps the text outside round 3's
/// rebinding fragment, where the parsed `a` was a second engine symbol (z3:
/// unsat on every line; AY answered sat with `[a = 0, a = 3]`).
#[test]
fn every_text_preamble_binds_the_contexts_constant() {
    let preambles = [
        "(set-logic QF_LIA)",
        "(set-option :produce-models true)",
        "(set-info :status unsat)",
        "(define-sort II () Int)",
        "(declare-sort U 0)",
        "(define-fun k () Int 7)",
        "(define-fun two () Int 2)(declare-fun b () Int)(assert (= b two))",
        "(define-fun-rec ff ((z Int)) Int (ite (<= z 0) 0 (ff (- z 1))))",
        "(define-funs-rec ((ev ((n Int)) Bool) (od ((n Int)) Bool)) \
         ((ite (= n 0) true (od (- n 1))) (ite (= n 0) false (ev (- n 1)))))",
    ];
    for preamble in preambles {
        // SAFETY: every handle below belongs to the live context `c`.
        unsafe {
            let c = mk_ctx();
            let int = Z3_mk_int_sort(c);
            let a = named_const(c, "a", int);
            let s = Z3_mk_solver(c);
            Z3_solver_assert(c, s, Z3_mk_eq(c, a, Z3_mk_int(c, 0, int)));
            from_string(
                c,
                s,
                &format!("{preamble}(declare-fun a () Int)(assert (> a 2))"),
            );
            assert_eq!(
                Z3_get_error_code(c),
                Z3_OK,
                "{preamble}: {}",
                error_message(c)
            );
            assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE, "{preamble}");
            Z3_del_context(c);
        }
    }
}

/// verify-3 R3 and the round-3 verifier's `set-logic` Bool form: the
/// assumption `Not(p)` contradicts the parsed `p`, and the core says so.
#[test]
fn a_parsed_assertion_meets_the_callers_assumption() {
    for text in [
        "(declare-fun p () Bool)(define-fun t () Bool true)(assert (and p t))",
        "(set-logic QF_UF)(declare-fun p () Bool)(assert p)",
        "(declare-fun |p| () Bool)(assert |p|)",
    ] {
        // SAFETY: every handle below belongs to the live context `c`.
        unsafe {
            let c = mk_ctx();
            let p = named_const(c, "p", Z3_mk_bool_sort(c));
            let s = Z3_mk_solver(c);
            from_string(c, s, text);
            assert_eq!(Z3_get_error_code(c), Z3_OK, "{text}: {}", error_message(c));
            let not_p = Z3_mk_not(c, p);
            assert_eq!(
                Z3_solver_check_assumptions(c, s, 1, [not_p].as_ptr()),
                Z3_L_FALSE,
                "{text}"
            );
            let core = Z3_solver_get_unsat_core(c, s);
            assert_eq!(Z3_ast_vector_size(c, core), 1, "{text}");
            Z3_del_context(c);
        }
    }
}

/// A quoted name, a sort the text declares, and a function over it all bind.
#[test]
fn quoted_names_and_declared_sorts_bind() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let ab = named_const(c, "a b", int);
        let u_name = CString::new("U").expect("no NUL");
        let u = Z3_mk_uninterpreted_sort(c, Z3_mk_string_symbol(c, u_name.as_ptr()));
        let x = named_const(c, "x", u);
        let y = named_const(c, "y", u);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, ab, Z3_mk_int(c, 0, int)));
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, y));
        from_string(
            c,
            s,
            "(declare-fun |a b| () Int)(declare-sort U 0)(declare-fun x () U)\
             (declare-fun y () U)(assert (or (> |a b| 4) (distinct x y)))",
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        // A later text of the same solver still sees its sort.
        let s = Z3_mk_solver(c);
        from_string(c, s, "(declare-sort U 0)(declare-fun x () U)");
        from_string(c, s, "(declare-fun y () U)(assert (distinct x y))");
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, y));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

/// verify-3 R4: `Z3_parse_smtlib2_string` with a definition returns an
/// assertion over the context's `a`.
#[test]
fn parse_smtlib2_string_with_a_definition_binds() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let a = named_const(c, "a", int);
        let text = CString::new(
            "(set-logic QF_LIA)(declare-fun a () Int)(define-fun two () Int 2)(assert (> a two))",
        )
        .expect("no NUL");
        let v = Z3_parse_smtlib2_string(
            c,
            text.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        assert_eq!(Z3_ast_vector_size(c, v), 1);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v, 0));
        Z3_solver_assert(c, s, Z3_mk_eq(c, a, Z3_mk_int(c, 0, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

/// Two SMT-LIB files with `set-logic` in one context: z3 accepts both, and
/// the context stays usable (it was poisoned: "the logic has already been
/// set", then every new solver failed).
#[test]
fn two_set_logic_texts_leave_the_context_usable() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let s1 = Z3_mk_solver(c);
        from_string(
            c,
            s1,
            "(set-logic QF_LIA)(declare-fun a () Int)(assert (> a 4))",
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        let s2 = Z3_mk_solver(c);
        from_string(
            c,
            s2,
            "(set-logic QF_LIA)(declare-fun b () Int)(assert (< b 0))",
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        let s3 = Z3_mk_solver(c);
        assert!(!s3.is_null());
        assert_eq!(Z3_solver_check(c, s1), Z3_L_TRUE);
        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

/// A text that declares a datatype (it panicked: "symbol 'red' is already
/// bound to a different declaration"): the datatype is the context's, and
/// the text's `p` is the caller's.
#[test]
fn a_datatype_text_neither_panics_nor_duplicates_names() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let p = named_const(c, "p", Z3_mk_bool_sort(c));
        let s = Z3_mk_solver(c);
        from_string(
            c,
            s,
            "(declare-datatypes ((C 0)) (((red) (green))))(declare-fun c () C)\
             (declare-fun p () Bool)(assert (and p (= c red)))",
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        let not_p = Z3_mk_not(c, p);
        assert_eq!(
            Z3_solver_check_assumptions(c, s, 1, [not_p].as_ptr()),
            Z3_L_FALSE
        );
        let r = Z3_solver_check(c, s);
        assert_ne!(r, Z3_L_FALSE);
        if r == Z3_L_TRUE {
            let m = Z3_solver_get_model(c, s);
            assert!(!m.is_null());
            assert!(evaluates_true(c, m, p));
        }
        Z3_del_context(c);
    }
}

/// The list datatype `L = nil | cons(hd: Int, tl: L)`, built as z3py builds it.
unsafe fn list_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: live context.
    unsafe {
        let int = Z3_mk_int_sort(c);
        let fnames = [
            Z3_mk_string_symbol(c, c"hd".as_ptr()),
            Z3_mk_string_symbol(c, c"tl".as_ptr()),
        ];
        let fsorts = [int, ptr::null_mut()];
        let frefs = [0u32, 0u32];
        let cons = Z3_mk_constructor(
            c,
            Z3_mk_string_symbol(c, c"cons".as_ptr()),
            Z3_mk_string_symbol(c, c"is-cons".as_ptr()),
            2,
            fnames.as_ptr(),
            fsorts.as_ptr(),
            frefs.as_ptr(),
        );
        let nil = Z3_mk_constructor(
            c,
            Z3_mk_string_symbol(c, c"nil".as_ptr()),
            Z3_mk_string_symbol(c, c"is-nil".as_ptr()),
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        let mut ctors = [nil, cons];
        Z3_mk_datatype(
            c,
            Z3_mk_string_symbol(c, c"L".as_ptr()),
            2,
            ctors.as_mut_ptr(),
        )
    }
}

/// The round-3 verifiers' parse API gaps: a caller datatype named in
/// `sorts=` with a constant in `decls=` (it raised "undefined symbol: l1"),
/// a caller uninterpreted sort in `sorts=` ("unknown sort 'U'"), and a text
/// that re-declares the caller's datatype ("sort 'L' is already declared").
#[test]
fn parses_see_caller_sorts_and_datatypes() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let list = list_sort(c);
        assert!(!list.is_null());
        let l1 = named_const(c, "l1", list);
        let text = CString::new("(assert ((_ is cons) l1))").expect("no NUL");
        let sort_names = [Z3_mk_string_symbol(c, c"L".as_ptr())];
        let decl_names = [Z3_mk_string_symbol(c, c"l1".as_ptr())];
        let decls = [Z3_get_app_decl(c, Z3_to_app(c, l1))];
        let v = Z3_parse_smtlib2_string(
            c,
            text.as_ptr(),
            1,
            sort_names.as_ptr(),
            [list].as_ptr(),
            1,
            decl_names.as_ptr(),
            decls.as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        assert_eq!(Z3_ast_vector_size(c, v), 1);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v, 0));
        let nil_name = CString::new("(assert (= l1 nil))").expect("no NUL");
        let w = Z3_parse_smtlib2_string(
            c,
            nil_name.as_ptr(),
            1,
            sort_names.as_ptr(),
            [list].as_ptr(),
            1,
            decl_names.as_ptr(),
            decls.as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, w, 0));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);

        // A caller uninterpreted sort under its own name.
        let u_name = Z3_mk_string_symbol(c, c"U".as_ptr());
        let u = Z3_mk_uninterpreted_sort(c, u_name);
        let x = named_const(c, "x", u);
        let text = CString::new("(declare-fun y () U)(assert (distinct x y))").expect("no NUL");
        let x_names = [Z3_mk_string_symbol(c, c"x".as_ptr())];
        let x_decls = [Z3_get_app_decl(c, Z3_to_app(c, x))];
        let v = Z3_parse_smtlib2_string(
            c,
            text.as_ptr(),
            1,
            [u_name].as_ptr(),
            [u].as_ptr(),
            1,
            x_names.as_ptr(),
            x_decls.as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v, 0));
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, named_const(c, "y", u)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);

        // A text that declares the caller's datatype again.
        let s = Z3_mk_solver(c);
        from_string(
            c,
            s,
            "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\
             (declare-fun l1 () L)(assert ((_ is cons) l1))",
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        let is_nil = CString::new("(assert (= l1 nil))").expect("no NUL");
        Z3_solver_assert(
            c,
            s,
            Z3_ast_vector_get(
                c,
                Z3_parse_smtlib2_string(
                    c,
                    is_nil.as_ptr(),
                    1,
                    sort_names.as_ptr(),
                    [list].as_ptr(),
                    1,
                    decl_names.as_ptr(),
                    decls.as_ptr(),
                ),
                0,
            ),
        );
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        Z3_del_context(c);
    }
}
