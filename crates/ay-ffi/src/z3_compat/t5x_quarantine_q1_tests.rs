// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the T5 design's P0.2 quarantine, implementer X
//! (`~/ay-bench/campaign/2026-10-02-T5-DESIGN.md` §4 P0.2), item Q1: de
//! Bruijn binders (`Z3_mk_forall`, `Z3_mk_exists`, `Z3_mk_quantifier*`,
//! `Z3_mk_lambda`, `Z3_mk_bound`).
//!
//! Each test pins libz3 5.1.0's measured answer or a fail-closed error. The
//! measurements are the z3py probes `q1_pins.py`, `q3_pins.py`, `q4_pins.py`
//! and `extra_pins.py` (`~/ay-bench/campaign/t5design-probes/t5x/`, with their
//! `*.real.out` from z3-solver 5.1.0.0 via that directory's `run.py`), and the
//! design's own probes (`p1_db.py`, `p3_leak.py`, `p8_lsubst.py`,
//! `p9_update.py`, `judge_sound/j6.py`, `judge_fid/f1.py`).

use std::ffi::CStr;
use std::ptr;

use super::t5x_quarantine_support::*;

// ---------------------------------------------------------------------------
// Q1: de Bruijn binders
// ---------------------------------------------------------------------------

/// p1(a) (`p1_db.py`): `forall x:Int. (:var 0) > 0` built with `Z3_mk_forall`
/// binds its variable. z3: unsat, its negation sat, bound name `x`, and the
/// same construction twice is one AST. AY answered sat: `(:var 0)` stayed a
/// free variable of the quantifier.
#[test]
fn q1_de_bruijn_forall_binds_its_variable() {
    // SAFETY: every handle lives in `c`; arrays outlive each call.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let v0 = Z3_mk_bound(c, 0, int_sort);
        let body = Z3_mk_gt(c, v0, int(c, 0));
        let x = sym(c, c"x");
        let q = Z3_mk_forall(
            c,
            0,
            0,
            ptr::null(),
            1,
            &raw const int_sort,
            &raw const x,
            body,
        );
        assert_ne!(q, 0, "{}", error_text(c));
        assert_eq!(check(c, &[q]), Z3_L_FALSE, "z3: unsat");
        assert_eq!(check(c, &[not(c, q)]), Z3_L_TRUE, "z3: sat");
        let name = Z3_get_quantifier_bound_name(c, q, 0);
        assert_eq!(
            CStr::from_ptr(Z3_get_symbol_string(c, name)).to_str(),
            Ok("x")
        );
        let shown = text(c, q);
        assert!(
            !shown.contains(":var") && shown.contains("x Int"),
            "{shown}"
        );
        let again = Z3_mk_forall(
            c,
            0,
            0,
            ptr::null(),
            1,
            &raw const int_sort,
            &raw const x,
            body,
        );
        assert!(
            Z3_is_eq_ast(c, q, again),
            "z3: the rebuilt quantifier is eq"
        );
        Z3_del_context(c);
    }
}

/// The variables.rs:50 panic: a binder name declared at one sort and reused
/// at another (`w:Int`, then `w:Bool`). z3 builds both and answers sat
/// (`q1_pins.py` 2). AY's `declare_const` panicked ("panic in FFI").
#[test]
fn q1_binder_name_at_a_second_sort_does_not_panic() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, bool_sort) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let vi = Z3_mk_bound(c, 0, int_sort);
        let q_int = db_quantifier(c, true, &[int_sort], &[c"w"], &[], Z3_mk_ge(c, vi, vi));
        assert_ne!(q_int, 0, "{}", error_text(c));
        let vb = Z3_mk_bound(c, 0, bool_sort);
        let excluded_middle = Z3_mk_or(c, 2, [vb, not(c, vb)].as_ptr());
        let q_bool = db_quantifier(c, true, &[bool_sort], &[c"w"], &[], excluded_middle);
        assert_ne!(q_bool, 0, "{}", error_text(c));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(check(c, &[q_int, q_bool]), Z3_L_TRUE, "z3: sat");
        let shown = text(c, q_bool);
        assert!(
            shown.contains("(w Bool)") && !shown.contains("!ay."),
            "{shown}"
        );
        Z3_del_context(c);
    }
}

/// A binder never takes the name of a constant the body uses: `forall xp'.
/// xp' >= xp` over a parsed constant `xp` is unsat in z3 (`q1_pins.py` 3);
/// AY bound the parsed constant itself and answered sat.
#[test]
fn q1_binder_never_captures_a_parsed_constant() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let parsed = Z3_parse_smtlib2_string(
            c,
            c"(declare-const xp Int) (assert (> xp 0))".as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert!(!parsed.is_null(), "{}", error_text(c));
        let assertion = Z3_ast_vector_get(c, parsed, 0);
        let mut xp = 0;
        for i in 0..Z3_get_app_num_args(c, Z3_to_app(c, assertion)) {
            let arg = Z3_get_app_arg(c, Z3_to_app(c, assertion), i);
            if text(c, arg) == "xp" {
                xp = arg;
            }
        }
        assert_ne!(xp, 0, "parsed assertion {}", text(c, assertion));
        let v0 = Z3_mk_bound(c, 0, int_sort);
        let q = db_quantifier(c, true, &[int_sort], &[c"xp"], &[], Z3_mk_ge(c, v0, xp));
        assert_ne!(q, 0, "{}", error_text(c));
        assert_eq!(check(c, &[q]), Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// A pattern's de Bruijn variables are the quantifier's (`q1_pins.py` 4):
/// `forall x. f(x) = 0` with pattern `f(x)` beside `f(3) = 1` is unsat in z3.
/// AY refused the pattern ("trigger must contain at least one bound variable").
#[test]
fn q1_pattern_variables_are_bound() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let f = Z3_mk_func_decl(c, sym(c, c"f4"), 1, &raw const int_sort, int_sort);
        let v0 = Z3_mk_bound(c, 0, int_sort);
        let fv = Z3_mk_app(c, f, 1, &raw const v0);
        let pattern = Z3_mk_pattern(c, 1, &raw const fv);
        let body = Z3_mk_eq(c, fv, int(c, 0));
        let q = db_quantifier(c, true, &[int_sort], &[c"x"], &[pattern], body);
        assert_ne!(q, 0, "{}", error_text(c));
        assert_eq!(Z3_get_quantifier_num_patterns(c, q), 1);
        let three = int(c, 3);
        let f3 = Z3_mk_app(c, f, 1, &raw const three);
        assert_eq!(
            check(c, &[q, Z3_mk_eq(c, f3, int(c, 1))]),
            Z3_L_FALSE,
            "z3: unsat"
        );
        Z3_del_context(c);
    }
}

/// Nested binders: an index past the inner binder names the outer one
/// (`q1_pins.py` 5, 8; `extra_pins.py` a). z3: `forall x. exists y. x < y`
/// sat and its negation unsat, also when both binders are named `x`;
/// `exists p. forall y. p` sat, negation unsat. AY left the outer index free
/// and answered sat for every negation. AY may answer unknown, never sat.
#[test]
fn q1_nested_binders_resolve_outer_indices() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, bool_sort) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let (v0, v1) = (Z3_mk_bound(c, 0, int_sort), Z3_mk_bound(c, 1, int_sort));
        for inner_name in [c"y", c"x"] {
            let inner = db_quantifier(
                c,
                false,
                &[int_sort],
                &[inner_name],
                &[],
                Z3_mk_lt(c, v1, v0),
            );
            assert_ne!(inner, 0, "{}", error_text(c));
            let q = db_quantifier(c, true, &[int_sort], &[c"x"], &[], inner);
            assert_ne!(q, 0, "{}", error_text(c));
            assert_ne!(check(c, &[q]), Z3_L_FALSE, "z3: sat ({})", text(c, q));
            assert_ne!(
                check(c, &[not(c, q)]),
                Z3_L_TRUE,
                "z3: unsat ({})",
                text(c, q)
            );
        }
        let p = Z3_mk_bound(c, 1, bool_sort);
        let inner = db_quantifier(c, true, &[int_sort], &[c"y"], &[], p);
        let q = db_quantifier(c, false, &[bool_sort], &[c"p"], &[], inner);
        assert_ne!(q, 0, "{}", error_text(c));
        assert_eq!(check(c, &[q]), Z3_L_TRUE, "z3: sat");
        assert_ne!(check(c, &[not(c, q)]), Z3_L_TRUE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// Two binders in one quantifier (`q1_pins.py` 6): `forall a b. a - b = 1` is
/// unsat in z3 (index 1 is `a`, index 0 is `b`), its negation sat.
#[test]
fn q1_two_binders_take_their_indices() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (v0, v1) = (Z3_mk_bound(c, 0, int_sort), Z3_mk_bound(c, 1, int_sort));
        let body = Z3_mk_eq(c, Z3_mk_sub(c, 2, [v1, v0].as_ptr()), int(c, 1));
        let q = db_quantifier(c, true, &[int_sort, int_sort], &[c"a", c"b"], &[], body);
        assert_ne!(q, 0, "{}", error_text(c));
        assert_eq!(check(c, &[q]), Z3_L_FALSE, "z3: unsat");
        assert_eq!(check(c, &[not(c, q)]), Z3_L_TRUE, "z3: sat");
        Z3_del_context(c);
    }
}

/// An ill-sorted body variable is refused with `Z3_INVALID_ARG` (T5 design
/// P0.2 Q1). z3 accepts the AST and answers unsat (`judge_fid/f1.py` b,
/// `judge_sound/j6.py`); AY answered sat (`forall x:Int. (:var 0):Real > 0`).
#[test]
fn q1_ill_sorted_body_variable_is_refused() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, real_sort, bool_sort) =
            (Z3_mk_int_sort(c), Z3_mk_real_sort(c), Z3_mk_bool_sort(c));
        let vr = Z3_mk_bound(c, 0, real_sort);
        let body = Z3_mk_gt(c, vr, real(c, 0, 1));
        assert_eq!(db_quantifier(c, true, &[int_sort], &[c"x"], &[], body), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        let vb = Z3_mk_bound(c, 0, bool_sort);
        assert_eq!(db_quantifier(c, false, &[int_sort], &[c"x"], &[], vb), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        let lambda_body = add(c, &[vr, real(c, 1, 1)]);
        assert_eq!(db_lambda(c, int_sort, c"x", lambda_body), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

/// A Char binder over an escaping Char variable (`q1_pins.py` 10): `forall
/// ch:Char. exists k:Int. char.to_int(ch) = k` is sat in z3, negation unsat.
/// AY answered sat for the negation. AY may answer unknown, never the other.
#[test]
fn q1_char_variable_escaping_an_inner_binder_keeps_its_sort() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, char_sort) = (Z3_mk_int_sort(c), Z3_mk_char_sort(c));
        let ch = Z3_mk_bound(c, 1, char_sort);
        let body = Z3_mk_eq(c, Z3_mk_char_to_int(c, ch), Z3_mk_bound(c, 0, int_sort));
        let inner = db_quantifier(c, false, &[int_sort], &[c"k"], &[], body);
        assert_ne!(inner, 0, "{}", error_text(c));
        let q = db_quantifier(c, true, &[char_sort], &[c"ch"], &[], inner);
        assert_ne!(q, 0, "{}", error_text(c));
        assert_ne!(check(c, &[q]), Z3_L_FALSE, "z3: sat");
        assert_ne!(check(c, &[not(c, q)]), Z3_L_TRUE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// One de Bruijn index at a FiniteSet sort and at its characteristic array
/// sort shares one AY engine variable, so the second is refused rather than
/// silently re-sorting the first (z3 keeps both: `extra_pins.py` e2).
#[test]
fn q1_finite_set_and_its_array_cannot_share_a_bound_index() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, bool_sort) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let set_sort = Z3_mk_finite_set_sort(c, int_sort);
        assert!(!set_sort.is_null(), "{}", error_text(c));
        let as_set = Z3_mk_bound(c, 0, set_sort);
        assert_ne!(as_set, 0, "{}", error_text(c));
        let array_sort = Z3_mk_array_sort(c, int_sort, bool_sort);
        assert_eq!(Z3_mk_bound(c, 0, array_sort), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(
            Z3_get_sort(c, as_set),
            set_sort,
            "the first stays a FiniteSet"
        );
        Z3_del_context(c);
    }
}

/// `Z3_mk_lambda` shares the binder rules: a name reused at another sort
/// builds (z3: `(lambda ((lw Bool)) (not lw))`, `extra_pins.py` h), and
/// beta reduction stays exact.
#[test]
fn q1_lambda_binder_name_at_a_second_sort() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, bool_sort) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let vi = Z3_mk_bound(c, 0, int_sort);
        let l_int = db_lambda(c, int_sort, c"lw", add(c, &[vi, int(c, 1)]));
        assert_ne!(l_int, 0, "{}", error_text(c));
        let vb = Z3_mk_bound(c, 0, bool_sort);
        let l_bool = db_lambda(c, bool_sort, c"lw", not(c, vb));
        assert_ne!(l_bool, 0, "{}", error_text(c));
        let shown = text(c, l_bool);
        assert!(
            shown.contains("lw Bool") && !shown.contains("!ay."),
            "{shown}"
        );
        let at_true = Z3_mk_select(c, l_bool, Z3_mk_true(c));
        assert_eq!(check(c, &[Z3_mk_eq(c, at_true, Z3_mk_false(c))]), Z3_L_TRUE);
        let at_41 = Z3_mk_select(c, l_int, int(c, 41));
        assert_eq!(
            check(c, &[not(c, Z3_mk_eq(c, at_41, int(c, 42)))]),
            Z3_L_FALSE
        );
        Z3_del_context(c);
    }
}
