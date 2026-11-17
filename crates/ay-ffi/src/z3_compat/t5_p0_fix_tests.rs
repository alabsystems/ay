// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T5 P0 regressions the verification round found in the quarantine
//! (claude/ffi-t5-base 7c46d84d85), each pinned to libz3 5.1.0 through the
//! probe script `~/ay-bench/t5-p0fix/p0fix.py` (z3py 5.1.0 over the real
//! library, and the 7c46d84d85 dylib for the regression):
//!
//! * (a) Q12's quantified guard of an `Array(_, Char/FD)` constant made
//!   quantifier-free sat goals `unknown`; a SAT model is now validated
//!   against the guard, which is asserted only by a re-check.
//! * (b) a free datatype constant with a `Char` field refused every goal with
//!   a binder; it now carries its quantifier-free guard.
//! * (d) a `Char` value's declaration had no parameter, so z3py raised
//!   printing any `Char` value; model text printed `Char` values as `Int`s.

use std::ffi::CStr;
use std::ptr;

use super::t5_p0_y_tests::{ctx, int, int_const, sym, text};
use crate::z3_compat::*;

unsafe fn check_one(c: Z3_context, formulas: &[Z3_ast]) -> (i32, Z3_solver) {
    // SAFETY: the caller passes a live context `c` owned by this test.
    unsafe {
        let s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        for &formula in formulas {
            Z3_solver_assert(c, s, formula);
        }
        (Z3_solver_check(c, s), s)
    }
}

unsafe fn exists_int(c: Z3_context, name: &CStr, body: impl Fn(Z3_ast) -> Z3_ast) -> Z3_ast {
    // SAFETY: `c` is live; the bound array lives across the call.
    unsafe {
        let x = int_const(c, name);
        Z3_mk_exists_const(c, 0, 1, [x].as_ptr(), 0, ptr::null(), body(x))
    }
}

unsafe fn char_val(c: Z3_context, ch: char) -> Z3_ast {
    // SAFETY: `c` is live.
    unsafe { Z3_mk_char(c, u32::from(ch)) }
}

unsafe fn code(c: Z3_context, ch: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is live and `ch` one of its `Char` terms.
    unsafe { Z3_mk_char_to_int(c, ch) }
}

/// The model text of `s`'s last check.
unsafe fn model_text(c: Z3_context, s: Z3_solver) -> String {
    // SAFETY: `s` is a live solver of `c` whose last check was sat.
    unsafe {
        let m = Z3_solver_get_model(c, s);
        assert!(!m.is_null(), "a sat check has a model");
        text(Z3_model_to_string(c, m))
    }
}

/// p0fix.py case `a_arrays`: libz3 5.1.0 answers `A[0] == 'a'`,
/// `code(A[3]) == 65` and `A == B, A[0] != 'z'` over `Array(Int, Char)`, and
/// `C[0] != C[1]` over `Array(Int, FiniteDomain(3))`, `sat`; 7c46d84d85
/// answered each `unknown` ("incomplete quantifier-unhandled") under the
/// array guard, 8dfa403f5f `sat`. The published model keeps every element in
/// range.
#[test]
fn quantifier_free_array_goals_are_sat_with_a_model_in_range() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let char_sort = Z3_mk_char_sort(c);
        let array_sort = Z3_mk_array_sort(c, Z3_mk_int_sort(c), char_sort);
        let a = Z3_mk_const(c, sym(c, c"A"), array_sort);
        let b = Z3_mk_const(c, sym(c, c"B"), array_sort);
        let a0 = Z3_mk_select(c, a, int(c, 0));
        let goals = [
            vec![Z3_mk_eq(c, a0, char_val(c, 'a'))],
            vec![Z3_mk_eq(
                c,
                code(c, Z3_mk_select(c, a, int(c, 3))),
                int(c, 65),
            )],
            vec![
                Z3_mk_eq(c, a, b),
                Z3_mk_not(c, Z3_mk_eq(c, a0, char_val(c, 'z'))),
            ],
        ];
        for goal in &goals {
            let (verdict, s) = check_one(c, goal);
            assert_eq!(verdict, Z3_L_TRUE, "z3: sat");
            let model = model_text(c, s);
            assert!(!model.contains("196608"), "{model}");
            Z3_solver_dec_ref(c, s);
        }
        let fd = Z3_mk_finite_domain_sort(c, sym(c, c"F"), 3);
        let fd_array = Z3_mk_const(c, sym(c, c"C"), Z3_mk_array_sort(c, Z3_mk_int_sort(c), fd));
        let differ = Z3_mk_not(
            c,
            Z3_mk_eq(
                c,
                Z3_mk_select(c, fd_array, int(c, 0)),
                Z3_mk_select(c, fd_array, int(c, 1)),
            ),
        );
        assert_eq!(check_one(c, &[differ]).0, Z3_L_TRUE, "z3: sat");
        Z3_del_context(c);
    }
}

/// p0fix.py cases `a_arrays` / `a_functions`: the goals the guards decide
/// stay decided. libz3 5.1.0: `code(A[3]) > 196607` (built by
/// `Z3_substitute`, without the range axiom of an API-built select) and
/// `Exists x. code(A[x]) > 196607`, `Exists x. code(ch(x)) > 196607` are
/// unsat; `Exists x. code(ch(x)) == 65` is sat (7c46d84d85: `unknown`).
#[test]
fn guarded_goals_keep_their_verdicts() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let char_sort = Z3_mk_char_sort(c);
        let a = Z3_mk_const(
            c,
            sym(c, c"As"),
            Z3_mk_array_sort(c, Z3_mk_int_sort(c), char_sort),
        );
        let ch = Z3_mk_func_decl(c, sym(c, c"ch"), 1, [Z3_mk_int_sort(c)].as_ptr(), char_sort);
        let max = int(c, 196_607);
        let x = int_const(c, c"sx");
        let over_a = Z3_mk_gt(c, code(c, Z3_mk_select(c, a, x)), max);
        let ground = Z3_substitute(c, over_a, 1, [x].as_ptr(), [int(c, 3)].as_ptr());
        assert_eq!(check_one(c, &[ground]).0, Z3_L_FALSE, "z3: unsat");
        let e_array = exists_int(c, c"ea", |x| {
            Z3_mk_gt(c, code(c, Z3_mk_select(c, a, x)), max)
        });
        assert_eq!(check_one(c, &[e_array]).0, Z3_L_FALSE, "z3: unsat");
        let app = |x: Z3_ast| code(c, Z3_mk_app(c, ch, 1, [x].as_ptr()));
        let e_over = exists_int(c, c"eo", |x| Z3_mk_gt(c, app(x), max));
        assert_eq!(check_one(c, &[e_over]).0, Z3_L_FALSE, "z3: unsat");
        let e_in = exists_int(c, c"ei", |x| Z3_mk_eq(c, app(x), int(c, 65)));
        let (verdict, s) = check_one(c, &[e_in]);
        assert_eq!(verdict, Z3_L_TRUE, "z3: sat");
        assert!(!model_text(c, s).contains("196608"));
        Z3_del_context(c);
    }
}

/// `W = w(c: Char)`: one constructor, one `Char` field.
unsafe fn char_record(c: Z3_context) -> (Z3_sort, Z3_func_decl) {
    // SAFETY: `c` is live; the arrays live across each call.
    unsafe {
        let fields = [sym(c, c"c")];
        let sorts = [Z3_mk_char_sort(c)];
        let refs = [0u32];
        let ctor = Z3_mk_constructor(
            c,
            sym(c, c"w"),
            sym(c, c"is_w"),
            1,
            fields.as_ptr(),
            sorts.as_ptr(),
            refs.as_ptr(),
        );
        let mut ctors = [ctor];
        let sort = Z3_mk_datatype(c, sym(c, c"W"), 1, ctors.as_mut_ptr());
        let mut constructor = ptr::null_mut();
        let mut tester = ptr::null_mut();
        let mut accessor = [ptr::null_mut()];
        Z3_query_constructor(
            c,
            ctor,
            1,
            &raw mut constructor,
            &raw mut tester,
            accessor.as_mut_ptr(),
        );
        (sort, accessor[0])
    }
}

/// p0fix.py case `b_datatypes`: libz3 5.1.0 answers `c(d) == 'q'` beside an
/// unrelated `ForAll x. x*0 == 0`, and `Exists x. x > 2 ∧ code(c(d)) == x`,
/// `sat`; `Exists x. code(c(ite(x > 0, d, e))) > 196607` is unsat.
/// 7c46d84d85 refused all three ("d: a Char or finite-domain valued symbol
/// of the goal has no well-formedness guard"), 8dfa403f5f answered the last
/// one `sat`. The constants now carry `0 <= code(c(d)) <= 196607`.
#[test]
fn datatype_constants_with_char_fields_are_guarded_not_refused() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let (w, field) = char_record(c);
        let d = Z3_mk_const(c, sym(c, c"d"), w);
        let e = Z3_mk_const(c, sym(c, c"e"), w);
        let c_of = |t: Z3_ast| Z3_mk_app(c, field, 1, [t].as_ptr());
        let x = int_const(c, c"x");
        let unrelated = Z3_mk_forall_const(
            c,
            0,
            1,
            [x].as_ptr(),
            0,
            ptr::null(),
            Z3_mk_eq(c, Z3_mk_mul(c, 2, [x, int(c, 0)].as_ptr()), int(c, 0)),
        );
        let is_q = Z3_mk_eq(c, c_of(d), char_val(c, 'q'));
        assert_eq!(check_one(c, &[is_q, unrelated]).0, Z3_L_TRUE, "z3: sat");
        let witness = exists_int(c, c"wx", |x| {
            Z3_mk_and(
                c,
                2,
                [Z3_mk_gt(c, x, int(c, 2)), Z3_mk_eq(c, code(c, c_of(d)), x)].as_ptr(),
            )
        });
        assert_eq!(check_one(c, &[witness]).0, Z3_L_TRUE, "z3: sat");
        let over = exists_int(c, c"ox", |x| {
            let pick = Z3_mk_ite(c, Z3_mk_gt(c, x, int(c, 0)), d, e);
            Z3_mk_gt(c, code(c, c_of(pick)), int(c, 196_607))
        });
        assert_eq!(check_one(c, &[over]).0, Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// p0fix.py case `d_char_values`: libz3 5.1.0 gives a character literal's
/// declaration one integer parameter, its code point (`CharVal('e')
/// .decl().params()` is `[101]`), which z3py prints `Char` values by;
/// `CharVal('e').sexpr()` is `(_ Char 101)`, and a model prints a `Char`
/// constant `(define-fun c () Unicode (_ Char 104))`, whose `m.eval(c)` is
/// `Char`-sorted. 7c46d84d85 gave no parameter (z3py raised `IndexError`
/// printing any `Char` value) and printed `(define-fun c () Int 104)`.
#[test]
fn char_values_carry_their_code_point_and_sort() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let e = char_val(c, 'e');
        let decl = Z3_get_app_decl(c, Z3_to_app(c, e));
        assert_eq!(Z3_get_decl_kind(c, decl), Z3_OP_CHAR_CONST);
        assert_eq!(Z3_get_decl_num_parameters(c, decl), 1);
        assert_eq!(Z3_get_decl_parameter_kind(c, decl, 0), Z3_PARAMETER_INT);
        assert_eq!(Z3_get_decl_int_parameter(c, decl, 0), 101);
        assert_eq!(text(Z3_ast_to_string(c, e)), "(_ Char 101)");

        let ch = Z3_mk_const(c, sym(c, c"ch"), Z3_mk_char_sort(c));
        let (verdict, s) = check_one(c, &[Z3_mk_eq(c, code(c, ch), int(c, 104))]);
        assert_eq!(verdict, Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        let printed = text(Z3_model_to_string(c, m));
        assert!(
            printed.contains("(define-fun ch () Unicode (_ Char 104))"),
            "{printed}"
        );
        let value = Z3_model_get_const_interp(c, m, Z3_get_app_decl(c, Z3_to_app(c, ch)));
        assert_ne!(value, 0);
        let value_decl = Z3_get_app_decl(c, Z3_to_app(c, value));
        assert_eq!(Z3_get_decl_int_parameter(c, value_decl, 0), 104);
        // `Z3_mk_char_to_int` returned `ch`'s own handle re-recorded as
        // `Int` (the handle aliasing T5 P1 removes), so `ch` is evaluated
        // through a constant no `Z3_mk_char_to_int` touched.
        let d = Z3_mk_const(c, sym(c, c"dh"), Z3_mk_char_sort(c));
        let (verdict, s) = check_one(c, &[Z3_mk_eq(c, d, char_val(c, 'h'))]);
        assert_eq!(verdict, Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        let mut evaluated = 0;
        assert!(Z3_model_eval(c, m, d, true, &raw mut evaluated));
        let sort = Z3_get_sort(c, evaluated);
        assert_eq!(Z3_get_sort_kind(c, sort), Z3_CHAR_SORT);
        assert_eq!(text(Z3_ast_to_string(c, evaluated)), "(_ Char 104)");
        Z3_del_context(c);
    }
}

/// p0fix.py case `d_char_values`: a finite-domain constant prints at its
/// sort, `(define-fun xv () S 1)` in libz3 5.1.0 (7c46d84d85: `Int`).
#[test]
fn finite_domain_values_print_at_their_sort() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let fd = Z3_mk_finite_domain_sort(c, sym(c, c"S"), 5);
        let xv = Z3_mk_const(c, sym(c, c"xv"), fd);
        let three = Z3_mk_numeral(c, c"3".as_ptr(), fd);
        let (verdict, s) = check_one(c, &[Z3_mk_eq(c, xv, three)]);
        assert_eq!(verdict, Z3_L_TRUE);
        let printed = model_text(c, s);
        assert!(printed.contains("(define-fun xv () S 3)"), "{printed}");
        Z3_del_context(c);
    }
}

/// `~/ay-bench/t5-p0fix/p0fix_opt.py` case `opt`: libz3 5.1.0 maximizes
/// `x <= 7` beside `A[0] == 'a'` over `Array(Int, Char)` to 7 and
/// `code(A[0])` to 196607; 7c46d84d85 answered both `unknown` under the
/// array guard, 8dfa403f5f gave both. The optimum of the relaxed goal is
/// published only when its model satisfies the guard and the optimum is
/// attained: the unbounded relaxed `code(A[0])` is re-checked with the guard,
/// never published as unbounded.
#[test]
fn optimize_over_char_arrays_validates_the_relaxed_optimum() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let array_sort = Z3_mk_array_sort(c, Z3_mk_int_sort(c), Z3_mk_char_sort(c));
        let a = Z3_mk_const(c, sym(c, c"A"), array_sort);
        let a0 = Z3_mk_select(c, a, int(c, 0));
        let x = int_const(c, c"x");
        let o = Z3_mk_optimize(c);
        Z3_optimize_inc_ref(c, o);
        Z3_optimize_assert(c, o, Z3_mk_eq(c, a0, char_val(c, 'a')));
        Z3_optimize_assert(c, o, Z3_mk_le(c, x, int(c, 7)));
        let objective = Z3_optimize_maximize(c, o, x);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE, "z3: 7");
        assert_eq!(
            text(Z3_ast_to_string(c, Z3_optimize_get_upper(c, o, objective))),
            "7"
        );
        Z3_optimize_dec_ref(c, o);

        let o = Z3_mk_optimize(c);
        Z3_optimize_inc_ref(c, o);
        let objective = Z3_optimize_maximize(c, o, code(c, a0));
        let verdict = Z3_optimize_check(c, o, 0, ptr::null());
        if verdict == Z3_L_TRUE {
            let upper = text(Z3_ast_to_string(c, Z3_optimize_get_upper(c, o, objective)));
            assert_eq!(upper, "196607", "z3: 196607");
        } else {
            assert_eq!(verdict, Z3_L_UNDEF, "never unsat");
        }
        Z3_optimize_dec_ref(c, o);
        Z3_del_context(c);
    }
}

/// p0fix.py case `a_arrays` / `p0fix_arr.py nested_subst`: over
/// `AA : Array(Int, Array(Int, Char))`, libz3 5.1.0 answers `AA[1][2] ==
/// 'c'` sat and `code(AA[1][3]) > 196607` (built by `Z3_substitute`) unsat;
/// 7c46d84d85 answered unknown and unsat. The guard is one quantifier over
/// both indices: a nested `forall i. forall j.` left the second unknown.
#[test]
fn nested_char_arrays_are_guarded_by_one_quantifier() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let inner = Z3_mk_array_sort(c, int_sort, Z3_mk_char_sort(c));
        let aa = Z3_mk_const(c, sym(c, c"AA"), Z3_mk_array_sort(c, int_sort, inner));
        let row = |i: i32, j: Z3_ast| Z3_mk_select(c, Z3_mk_select(c, aa, int(c, i)), j);
        let sat_goal = Z3_mk_eq(c, row(1, int(c, 2)), char_val(c, 'c'));
        assert_eq!(check_one(c, &[sat_goal]).0, Z3_L_TRUE, "z3: sat");
        let x = int_const(c, c"nx");
        let over = Z3_mk_gt(c, code(c, row(1, x)), int(c, 196_607));
        let ground = Z3_substitute(c, over, 1, [x].as_ptr(), [int(c, 3)].as_ptr());
        assert_eq!(check_one(c, &[ground]).0, Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}
