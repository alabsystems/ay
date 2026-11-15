// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression battery for the third round of the Z3 C API differential runs
//! (z3py 5.1.0 against AY's dylib): an FP `-0` numeral is negative zero; a
//! symbolic function interpretation declares nothing in the context; an
//! Optimize core is sound beside a Solver; a published sat makes every
//! assertion and assumption literally true under the published model (with
//! z3's completion of absent functions); parsed declarations are the
//! context's own; and a definition adopted for one check rewrites no term
//! built for another.

use std::ffi::{CStr, CString};

use super::solver_model_scope_tests::{evaluates_true, mk_ctx, named_const};
use super::*;

/// A one-argument function declaration `name : dom -> range`.
unsafe fn func1(c: Z3_context, name: &str, dom: Z3_sort, range: Z3_sort) -> Z3_func_decl {
    let name = CString::new(name).expect("test symbol has no NUL");
    // SAFETY: live context and sorts; `name` outlives the call.
    unsafe {
        Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, name.as_ptr()),
            1,
            [dom].as_ptr(),
            range,
        )
    }
}

/// `f(arg)`.
unsafe fn app1(c: Z3_context, f: Z3_func_decl, arg: Z3_ast) -> Z3_ast {
    // SAFETY: live context, declaration and argument of the declared sort.
    unsafe { Z3_mk_app(c, f, 1, [arg].as_ptr()) }
}

/// `forall bound. body` over caller constants (z3py `ForAll`).
unsafe fn forall(c: Z3_context, bound: &[Z3_ast], body: Z3_ast) -> Z3_ast {
    // SAFETY: live context; `bound` are constants of it.
    unsafe {
        let apps: Vec<Z3_ast> = bound.iter().map(|&b| Z3_to_app(c, b)).collect();
        Z3_mk_forall_const(c, 0, apps.len() as u32, apps.as_ptr(), 0, ptr::null(), body)
    }
}

/// `exists bound. body` over caller constants (z3py `Exists`).
unsafe fn exists(c: Z3_context, bound: &[Z3_ast], body: Z3_ast) -> Z3_ast {
    // SAFETY: live context; `bound` are constants of it.
    unsafe {
        let apps: Vec<Z3_ast> = bound.iter().map(|&b| Z3_to_app(c, b)).collect();
        Z3_mk_exists_const(c, 0, apps.len() as u32, apps.as_ptr(), 0, ptr::null(), body)
    }
}

/// Check `s` under `assumptions`; when sat, every term of `must_hold`
/// (assertions and assumptions) is literally true in the published model, and
/// an unknown carries a reason.
unsafe fn check_valid(
    c: Z3_context,
    s: Z3_solver,
    assumptions: &[Z3_ast],
    must_hold: &[Z3_ast],
) -> c_int {
    // SAFETY: live handles of `c`.
    unsafe {
        let r = Z3_solver_check_assumptions(c, s, assumptions.len() as u32, assumptions.as_ptr());
        if r == Z3_L_TRUE {
            let m = Z3_solver_get_model(c, s);
            assert!(!m.is_null(), "a published sat must carry a model");
            for &t in must_hold {
                assert!(
                    evaluates_true(c, m, t),
                    "published sat model does not satisfy {}; model:\n{}",
                    CStr::from_ptr(Z3_ast_to_string(c, t)).to_string_lossy(),
                    CStr::from_ptr(Z3_model_to_string(c, m)).to_string_lossy()
                );
            }
        } else if r == Z3_L_UNDEF {
            let reason = CStr::from_ptr(Z3_solver_get_reason_unknown(c, s)).to_string_lossy();
            assert!(!reason.is_empty(), "unknown must carry a reason");
        }
        r
    }
}

/// `Z3_model_eval(m, t, completion)` rendered as text.
unsafe fn eval_text(c: Z3_context, m: Z3_model, t: Z3_ast, completion: bool) -> Option<String> {
    let mut out: Z3_ast = 0;
    // SAFETY: live handles; `out` is a valid out-pointer.
    unsafe {
        Z3_model_eval(c, m, t, completion, &raw mut out).then(|| {
            CStr::from_ptr(Z3_ast_to_string(c, out))
                .to_string_lossy()
                .into_owned()
        })
    }
}

#[test]
fn a_negative_zero_fp_numeral_is_negative_zero() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let f32s = Z3_mk_fpa_sort_32(c);
        for text in ["-0", "-0.0", "-0/1p0"] {
            let t = CString::new(text).expect("no NUL");
            let a = Z3_mk_numeral(c, t.as_ptr(), f32s);
            assert_ne!(a, 0, "{text} is a numeral");
            // z3: fpIsNegative sat, fpIsPositive unsat (the baseline built +0).
            let s = Z3_mk_solver(c);
            Z3_solver_assert(c, s, Z3_mk_fpa_is_negative(c, a));
            assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE, "{text} is negative");
            let s = Z3_mk_solver(c);
            Z3_solver_assert(c, s, Z3_mk_fpa_is_positive(c, a));
            assert_ne!(Z3_solver_check(c, s), Z3_L_TRUE, "{text} is not positive");
        }
        Z3_del_context(c);
    }
}

#[test]
fn a_symbolic_function_interpretation_declares_nothing_in_the_context() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let real = Z3_mk_real_sort(c);
        // forall q. f(q) = q + 1 (Int), then forall r. g(r) = 2 r (Real): the
        // first check's interpretation `[else -> Var(0) + 1]` declared a
        // permanent Int `__db0`, so the second panicked in declare_const.
        let f = func1(c, "f", int, int);
        let q = named_const(c, "q", int);
        let one = Z3_mk_int(c, 1, int);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(
            c,
            s,
            forall(
                c,
                &[q],
                Z3_mk_eq(c, app1(c, f, q), Z3_mk_add(c, 2, [q, one].as_ptr())),
            ),
        );
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let g = func1(c, "g", real, real);
        let r = named_const(c, "r", real);
        let two = Z3_mk_real(c, 2, 1);
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(
            c,
            s2,
            forall(
                c,
                &[r],
                Z3_mk_eq(c, app1(c, g, r), Z3_mk_mul(c, 2, [two, r].as_ptr())),
            ),
        );
        assert_ne!(
            Z3_solver_check(c, s2),
            Z3_L_UNDEF,
            "{:?}",
            Z3_get_error_code(c)
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // z3py `Var(0, BoolSort())` works after both checks.
        assert_ne!(Z3_mk_bound(c, 0, Z3_mk_bool_sort(c)), 0);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // A later Optimize lists only its own symbol, never `__db0`.
        let x = named_const(c, "x", int);
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_le(c, x, Z3_mk_int(c, 10, int)));
        Z3_optimize_maximize(c, o, x);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        let m = Z3_optimize_get_model(c, o);
        let names: Vec<String> = (0..Z3_model_get_num_consts(c, m))
            .map(|i| {
                let d = Z3_model_get_const_decl(c, m, i);
                CStr::from_ptr(Z3_get_symbol_string(c, Z3_get_decl_name(c, d)))
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        assert_eq!(
            names,
            vec!["x".to_string()],
            "an Optimize model lists its own symbols"
        );
        Z3_del_context(c);
    }
}

#[test]
fn an_optimize_core_beside_a_solver_is_sound() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let bool_sort = Z3_mk_bool_sort(c);
        let xi = named_const(c, "xi", int);
        let k = |v: i32| Z3_mk_int(c, v, int);
        // A Solver check first, in the same context.
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_gt(c, xi, k(3)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        // probe S13: xi > 0 (p1), xi != 1 (p2), xi < 0 (p3).
        let p: Vec<Z3_ast> = ["p1", "p2", "p3"]
            .iter()
            .map(|n| named_const(c, n, bool_sort))
            .collect();
        let tracked = [
            Z3_mk_gt(c, xi, k(0)),
            Z3_mk_not(c, Z3_mk_eq(c, xi, k(1))),
            Z3_mk_lt(c, xi, k(0)),
        ];
        let o = Z3_mk_optimize(c);
        for (a, &lit) in tracked.iter().zip(&p) {
            Z3_optimize_assert_and_track(c, o, *a, lit);
        }
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
        let core = Z3_optimize_get_unsat_core(c, o);
        let core: Vec<Z3_ast> = (0..Z3_ast_vector_size(c, core))
            .map(|i| Z3_ast_vector_get(c, core, i))
            .collect();
        assert!(
            !core.is_empty(),
            "an empty core claims the untracked constraints are unsat"
        );
        // The core alone, with the tracked implications, is unsat.
        let s2 = Z3_mk_solver(c);
        for (a, &lit) in tracked.iter().zip(&p) {
            Z3_solver_assert(c, s2, Z3_mk_implies(c, lit, *a));
        }
        let r = Z3_solver_check_assumptions(c, s2, core.len() as u32, core.as_ptr());
        assert_eq!(r, Z3_L_FALSE, "the core is unsat on its own");

        // A tracking literal another hard constraint refutes: z3 assumes it,
        // so the problem is unsat (AY asserted `a` alone and answered sat).
        let c2 = mk_ctx();
        let x2 = named_const(c2, "x", Z3_mk_int_sort(c2));
        let t2 = named_const(c2, "t", Z3_mk_bool_sort(c2));
        let o2 = Z3_mk_optimize(c2);
        Z3_optimize_assert(c2, o2, Z3_mk_not(c2, t2));
        Z3_optimize_assert_and_track(
            c2,
            o2,
            Z3_mk_gt(c2, x2, Z3_mk_int(c2, 0, Z3_mk_int_sort(c2))),
            t2,
        );
        assert_eq!(Z3_optimize_check(c2, o2, 0, ptr::null()), Z3_L_FALSE);
        Z3_del_context(c2);
        Z3_del_context(c);
    }
}

#[test]
fn a_published_sat_satisfies_quantified_and_function_assumptions() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let bv8 = Z3_mk_bv_sort(c, 8);
        let u = named_const(c, "u", bv8);
        let zero8 = Z3_mk_int(c, 0, bv8);
        let k = |v: i32| Z3_mk_int(c, v, int);
        // W_36: (pr(-2) => false) and u <= 0, assuming forall q5. pr(5): z3
        // [pr = [5 -> True, else -> False]]; AY published pr = false.
        let pr = func1(c, "pr", int, Z3_mk_bool_sort(c));
        let q5 = named_const(c, "q5", int);
        let goal = Z3_mk_and(
            c,
            2,
            [
                Z3_mk_implies(c, app1(c, pr, k(-2)), Z3_mk_false(c)),
                Z3_mk_bvule(c, u, zero8),
            ]
            .as_ptr(),
        );
        let assumption = forall(c, &[q5], app1(c, pr, k(5)));
        let s = Z3_mk_simple_solver(c);
        Z3_solver_assert(c, s, goal);
        assert_ne!(
            check_valid(c, s, &[assumption], &[goal, assumption]),
            Z3_L_FALSE
        );

        // A_361: a function only in the assumption with BV assertions.
        let f = func1(c, "f", int, int);
        let fa = Z3_mk_gt(c, app1(c, f, k(0)), k(4));
        let ge = Z3_mk_bvuge(c, u, zero8);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, ge);
        assert_ne!(check_valid(c, s, &[fa], &[ge, fa]), Z3_L_FALSE);

        // A_1449: R = Store(R, 2, -3/2) over Array(Int, Real).
        let arr = Z3_mk_array_sort(c, int, Z3_mk_real_sort(c));
        let rr = named_const(c, "R", arr);
        let eq = Z3_mk_eq(c, Z3_mk_store(c, rr, k(2), Z3_mk_real(c, -3, 2)), rr);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, eq);
        assert_ne!(check_valid(c, s, &[], &[eq]), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

#[test]
fn model_completion_completes_functions_and_folds_values() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let cc = named_const(c, "c", int);
        let f = func1(c, "f", int, int);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_ge(c, cc, Z3_mk_int(c, 0, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        // z3: an absent function completes to its sort's default.
        assert_eq!(eval_text(c, m, app1(c, f, cc), true).as_deref(), Some("0"));
        // Without completion it stays symbolic.
        assert_ne!(eval_text(c, m, app1(c, f, cc), false).as_deref(), Some("0"));
        // Quantifiers over literal bodies, and over the model's constants.
        let q = named_const(c, "q", int);
        assert_eq!(
            eval_text(c, m, exists(c, &[q], Z3_mk_true(c)), true).as_deref(),
            Some("true")
        );
        assert_eq!(
            eval_text(c, m, forall(c, &[q], Z3_mk_true(c)), true).as_deref(),
            Some("true")
        );
        let ge = forall(c, &[q], Z3_mk_ge(c, cc, Z3_mk_int(c, 0, int)));
        assert_eq!(eval_text(c, m, ge, true).as_deref(), Some("true"));
        // bv2nat, int2bv and ^ over values.
        let five = Z3_mk_int(c, 5, Z3_mk_bv_sort(c, 8));
        assert_eq!(
            eval_text(c, m, Z3_mk_bv2int(c, five, false), true).as_deref(),
            Some("5")
        );
        let bv = Z3_mk_int2bv(c, 4, Z3_mk_int(c, 18, int));
        assert_eq!(eval_text(c, m, bv, true).as_deref(), Some("#x2"));
        let pw = Z3_mk_power(c, Z3_mk_int(c, 2, int), Z3_mk_int(c, -1, int));
        // 2 ^ -1 is the Real 1/2 (z3 prints `(/ 1.0 2.0)`).
        let mut out: Z3_ast = 0;
        assert!(Z3_model_eval(c, m, pw, true, &raw mut out));
        assert_eq!(
            CStr::from_ptr(Z3_get_numeral_string(c, out)).to_string_lossy(),
            "1/2"
        );
        Z3_del_context(c);
    }
}

#[test]
fn parsed_declarations_are_the_contexts_own() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let bool_sort = Z3_mk_bool_sort(c);
        let int = Z3_mk_int_sort(c);
        // B_469: p = Bool('p'); from_string('(declare-fun p () Bool)(assert
        // p)'); check(Not(p)) is unsat in z3.
        let p = named_const(c, "p", bool_sort);
        let s = Z3_mk_solver(c);
        let text = CString::new("(declare-fun p () Bool)(assert p)").expect("no NUL");
        Z3_solver_from_string(c, s, text.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let not_p = Z3_mk_not(c, p);
        assert_eq!(
            Z3_solver_check_assumptions(c, s, 1, [not_p].as_ptr()),
            Z3_L_FALSE
        );
        // A_1508: the parse first names `a`, then the API's `a == 0`.
        let a = named_const(c, "a", int);
        let s = Z3_mk_solver(c);
        let text = CString::new("(declare-fun a () Int)(assert (> a 4))").expect("no NUL");
        Z3_solver_from_string(c, s, text.as_ptr());
        Z3_solver_assert(c, s, Z3_mk_eq(c, a, Z3_mk_int(c, 0, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        // Another solver may declare `a` again, and a solver's later parse
        // sees its earlier declarations (z3's per-solver command context).
        let s = Z3_mk_solver(c);
        Z3_solver_from_string(c, s, text.as_ptr());
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "a second declaration of a is accepted"
        );
        let more = CString::new("(assert (< a 6))").expect("no NUL");
        Z3_solver_from_string(c, s, more.as_ptr());
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "the solver's own declaration is visible"
        );
        let eq5 = Z3_mk_eq(c, a, Z3_mk_int(c, 5, int));
        assert_eq!(
            check_valid(c, s, &[], &[eq5]),
            Z3_L_TRUE,
            "a = 5 is the only model"
        );
        // A name parsed first is the API's constant of that name afterwards.
        let s = Z3_mk_solver(c);
        let text = CString::new("(declare-fun z () Int)(assert (= z 7))").expect("no NUL");
        Z3_solver_from_string(c, s, text.as_ptr());
        let z = named_const(c, "z", int);
        Z3_solver_assert(c, s, Z3_mk_eq(c, z, Z3_mk_int(c, 8, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        // Z3_parse_smtlib2_string binds caller-named declarations.
        let x = named_const(c, "x", int);
        let g = func1(c, "g", int, int);
        let names: Vec<Z3_symbol> = ["foo", "g"]
            .iter()
            .map(|n| {
                let n = CString::new(*n).expect("no NUL");
                Z3_mk_string_symbol(c, n.as_ptr())
            })
            .collect();
        let decls = [Z3_get_app_decl(c, Z3_to_app(c, x)), g];
        let text = CString::new("(assert (> (+ foo (g foo)) 0))").expect("no NUL");
        let v = Z3_parse_smtlib2_string(
            c,
            text.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            2,
            names.as_ptr(),
            decls.as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_ast_vector_size(c, v), 1);
        let parsed = Z3_ast_vector_get(c, v, 0);
        let expected = Z3_mk_gt(
            c,
            Z3_mk_add(c, 2, [x, app1(c, g, x)].as_ptr()),
            Z3_mk_int(c, 0, int),
        );
        assert_eq!(
            CStr::from_ptr(Z3_ast_to_string(c, parsed)).to_string_lossy(),
            CStr::from_ptr(Z3_ast_to_string(c, expected)).to_string_lossy()
        );
        Z3_del_context(c);
    }
}

#[test]
fn an_adopted_definition_rewrites_no_term_built_for_another_handle() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let k = |v: i32| Z3_mk_int(c, v, int);
        let x = named_const(c, "x", int);
        let y = named_const(c, "y", int);
        let f = func1(c, "f", int, int);
        // probe unsat7: s2 adopts forall y. f(y) = y + 1; `late` is built
        // after its check; s3 asserts x > 1 and late. z3: sat [x = 2, f = 0].
        let s2 = Z3_mk_solver(c);
        let def = forall(
            c,
            &[y],
            Z3_mk_eq(c, app1(c, f, y), Z3_mk_add(c, 2, [y, k(1)].as_ptr())),
        );
        Z3_solver_assert(c, s2, def);
        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE);
        let late = Z3_mk_eq(c, app1(c, f, x), k(0));
        let s3 = Z3_mk_solver(c);
        let gt = Z3_mk_gt(c, x, k(1));
        Z3_solver_assert(c, s3, gt);
        Z3_solver_assert(c, s3, late);
        assert_eq!(check_valid(c, s3, &[], &[gt, late]), Z3_L_TRUE);
        // The same solver after reset: the definition is gone with it.
        Z3_solver_reset(c, s2);
        Z3_solver_assert(c, s2, gt);
        Z3_solver_assert(c, s2, late);
        assert_eq!(check_valid(c, s2, &[], &[gt, late]), Z3_L_TRUE);
        // And the defining solver still uses its definition: f(x) = 0 is
        // refuted under x > 1.
        let s4 = Z3_mk_solver(c);
        Z3_solver_assert(c, s4, def);
        Z3_solver_assert(c, s4, gt);
        Z3_solver_assert(c, s4, late);
        assert_ne!(Z3_solver_check(c, s4), Z3_L_TRUE);
        Z3_del_context(c);
    }
}
