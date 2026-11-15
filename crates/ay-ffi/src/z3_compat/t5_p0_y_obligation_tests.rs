// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T5 P0.2 quarantine, implementer Y: Q8 (adopted definitions released after
//! every Optimize operation, consequences and implied equalities), Q9
//! (Optimize asserts only the recursive axioms its goal reaches) and Q12
//! (well-formedness guards and lossy binder sorts).
//!
//! Every pin cites its libz3 5.1.0 measurement: z3py 5.1.0 over the real
//! library, one case of the T5 P0 implementer-Y pin script `ypins.py`
//! (`~/ay-bench/t5y-bench`), and `ffi-v3-2/x33.py`, `judge_sound/j7.py`.

use std::ffi::{c_uint, CStr};
use std::ptr;
use std::time::{Duration, Instant};

use super::t5_p0_y_tests::{ctx, int, int_const, sym, text};
use crate::z3_compat::*;

/// `f : Int -> Int`, uninterpreted.
unsafe fn f_decl(c: Z3_context) -> Z3_func_decl {
    // SAFETY: `c` is live; the domain array lives across the call.
    unsafe {
        let domain = [Z3_mk_int_sort(c)];
        Z3_mk_func_decl(c, sym(c, c"f"), 1, domain.as_ptr(), Z3_mk_int_sort(c))
    }
}

/// The definitional `forall y. f(y) = y + 1` the engine adopts as a macro.
unsafe fn definition(c: Z3_context, f: Z3_func_decl) -> Z3_ast {
    // SAFETY: `c` is live; the arrays live across each call.
    unsafe {
        let y = int_const(c, c"y");
        let fy = Z3_mk_app(c, f, 1, [y].as_ptr());
        let body = Z3_mk_eq(c, fy, Z3_mk_add(c, 2, [y, int(c, 1)].as_ptr()));
        Z3_mk_forall_const(c, 0, 1, [y].as_ptr(), 0, ptr::null(), body)
    }
}

/// x33.py's victim: `f(x) == 0` built now, checked by another solver with
/// `x > 1`. libz3 5.1.0 keeps the application (`f(x) == 0`) and answers sat
/// after every operation of x33.py / ypins.py q8_optimize_ops,
/// q8_consequences, q8_implied_equalities.
unsafe fn assert_victim_unaffected(c: Z3_context, after: &str) {
    // SAFETY: the caller passes a live context `c` owned by this test.
    unsafe {
        let f = f_decl(c);
        let x = int_const(c, c"x");
        let late = Z3_mk_eq(c, Z3_mk_app(c, f, 1, [x].as_ptr()), int(c, 0));
        let printed = text(Z3_ast_to_string(c, late));
        assert!(
            printed.contains("(f x)"),
            "after {after}: built as {printed}"
        );
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, int(c, 1)));
        Z3_solver_assert(c, s, late);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE, "after {after}");
    }
}

#[test]
fn q8_optimize_operations_leave_no_definition_installed() {
    let operations: [(&str, unsafe fn(Z3_context, Z3_optimize)); 6] = [
        ("maximize", |c, o| unsafe {
            Z3_optimize_maximize(c, o, int_const(c, c"x"));
        }),
        ("minimize", |c, o| unsafe {
            Z3_optimize_minimize(c, o, int_const(c, c"x"));
        }),
        ("assert_soft", |c, o| unsafe {
            Z3_optimize_assert_soft(c, o, Z3_mk_true(c), c"1".as_ptr(), ptr::null_mut());
        }),
        ("push", |c, o| unsafe { Z3_optimize_push(c, o) }),
        ("set_params", |c, o| unsafe {
            let p = Z3_mk_params(c);
            Z3_params_set_uint(c, p, sym(c, c"timeout"), 100_000);
            Z3_optimize_set_params(c, o, p);
        }),
        ("check", |c, o| unsafe {
            Z3_optimize_maximize(c, o, int_const(c, c"x"));
            Z3_optimize_assert(c, o, Z3_mk_le(c, int_const(c, c"x"), int(c, 3)));
            let _ = Z3_optimize_check(c, o, 0, ptr::null());
        }),
    ];
    for (name, operation) in operations {
        // SAFETY: all handles belong to `c`, freed at the end.
        unsafe {
            let c = ctx();
            let o = Z3_mk_optimize(c);
            Z3_optimize_assert(c, o, definition(c, f_decl(c)));
            operation(c, o);
            assert_victim_unaffected(c, name);
            Z3_del_context(c);
        }
    }
}

#[test]
fn q8_auxiliary_queries_leave_no_definition_installed() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        let p = Z3_mk_const(c, sym(c, c"p"), Z3_mk_bool_sort(c));
        Z3_solver_assert(c, s, definition(c, f_decl(c)));
        let x = int_const(c, c"x");
        Z3_solver_assert(c, s, Z3_mk_implies(c, p, Z3_mk_gt(c, x, int(c, 0))));
        let assumptions = Z3_mk_ast_vector(c);
        Z3_ast_vector_push(c, assumptions, p);
        let out = Z3_mk_ast_vector(c);
        let _ = Z3_solver_get_consequences(c, s, assumptions, assumptions, out);
        assert_victim_unaffected(c, "consequences");

        let y = int_const(c, c"y");
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, y));
        let terms = [x, y];
        let mut classes: [c_uint; 2] = [0; 2];
        let _ = Z3_get_implied_equalities(c, s, 2, terms.as_ptr(), classes.as_mut_ptr());
        assert_victim_unaffected(c, "implied equalities");
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q9_unreachable): `maximize x` under `x <= 7` beside
/// an unrelated recursive function answers 7 at once. AY asserted every
/// recursive axiom and timed out (> 60 s).
#[test]
fn q9_optimize_ignores_unreached_recursive_definitions() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let domain = [Z3_mk_int_sort(c)];
        let fr = Z3_mk_rec_func_decl(c, sym(c, c"fr9"), 1, domain.as_ptr(), Z3_mk_int_sort(c));
        let n = int_const(c, c"n");
        let rec = Z3_mk_app(
            c,
            fr,
            1,
            [Z3_mk_sub(c, 2, [n, int(c, 1)].as_ptr())].as_ptr(),
        );
        let body = Z3_mk_ite(
            c,
            Z3_mk_le(c, n, int(c, 0)),
            int(c, 0),
            Z3_mk_add(c, 2, [n, rec].as_ptr()),
        );
        Z3_add_rec_def(c, fr, 1, [n].as_ptr(), body);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let o = Z3_mk_optimize(c);
        let x = int_const(c, c"x");
        Z3_optimize_assert(c, o, Z3_mk_le(c, x, int(c, 7)));
        let objective = Z3_optimize_maximize(c, o, x);
        let started = Instant::now();
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert!(started.elapsed() < Duration::from_secs(20));
        let upper = Z3_optimize_get_upper(c, o, objective);
        assert_eq!(text(Z3_get_numeral_string(c, upper)), "7");
        Z3_del_context(c);
    }
}

unsafe fn exists_int(c: Z3_context, name: &CStr, body: impl Fn(Z3_ast) -> Z3_ast) -> Z3_ast {
    // SAFETY: `c` is live; the bound array lives across the call.
    unsafe {
        let x = int_const(c, name);
        Z3_mk_exists_const(c, 0, 1, [x].as_ptr(), 0, ptr::null(), body(x))
    }
}

unsafe fn check_one(c: Z3_context, formula: Z3_ast) -> i32 {
    // SAFETY: the caller passes a live context `c` owned by this test.
    unsafe {
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, formula);
        Z3_solver_check(c, s)
    }
}

/// libz3 5.1.0 (judge_sound/j7.py E1/E2, ypins.py q12_j7): `Exists x.
/// code(ch(x)) > 196607` with `ch : Int -> Char`, and `Exists x. code(A[x])
/// > 196607` with `A : Array(Int, Char)`, are unsat; `Exists x. code(ch(x))
/// == 65` and the ground `code(A[3]) == 65` are sat. AY answered both E1 and
/// E2 sat (the ground range axiom never reached the bound occurrence). The
/// guards are quantified (design §2.10 rule 1). The engine cannot certify
/// `sat` beside them (7c46d84d85 answered the two sat goals `unknown`:
/// "incomplete", "incomplete quantifier-unhandled"), so a check validates its
/// model against them instead and asserts them only in a re-check
/// (`wf_guards`): the two sat goals are `sat`, as in libz3 5.1.0.
#[test]
fn q12_char_ranged_free_symbols_are_guarded() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let char_sort = Z3_mk_char_sort(c);
        let domain = [Z3_mk_int_sort(c)];
        let ch = Z3_mk_func_decl(c, sym(c, c"ch"), 1, domain.as_ptr(), char_sort);
        let max = int(c, 196_607);
        let e1 = exists_int(c, c"ex1", |x| {
            Z3_mk_gt(
                c,
                Z3_mk_char_to_int(c, Z3_mk_app(c, ch, 1, [x].as_ptr())),
                max,
            )
        });
        assert_ne!(check_one(c, e1), Z3_L_TRUE, "E1: z3 unsat");
        let ok = exists_int(c, c"ex2", |x| {
            Z3_mk_eq(
                c,
                Z3_mk_char_to_int(c, Z3_mk_app(c, ch, 1, [x].as_ptr())),
                int(c, 65),
            )
        });
        assert_eq!(check_one(c, ok), Z3_L_TRUE, "z3: sat");

        let array_sort = Z3_mk_array_sort(c, Z3_mk_int_sort(c), char_sort);
        let a = Z3_mk_const(c, sym(c, c"A"), array_sort);
        let e2 = exists_int(c, c"ex3", |x| {
            Z3_mk_gt(c, Z3_mk_char_to_int(c, Z3_mk_select(c, a, x)), max)
        });
        assert_ne!(check_one(c, e2), Z3_L_TRUE, "E2: z3 unsat");

        // The array guard reaches quantifier-free goals too (see
        // `q12_guards_reach_substituted_ground_terms`).
        let ground = Z3_mk_eq(
            c,
            Z3_mk_char_to_int(c, Z3_mk_select(c, a, int(c, 3))),
            int(c, 65),
        );
        assert_eq!(check_one(c, ground), Z3_L_TRUE, "z3: sat");
        // A quantifier-free goal over a `Char`-ranged function stays decided
        // under its guard (libz3 5.1.0, ypins.py q12_ground_char_fun_sat).
        let ground_fun = Z3_mk_eq(
            c,
            Z3_mk_char_to_int(c, Z3_mk_app(c, ch, 1, [int(c, 3)].as_ptr())),
            int(c, 65),
        );
        assert_eq!(check_one(c, ground_fun), Z3_L_TRUE);
        // A guard reaches only the goals that mention its symbol.
        let plain = Z3_mk_gt(c, int_const(c, c"z"), int(c, 3));
        assert_eq!(check_one(c, plain), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q12_binder_array_char_rng): `Exists b : Array(Int,
/// Char). code(b[0]) > 196607` is unsat; AY answered sat. A binder whose sort
/// holds a Char below the top level is now refused (unknown).
#[test]
fn q12_lossy_binder_sorts_are_refused() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let array_sort = Z3_mk_array_sort(c, Z3_mk_int_sort(c), Z3_mk_char_sort(c));
        let b = Z3_mk_const(c, sym(c, c"b"), array_sort);
        let body = Z3_mk_gt(
            c,
            Z3_mk_char_to_int(c, Z3_mk_select(c, b, int(c, 0))),
            int(c, 196_607),
        );
        let q = Z3_mk_exists_const(c, 0, 1, [b].as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, q);
        assert_eq!(Z3_solver_check(c, s), Z3_L_UNDEF);
        assert!(text(Z3_solver_get_reason_unknown(c, s)).contains("Char"));
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q12_j7 E3, fdprobe.py): z3's own SMT kernel answers
/// `Exists x. fs(x) ∉ {0, 1, 2}` over `FiniteDomainSort('S', 3)` `sat` with
/// `fs = [else -> 0]`, a model its own evaluator rejects (the formula
/// evaluates to False), and answers a ground `c ∉ {0, 1, 2}` `sat` with
/// `c = 0` the same way. AY answered `sat` with `fs(5) = 3`. The
/// finite-domain-ranged function is guarded like a `Char`-ranged one, so the
/// answer is never `sat` (AY's ground finite-domain range axioms already
/// answer the ground form `unsat`).
#[test]
fn q12_finite_domain_ranged_function_is_guarded() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let fd = Z3_mk_finite_domain_sort(c, sym(c, c"S"), 3);
        let domain = [Z3_mk_int_sort(c)];
        let fs = Z3_mk_func_decl(c, sym(c, c"fs"), 1, domain.as_ptr(), fd);
        let values: Vec<Z3_ast> = [c"0", c"1", c"2"]
            .iter()
            .map(|v| Z3_mk_numeral(c, v.as_ptr(), fd))
            .collect();
        let e3 = exists_int(c, c"fx", |x| {
            let app = Z3_mk_app(c, fs, 1, [x].as_ptr());
            let differs: Vec<Z3_ast> = values
                .iter()
                .map(|&v| Z3_mk_not(c, Z3_mk_eq(c, app, v)))
                .collect();
            Z3_mk_and(c, 3, differs.as_ptr())
        });
        assert_ne!(check_one(c, e3), Z3_L_TRUE, "fs ranges over three values");
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q12_fresh_char_fun): a fresh function
/// `Int -> Char` is free like any other: `Exists x. code(f(x)) > 196607` is
/// unsat and `code(f(x)) == 66` sat. AY answered the first `sat`
/// (`f!4 = [else -> 196608]`): `Z3_mk_fresh_func_decl` registered no guard.
/// The second is `sat` with a model that satisfies the guard (7c46d84d85,
/// which asserted the guard up front: `unknown`).
#[test]
fn q12_fresh_char_ranged_function_is_guarded() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let domain = [Z3_mk_int_sort(c)];
        let fresh = Z3_mk_fresh_func_decl(c, c"f".as_ptr(), 1, domain.as_ptr(), Z3_mk_char_sort(c));
        assert!(!fresh.is_null());
        let code_of = |x: Z3_ast| Z3_mk_char_to_int(c, Z3_mk_app(c, fresh, 1, [x].as_ptr()));
        let out_of_range = exists_int(c, c"fx1", |x| Z3_mk_gt(c, code_of(x), int(c, 196_607)));
        assert_ne!(check_one(c, out_of_range), Z3_L_TRUE, "z3: unsat");
        let in_range = exists_int(c, c"fx2", |x| Z3_mk_eq(c, code_of(x), int(c, 66)));
        assert_eq!(check_one(c, in_range), Z3_L_TRUE, "z3: sat");
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q12_substitute_ground): `Z3_substitute` of `x := 3`
/// into `code(ch(x)) > 196607` and `code(A[x]) > 196607` gives ground goals
/// that are unsat. `Z3_substitute` builds `ch(3)` and `A[3]` without the
/// range axiom an API-built `Char` term carries, and AY answered both `sat`
/// (`A = Store(K(0), 3, 196608)`). The guards of `ch` and `A` reach
/// quantifier-free goals as well.
#[test]
fn q12_guards_reach_substituted_ground_terms() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let char_sort = Z3_mk_char_sort(c);
        let domain = [Z3_mk_int_sort(c)];
        let ch = Z3_mk_func_decl(c, sym(c, c"chs"), 1, domain.as_ptr(), char_sort);
        let a = Z3_mk_const(
            c,
            sym(c, c"As"),
            Z3_mk_array_sort(c, Z3_mk_int_sort(c), char_sort),
        );
        let x = int_const(c, c"sx");
        let three = int(c, 3);
        let max = int(c, 196_607);
        let over_ch = Z3_mk_gt(
            c,
            Z3_mk_char_to_int(c, Z3_mk_app(c, ch, 1, [x].as_ptr())),
            max,
        );
        let over_a = Z3_mk_gt(c, Z3_mk_char_to_int(c, Z3_mk_select(c, a, x)), max);
        for formula in [over_ch, over_a] {
            let ground = Z3_substitute(c, formula, 1, [x].as_ptr(), [three].as_ptr());
            assert_ne!(ground, 0, "substitute built a term");
            assert_ne!(check_one(c, ground), Z3_L_TRUE, "z3: unsat");
        }
        Z3_del_context(c);
    }
}
