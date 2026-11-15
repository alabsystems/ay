// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the T5 design's P0.2 quarantine, implementer X
//! (`~/ay-bench/campaign/2026-10-02-T5-DESIGN.md` §4 P0.2), items Q3
//! (`Z3_substitute` and `Z3_update_term` over binders) and Q4 (`Z3_mk_app`
//! never panics; mixed Int/Real arithmetic gets z3's `to_real`).
//!
//! Each test pins libz3 5.1.0's measured answer or a fail-closed error. The
//! measurements are the z3py probes `q1_pins.py`, `q3_pins.py`, `q4_pins.py`
//! and `extra_pins.py` (`~/ay-bench/campaign/t5design-probes/t5x/`, with their
//! `*.real.out` from z3-solver 5.1.0.0 via that directory's `run.py`), and the
//! design's own probes (`p1_db.py`, `p3_leak.py`, `p8_lsubst.py`,
//! `p9_update.py`, `judge_sound/j6.py`, `judge_fid/f1.py`).

use std::ffi::c_uint;
use std::ptr;

use super::t5x_quarantine_support::*;

// ---------------------------------------------------------------------------
// Q3: substitution and update over binders
// ---------------------------------------------------------------------------

/// A `from` that the input binds (`q3_pins.py` 1, 7): z3 leaves bound
/// occurrences alone (`And(ForAll x. x > 0, 5 > 3)`); AY rewrote them
/// (`ForAll x. True`). Refused.
#[test]
fn q3_substitute_refuses_a_bound_pattern() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = konst(c, c"x", int_sort);
        let q = Z3_mk_forall_const(
            c,
            0,
            1,
            &raw const x,
            0,
            ptr::null(),
            Z3_mk_gt(c, x, int(c, 0)),
        );
        let target = Z3_mk_and(c, 2, [q, Z3_mk_gt(c, x, int(c, 3))].as_ptr());
        let (r, code) = subst(c, target, &[x], &[int(c, 5)]);
        assert_eq!((r, code), (0, Z3_INVALID_ARG));
        assert!(
            error_text(c).contains("which the input binds"),
            "{}",
            error_text(c)
        );
        Z3_del_context(c);
    }
}

/// A `to` that mentions a variable the input binds would be captured
/// (`q3_pins.py` 2-3, p3 E2): z3's `substitute(Exists x. x != z, z -> x)` is
/// sat; AY built `exists x. false` and answered UNSAT. Refused, also for
/// `z -> x + 1`.
#[test]
fn q3_substitute_refuses_capture_by_a_replacement() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, z) = (konst(c, c"x", int_sort), konst(c, c"z", int_sort));
        let e = Z3_mk_exists_const(
            c,
            0,
            1,
            &raw const x,
            0,
            ptr::null(),
            not(c, Z3_mk_eq(c, x, z)),
        );
        assert_eq!(subst(c, e, &[z], &[x]), (0, Z3_INVALID_ARG));
        let x_plus_1 = add(c, &[x, int(c, 1)]);
        assert_eq!(subst(c, e, &[z], &[x_plus_1]), (0, Z3_INVALID_ARG));
        Z3_del_context(c);
    }
}

/// A lambda's parameter is a binder (`q3_pins.py` 4, 6; p8): z3 leaves
/// `Lambda x. x + 1` unchanged under `x -> 3` and `x + 1 -> 5`; AY built
/// `lambda-array(3, 4)` (and `Select(.., 10) != 11` sat) and `lambda x. 5`.
/// Refused.
#[test]
fn q3_substitute_refuses_a_lambda_parameter() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = konst(c, c"x", int_sort);
        let x_plus_1 = add(c, &[x, int(c, 1)]);
        let lambda = Z3_mk_lambda_const(c, 1, &raw const x, x_plus_1);
        assert_ne!(lambda, 0, "{}", error_text(c));
        assert_eq!(subst(c, lambda, &[x], &[int(c, 3)]), (0, Z3_INVALID_ARG));
        assert_eq!(
            subst(c, lambda, &[x_plus_1], &[int(c, 5)]),
            (0, Z3_INVALID_ARG)
        );
        Z3_del_context(c);
    }
}

/// A free constant beside a binder still substitutes (`q3_pins.py` 5): z3's
/// `substitute(ForAll x. x > y, y -> 3)` is `ForAll x. x > 3`.
#[test]
fn q3_substitute_keeps_replacing_free_constants_beside_binders() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, y) = (konst(c, c"x", int_sort), konst(c, c"y", int_sort));
        let q = Z3_mk_forall_const(c, 0, 1, &raw const x, 0, ptr::null(), Z3_mk_gt(c, x, y));
        let (r, code) = subst(c, q, &[y], &[int(c, 3)]);
        assert_eq!(code, Z3_OK, "{}", error_text(c));
        assert_ne!(r, 0);
        assert_eq!(Z3_get_ast_kind(c, r), Z3_QUANTIFIER_AST);
        let shown = text(c, r);
        assert!(shown.contains('3') && !shown.contains(" y"), "{shown}");
        Z3_del_context(c);
    }
}

/// `Z3_update_term` gives a quantifier a new body in de Bruijn form
/// (`q3_pins.py` 8-9, p9): z3 binds `(:var 0)` to the quantifier's variable
/// (`update(forall k. p, [(:var 0) > 0])` is `forall k. k > 0`, unsat); AY
/// left it free and answered sat. Refused. A closed new body still updates
/// (z3: `forall k. false`, unsat; `extra_pins.py` d).
#[test]
fn q3_update_term_refuses_a_loose_quantifier_body() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let p = konst(c, c"p8", Z3_mk_bool_sort(c));
        let q = db_quantifier(c, true, &[int_sort], &[c"k"], &[], p);
        assert_ne!(q, 0, "{}", error_text(c));
        let loose = Z3_mk_gt(c, Z3_mk_bound(c, 0, int_sort), int(c, 0));
        assert_eq!(update(c, q, &[loose]), (0, Z3_INVALID_ARG));
        assert!(error_text(c).contains("(:var 0)"), "{}", error_text(c));
        let (closed, code) = update(c, q, &[Z3_mk_false(c)]);
        assert_eq!(code, Z3_OK, "{}", error_text(c));
        assert_eq!(check(c, &[closed]), Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// A lambda takes one argument, its body: z3 answers `Z3_IOB` for two
/// (`q3_pins.py` 10b), where AY rebound the lambda to the first argument.
/// One argument z3 accepts (`lambda x. x + 2`); AY cannot rebuild it yet
/// and refuses.
#[test]
fn q3_update_term_on_a_lambda_fails_closed() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, y) = (konst(c, c"x", int_sort), konst(c, c"y", int_sort));
        let lambda = Z3_mk_lambda_const(c, 1, &raw const x, add(c, &[x, int(c, 1)]));
        assert_ne!(lambda, 0, "{}", error_text(c));
        assert_eq!(
            update(c, lambda, &[y, add(c, &[y, int(c, 2)])]),
            (0, Z3_IOB)
        );
        let body = add(c, &[Z3_mk_bound(c, 0, int_sort), int(c, 2)]);
        assert_eq!(update(c, lambda, &[body]), (0, Z3_INVALID_ARG));
        Z3_del_context(c);
    }
}

/// `Z3_substitute_vars` must not carry a replacement under a binder of a
/// name it mentions (`q3_vars_pins.py` 7-8, libz3 5.1.0): z3's
/// `substitute_vars(Exists([x], x > Var(1)), x)` is `exists y. y > x`, sat
/// (the `forall` form unsat); AY's name binding would build `exists x. x >
/// x`, unsat. Refused. A replacement that mentions no bound name still
/// substitutes, and a call with nothing to replace returns the input.
#[test]
fn q3_substitute_vars_refuses_capture() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, z) = (konst(c, c"x", int_sort), konst(c, c"z", int_sort));
        let body = Z3_mk_gt(c, x, Z3_mk_bound(c, 1, int_sort));
        let e = Z3_mk_exists_const(c, 0, 1, &raw const x, 0, ptr::null(), body);
        assert_ne!(e, 0, "{}", error_text(c));
        let r = Z3_substitute_vars(c, e, 1, &raw const x);
        assert_eq!((r, Z3_get_error_code(c)), (0, Z3_INVALID_ARG));
        assert!(
            error_text(c).contains("which the input binds"),
            "{}",
            error_text(c)
        );
        let r = Z3_substitute_vars(c, e, 1, &raw const z);
        assert_ne!(r, 0, "{}", error_text(c));
        assert_eq!(
            check(c, &[r, Z3_mk_eq(c, z, int(c, 0))]),
            Z3_L_TRUE,
            "z3: sat"
        );
        let closed = Z3_mk_exists_const(
            c,
            0,
            1,
            &raw const x,
            0,
            ptr::null(),
            not(c, Z3_mk_eq(c, x, Z3_mk_bound(c, 0, int_sort))),
        );
        let r = Z3_substitute_vars(c, closed, 1, &raw const x);
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_text(c));
        assert!(Z3_is_eq_ast(c, r, closed), "z3: nothing to replace");
        assert_eq!(check(c, &[r]), Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// `Z3_substitute_funs` refuses a template that mentions a variable the input
/// binds (`q3_vars_pins.py` 4): z3's `substitute_funs(Exists([x], f(x) != x +
/// z), f -> Var(0) + x)` keeps the template's `x` free (sat); AY's would be
/// captured. A template over free names still expands: `f -> Var(0) + z`
/// gives z3's unsat `exists x. x + z != x + z` (4b).
#[test]
fn q3_substitute_funs_refuses_capture() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, z) = (konst(c, c"x", int_sort), konst(c, c"z", int_sort));
        let f = Z3_mk_func_decl(c, sym(c, c"fz"), 1, &raw const int_sort, int_sort);
        let fx = Z3_mk_app(c, f, 1, &raw const x);
        let body = not(c, Z3_mk_eq(c, fx, add(c, &[x, z])));
        let e = Z3_mk_exists_const(c, 0, 1, &raw const x, 0, ptr::null(), body);
        assert_ne!(e, 0, "{}", error_text(c));
        let v0 = Z3_mk_bound(c, 0, int_sort);
        let captured = add(c, &[v0, x]);
        let r = Z3_substitute_funs(c, e, 1, &raw const f, &raw const captured);
        assert_eq!((r, Z3_get_error_code(c)), (0, Z3_INVALID_ARG));
        let free = add(c, &[v0, z]);
        let r = Z3_substitute_funs(c, e, 1, &raw const f, &raw const free);
        assert_ne!(r, 0, "{}", error_text(c));
        assert_eq!(check(c, &[r]), Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

// ---------------------------------------------------------------------------
// Q4: Z3_mk_app and mixed Int/Real arithmetic
// ---------------------------------------------------------------------------

/// f1 d: z3 inserts `to_real` (`(+ (to_real dx) dy)` of sort Real,
/// `(> (to_real dx) dy)`, `(= (to_real dx) dy)`); AY panicked in
/// `add_many`. Verdicts over the coerced terms (`q4_pins.py`): `dx + dy =
/// 1/2, dx = 0, dy = 1/2` sat; `dx > dy, dy = 7/2, dx = 3` unsat; `dx = dy,
/// dy = 1/2` unsat.
#[test]
fn q4_mixed_int_real_operands_get_to_real() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, real_sort) = (Z3_mk_int_sort(c), Z3_mk_real_sort(c));
        let (dx, dy) = (konst(c, c"dx", int_sort), konst(c, c"dy", real_sort));
        let sum = add(c, &[dx, dy]);
        assert_ne!(sum, 0, "{}", error_text(c));
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, sum)), Z3_REAL_SORT);
        assert!(text(c, sum).contains("(to_real dx)"), "{}", text(c, sum));
        let gt = Z3_mk_gt(c, dx, dy);
        let eq = Z3_mk_eq(c, dx, dy);
        assert!(gt != 0 && eq != 0, "{}", error_text(c));
        assert!(text(c, gt).contains("(to_real dx)"), "{}", text(c, gt));
        assert!(text(c, eq).contains("(to_real dx)"), "{}", text(c, eq));
        let half = real(c, 1, 2);
        let sum_half = Z3_mk_eq(c, sum, half);
        let facts = [sum_half, Z3_mk_eq(c, dx, int(c, 0)), Z3_mk_eq(c, dy, half)];
        assert_eq!(check(c, &facts), Z3_L_TRUE, "z3: sat");
        let facts = [
            gt,
            Z3_mk_eq(c, dy, real(c, 7, 2)),
            Z3_mk_eq(c, dx, int(c, 3)),
        ];
        assert_eq!(check(c, &facts), Z3_L_FALSE, "z3: unsat");
        assert_eq!(
            check(c, &[eq, Z3_mk_eq(c, dy, half)]),
            Z3_L_FALSE,
            "z3: unsat"
        );
        for (label, built) in [
            ("mul", Z3_mk_mul(c, 2, [dx, dy].as_ptr())),
            ("sub", Z3_mk_sub(c, 2, [dx, dy].as_ptr())),
            ("power", Z3_mk_power(c, dx, dy)),
            (
                "ite",
                Z3_mk_ite(c, konst(c, c"fb", Z3_mk_bool_sort(c)), dx, dy),
            ),
        ] {
            assert_ne!(built, 0, "{label}: {}", error_text(c));
            assert_eq!(
                Z3_get_sort_kind(c, Z3_get_sort(c, built)),
                Z3_REAL_SORT,
                "{label}"
            );
        }
        assert_ne!(
            Z3_mk_distinct(c, 2, [dx, dy].as_ptr()),
            0,
            "{}",
            error_text(c)
        );
        for (label, built) in [
            ("lt", Z3_mk_lt(c, dy, dx)),
            ("le", Z3_mk_le(c, dx, dy)),
            ("ge", Z3_mk_ge(c, dy, dx)),
        ] {
            assert_ne!(built, 0, "{label}: {}", error_text(c));
        }
        Z3_del_context(c);
    }
}

/// z3's division follows the dividend (`q4_pins.py`, `extra_pins.py` b): a
/// Real dividend is real `/` with `(to_real d)` on an Int divisor. z3 lowers a
/// Real operand of `div`, `mod` and `rem` with the LOSSY `(to_int t)` (`(div x
/// (to_int y))`, `(mod (to_int y) (to_int y))`); AY refuses instead of
/// inserting it (base AY panicked), as `solver_model_fuzz_tests` pins for
/// `mod`.
#[test]
fn q4_division_by_sort_and_no_lossy_to_int() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, real_sort) = (Z3_mk_int_sort(c), Z3_mk_real_sort(c));
        let (x, y) = (konst(c, c"mx", int_sort), konst(c, c"my", real_sort));
        let half = Z3_mk_div(c, y, int(c, 2));
        assert_ne!(half, 0, "{}", error_text(c));
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, half)), Z3_REAL_SORT);
        let at = Z3_mk_eq(c, y, int_real(c, 7));
        assert_eq!(check(c, &[at, Z3_mk_eq(c, half, real(c, 7, 2))]), Z3_L_TRUE);
        assert_eq!(
            check(c, &[at, Z3_mk_eq(c, half, real(c, 3, 1))]),
            Z3_L_FALSE
        );
        let int_div = Z3_mk_div(c, x, int(c, 2));
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, int_div)), Z3_INT_SORT);
        for (label, built) in [
            ("div", Z3_mk_div(c, x, y)),
            ("mod", Z3_mk_mod(c, x, y)),
            ("rem", Z3_mk_rem(c, y, x)),
        ] {
            assert_eq!(built, 0, "{label}");
            assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR, "{label}");
            assert!(
                error_text(c).contains("to_int"),
                "{label}: {}",
                error_text(c)
            );
        }
        Z3_del_context(c);
    }
}

/// A non-arithmetic operand of an arithmetic operator is a sort error, never
/// a panic (`q4_pins.py`): z3 refuses bit-vector, finite-domain and Char
/// operands ("Sort mismatch"); AY panicked on bit-vectors and built a
/// finite-domain-sorted sum. z3 coerces a Bool operand to `(ite b 1 0)`; AY
/// refuses it. Comparisons keep AY's Char / finite-domain carrier extension
/// (pinned by `bounded_gap_tests` and `feasible_tier_tests`); a bit-vector or
/// Bool comparison is a sort error.
#[test]
fn q4_non_arithmetic_operands_are_sort_errors() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let bv = konst(c, c"qbv", Z3_mk_bv_sort(c, 8));
        let fd_sort = Z3_mk_finite_domain_sort(c, sym(c, c"QF"), 5);
        let fd = konst(c, c"qfd", fd_sort);
        let ch = konst(c, c"qch", Z3_mk_char_sort(c));
        let b = konst(c, c"qb", Z3_mk_bool_sort(c));
        let x = konst(c, c"qx", Z3_mk_int_sort(c));
        for operand in [bv, fd, ch, b] {
            let shown = text(c, operand);
            for (label, built) in [
                ("add", add(c, &[operand, operand])),
                ("mul", Z3_mk_mul(c, 2, [operand, operand].as_ptr())),
                ("sub", Z3_mk_sub(c, 2, [operand, operand].as_ptr())),
                ("neg", Z3_mk_unary_minus(c, operand)),
                ("abs", Z3_mk_abs(c, operand)),
                ("div", Z3_mk_div(c, x, operand)),
                ("mod", Z3_mk_mod(c, operand, x)),
                ("power", Z3_mk_power(c, operand, x)),
            ] {
                assert_eq!(built, 0, "{label} over {shown}");
                assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR, "{label} over {shown}");
                assert!(
                    !error_text(c).contains("panic"),
                    "{label}: {}",
                    error_text(c)
                );
            }
        }
        for operand in [bv, b] {
            for built in [Z3_mk_lt(c, operand, operand), Z3_mk_ge(c, operand, x)] {
                assert_eq!(built, 0, "{}", text(c, operand));
                assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
            }
        }
        for operand in [fd, ch] {
            assert_ne!(Z3_mk_lt(c, operand, x), 0, "{}", error_text(c));
        }
        Z3_del_context(c);
    }
}

/// Building a finite-domain sum installed the range axiom of its (FD) result
/// sort for the whole context, so `fx = 2, fy = 2` over a 3-element domain
/// was answered UNSAT once `fx + fy` had merely been built; z3 refuses the
/// sum and answers sat (`fd_sum_pin.py`, measured: base AY unsat).
#[test]
fn q4_a_refused_finite_domain_sum_constrains_nothing() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let fd_sort = Z3_mk_finite_domain_sort(c, sym(c, c"FS3"), 3);
        let (fx, fy) = (konst(c, c"fx", fd_sort), konst(c, c"fy", fd_sort));
        assert_eq!(add(c, &[fx, fy]), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        let two = Z3_mk_int64(c, 2, fd_sort);
        let facts = [Z3_mk_eq(c, fx, two), Z3_mk_eq(c, fy, two)];
        assert_eq!(check(c, &facts), Z3_L_TRUE, "z3: sat");
        Z3_del_context(c);
    }
}

/// `Z3_mk_sub` over one argument is that argument (`judge_fid/f1.py` i:
/// `sub1.eq(x)` is True); AY returned null without an error.
#[test]
fn q4_sub_of_one_argument_is_the_argument() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let x = konst(c, c"sx", Z3_mk_int_sort(c));
        let one = Z3_mk_sub(c, 1, &raw const x);
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_text(c));
        assert!(Z3_is_eq_ast(c, one, x));
        Z3_del_context(c);
    }
}

/// `Z3_mk_app` never panics (p1(h), `q4_pins.py`): the decl of a literal
/// applied to nothing is that literal (z3: `3`); a builtin operator's decl,
/// which z3 applies (`(+ hx 2)`), is an error in AY until T5 gives builtin
/// decls public identities.
#[test]
fn q4_mk_app_on_value_and_builtin_decls_never_panics() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let three = int(c, 3);
        let value_decl = Z3_get_app_decl(c, Z3_to_app(c, three));
        let applied = Z3_mk_app(c, value_decl, 0, ptr::null());
        assert!(
            applied != 0 && Z3_is_eq_ast(c, applied, three),
            "{}",
            error_text(c)
        );
        let (hx, hy) = (konst(c, c"hx", int_sort), konst(c, c"hy", int_sort));
        for built in [
            add(c, &[hx, hy]),
            Z3_mk_mul(c, 2, [hx, hy].as_ptr()),
            Z3_mk_lt(c, hx, hy),
            Z3_mk_select(
                c,
                konst(c, c"hA", Z3_mk_array_sort(c, int_sort, int_sort)),
                hx,
            ),
        ] {
            let decl = Z3_get_app_decl(c, Z3_to_app(c, built));
            assert!(!decl.is_null(), "{}", error_text(c));
            let args = [hx, int(c, 2)];
            let arity = Z3_get_arity(c, decl) as usize;
            let r = Z3_mk_app(c, decl, arity as c_uint, args.as_ptr());
            if r == 0 {
                assert_ne!(Z3_get_error_code(c), Z3_OK);
                assert!(!error_text(c).contains("panic"), "{}", error_text(c));
            }
        }
        Z3_del_context(c);
    }
}
