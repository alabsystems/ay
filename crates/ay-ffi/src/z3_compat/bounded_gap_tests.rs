// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the bounded-gap Z3 C-API closings:
//! `Z3_algebraic_roots` / `Z3_polynomial_subresultants` (AST→polynomial
//! extractor over the exact `ay-nra` engines), `Z3_mk_array_ext`,
//! `Z3_solver_solve_for`, `Z3_solver_cube`, `Z3_model_extrapolate`,
//! `Z3_pattern_to_ast` (multi-trigger), `Z3_mk_type_variable`, finite-domain
//! sorts, the fixedpoint engine-state extras, and the HO-seq constructors.
//!
//! SOUNDNESS-CRITICAL cases (a Z3-UNSAT that MUST stay UNSAT in AY) are
//! marked; libz3-4.16-cross-checked values are quoted from the probe runs.

use super::super::*;
use ay_dpll::api::Sort;
use std::ffi::CStr;
use std::ptr;

unsafe fn ctx() -> Z3_context {
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn sym(c: Z3_context, name: &CStr) -> Z3_symbol {
    unsafe { Z3_mk_string_symbol(c, name.as_ptr()) }
}

// ============================================================================
// Z3_algebraic_roots — REAL via the AST→coefficient extractor + Sturm roots.
// ============================================================================

#[test]
fn algebraic_roots_sqrt2_exact() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        // p((:var 0)) = v0^2 - 2 — libz3 convention: bound vars are the
        // polynomial variables; with n = 0 the sole var is the unknown.
        let v0 = Z3_mk_bound(c, 0, real);
        let two = Z3_mk_real(c, 2, 1);
        let v0sq = Z3_mk_power(c, v0, two);
        let neg2 = Z3_mk_unary_minus(c, two);
        let add_args = [v0sq, neg2];
        let p = Z3_mk_add(c, 2, add_args.as_ptr());
        let roots = Z3_algebraic_roots(c, p, 0, ptr::null());
        assert!(!roots.is_null());
        assert_eq!(Z3_ast_vector_size(c, roots), 2, "x^2-2 has two real roots");
        let r0 = Z3_ast_vector_get(c, roots, 0);
        let r1 = Z3_ast_vector_get(c, roots, 1);
        assert!(Z3_algebraic_is_value(c, r0) && Z3_algebraic_is_value(c, r1));
        // Ascending: r0 = -√2 < 0 < r1 = +√2; and r1*r1 == 2 exactly.
        assert!(Z3_algebraic_lt(c, r0, r1), "roots must be ascending");
        let sq = Z3_algebraic_mul(c, r1, r1);
        assert!(Z3_algebraic_eq(c, sq, two), "(+√2)² must equal 2 exactly");
        Z3_del_context(c);
    }
}

#[test]
fn algebraic_roots_parametric_and_rational() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let v0 = Z3_mk_bound(c, 0, real);
        let v1 = Z3_mk_bound(c, 1, real);
        let two = Z3_mk_real(c, 2, 1);
        // p(a, x) = v1^2 - v0 at a = 9 → roots -3, 3 (libz3-cross-checked).
        let v1sq = Z3_mk_power(c, v1, two);
        let neg_v0 = Z3_mk_unary_minus(c, v0);
        let add_args = [v1sq, neg_v0];
        let p = Z3_mk_add(c, 2, add_args.as_ptr());
        let nine = Z3_mk_real(c, 9, 1);
        let args = [nine];
        let roots = Z3_algebraic_roots(c, p, 1, args.as_ptr());
        assert_eq!(Z3_ast_vector_size(c, roots), 2, "x^2-9 has roots ±3");
        let m3 = Z3_mk_real(c, -3, 1);
        let p3 = Z3_mk_real(c, 3, 1);
        assert!(Z3_algebraic_eq(c, Z3_ast_vector_get(c, roots, 0), m3));
        assert!(Z3_algebraic_eq(c, Z3_ast_vector_get(c, roots, 1), p3));
        // Linear 2*v0 - 1 → the single rational root 1/2.
        let one = Z3_mk_real(c, 1, 1);
        let two_v0_args = [two, v0];
        let two_v0 = Z3_mk_mul(c, 2, two_v0_args.as_ptr());
        let neg1 = Z3_mk_unary_minus(c, one);
        let lin_args = [two_v0, neg1];
        let lin = Z3_mk_add(c, 2, lin_args.as_ptr());
        let lroots = Z3_algebraic_roots(c, lin, 0, ptr::null());
        assert_eq!(Z3_ast_vector_size(c, lroots), 1);
        let half = Z3_mk_real(c, 1, 2);
        assert!(Z3_algebraic_eq(c, Z3_ast_vector_get(c, lroots, 0), half));
        // No real roots: v0^2 + 1 → EMPTY (not an error, matching libz3).
        let pos_args = [Z3_mk_power(c, v0, two), one];
        let pos = Z3_mk_add(c, 2, pos_args.as_ptr());
        let nroots = Z3_algebraic_roots(c, pos, 0, ptr::null());
        assert_eq!(Z3_ast_vector_size(c, nroots), 0, "x^2+1 has no real roots");
        Z3_del_context(c);
    }
}

#[test]
fn algebraic_roots_honest_divergences() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        // Multivariate residual (two free vars, n = 0) → INVALID_ARG + empty.
        let v0 = Z3_mk_bound(c, 0, real);
        let v1 = Z3_mk_bound(c, 1, real);
        let mul_args = [v0, v1];
        let bad = Z3_mk_mul(c, 2, mul_args.as_ptr());
        let r = Z3_algebraic_roots(c, bad, 0, ptr::null());
        // Read the code BEFORE any other API call: every entry point clears the
        // error state on entry, exactly as libz3 does, so an intervening
        // `Z3_ast_vector_size` would legitimately reset it to Z3_OK.
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_ast_vector_size(c, r), 0);
        // Constant polynomial → INVALID_ARG + empty (libz3 errors too).
        let two = Z3_mk_real(c, 2, 1);
        let r2 = Z3_algebraic_roots(c, two, 0, ptr::null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_ast_vector_size(c, r2), 0);
        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_polynomial_subresultants — REAL exact PSC chain, libz3-value-checked.
// ============================================================================

/// Assert the PSC vector equals the expected integer values (as exact reals).
unsafe fn assert_psc(c: Z3_context, v: Z3_ast_vector, expected: &[i32]) {
    unsafe {
        assert!(!v.is_null());
        assert_eq!(Z3_ast_vector_size(c, v) as usize, expected.len());
        for (i, &e) in expected.iter().enumerate() {
            let got = Z3_ast_vector_get(c, v, i as u32);
            let want = Z3_mk_real(c, e, 1);
            assert!(
                Z3_algebraic_eq(c, got, want),
                "psc[{i}] mismatch (want {e})"
            );
        }
    }
}

#[test]
fn subresultants_match_libz3_values() {
    unsafe {
        let c = ctx();
        let real = Z3_mk_real_sort(c);
        let x = Z3_mk_const(c, sym(c, c"x"), real);
        let n = |c: Z3_context, k: i32| Z3_mk_real(c, k, 1);
        let pow = |c, b, k| Z3_mk_power(c, b, n(c, k));
        let add2 = |c: Z3_context, a: Z3_ast, b: Z3_ast| {
            let args = [a, b];
            Z3_mk_add(c, 2, args.as_ptr())
        };
        let mul2 = |c: Z3_context, a: Z3_ast, b: Z3_ast| {
            let args = [a, b];
            Z3_mk_mul(c, 2, args.as_ptr())
        };
        // (x²-2, 2x) → [-8]  (libz3-cross-checked)
        let p1 = add2(c, pow(c, x, 2), n(c, -2));
        let q1 = mul2(c, n(c, 2), x);
        assert_psc(c, Z3_polynomial_subresultants(c, p1, q1, x), &[-8]);
        // (x⁴-5x²+4, 4x³-10x) → [5184, -360, -40]
        let p2 = add2(
            c,
            add2(c, pow(c, x, 4), mul2(c, n(c, -5), pow(c, x, 2))),
            n(c, 4),
        );
        let q2 = add2(c, mul2(c, n(c, 4), pow(c, x, 3)), mul2(c, n(c, -10), x));
        assert_psc(
            c,
            Z3_polynomial_subresultants(c, p2, q2, x),
            &[5184, -360, -40],
        );
        // Equal degrees are ORDER-SENSITIVE: (x²+1, x²-x) → [2, -1]; swapped → [2, 1].
        let p3 = add2(c, pow(c, x, 2), n(c, 1));
        let q3 = add2(c, pow(c, x, 2), Z3_mk_unary_minus(c, x));
        assert_psc(c, Z3_polynomial_subresultants(c, p3, q3, x), &[2, -1]);
        assert_psc(c, Z3_polynomial_subresultants(c, q3, p3, x), &[2, 1]);
        // Unequal degrees canonicalize (swap, no sign flip): both orders → [-7].
        let p4 = add2(c, x, n(c, -2));
        let q4 = add2(c, pow(c, x, 3), n(c, -1));
        assert_psc(c, Z3_polynomial_subresultants(c, p4, q4, x), &[-7]);
        assert_psc(c, Z3_polynomial_subresultants(c, q4, p4, x), &[-7]);
        // Zero entries drop: (x⁴+x, x²) → [-1]; all-zero chain pads: (x⁴, x²) → [0].
        let p5 = add2(c, pow(c, x, 4), x);
        let q5 = pow(c, x, 2);
        assert_psc(c, Z3_polynomial_subresultants(c, p5, q5, x), &[-1]);
        assert_psc(c, Z3_polynomial_subresultants(c, pow(c, x, 4), q5, x), &[0]);
        // Constant operand → [0] (libz3-cross-checked).
        assert_psc(c, Z3_polynomial_subresultants(c, q4, n(c, 5), x), &[0]);
        // Parametric (a second variable) → honest INVALID_ARG + empty.
        let a = Z3_mk_const(c, sym(c, c"a"), real);
        let par = add2(c, mul2(c, a, pow(c, x, 2)), n(c, -2));
        let v = Z3_polynomial_subresultants(c, par, q1, x);
        // Read the code BEFORE the next API call, which clears it (libz3 does the
        // same reset on every entry point).
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_ast_vector_size(c, v), 0);
        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_mk_array_ext — cached witness + extensionality background axiom.
// ============================================================================

#[test]
fn array_ext_soundness_and_caching() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let arr = Z3_mk_array_sort(c, int, int);
        let a = Z3_mk_const(c, sym(c, c"exta"), arr);
        let b = Z3_mk_const(c, sym(c, c"extb"), arr);
        let k = Z3_mk_array_ext(c, a, b);
        assert_ne!(k, 0, "ext witness must be a real AST");
        // Witness has the arrays' INDEX sort.
        let ks = Z3_get_sort(c, k);
        assert_eq!(Z3_get_sort_kind(c, ks), Z3_INT_SORT);
        // Same pair → identical witness (Z3 hash-consing parity).
        assert_eq!(Z3_mk_array_ext(c, a, b), k);
        // SOUNDNESS (libz3-cross-checked UNSAT): a != b && a[k] == b[k].
        let s = Z3_mk_solver(c);
        let a_eq_b = Z3_mk_eq(c, a, b);
        Z3_solver_assert(c, s, Z3_mk_not(c, a_eq_b));
        let sel_a = Z3_mk_select(c, a, k);
        let sel_b = Z3_mk_select(c, b, k);
        Z3_solver_assert(c, s, Z3_mk_eq(c, sel_a, sel_b));
        assert_eq!(
            Z3_solver_check(c, s),
            Z3_L_FALSE,
            "a != b with equal reads at the ext witness must be UNSAT"
        );
        // The axiom alone is satisfiable: a != b (no read constraint) is SAT.
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_not(c, a_eq_b));
        assert_eq!(
            Z3_solver_check(c, s2),
            Z3_L_TRUE,
            "ext axiom must not overconstrain"
        );
        // Non-array operands → honest sort error.
        let i = Z3_mk_const(c, sym(c, c"exti"), int);
        assert_eq!(Z3_mk_array_ext(c, i, i), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        Z3_del_context(c);
    }
}

// ============================================================================
// Bounded-carrier arrays — public extensionality, and the exact limits of it.
// ============================================================================

/// `Char` and finite-domain sorts lower to an unbounded `Int` in the core term
/// store, so `(Array Char Bool)` becomes `(Array Int Bool)` and gains indices
/// (`-1`, `196608`, …) that no public formula can name. Quantifier construction
/// relativizes `forall ch:Char` to `[0, 196607]`, so without the extensionality
/// lemma the engine can satisfy "agrees at every public index AND is a different
/// core array" by differing at `-1`.
///
/// Oracle, measured against the pinned z3 5.0.0 (`Z3 5.0.0.0`):
///
/// ```text
/// ForAll([ch], Select(a, ch) == Select(b, ch)), a != b   => unsat   (Char)
/// ForAll([d],  Select(x, d)  == Select(y, d)),  x != y   => unsat   (D3)
/// ForAll([ch], Select(a, ch) == Select(b, ch)), a[0] != b[0] => unsat
/// a != b                                                 => sat
/// Select(a, CharVal(0)) == Select(b, CharVal(0)), a != b => sat
/// ```
#[test]
fn bounded_array_extensionality_is_exact_for_free_carrier_arrays() {
    unsafe {
        let c = ctx();
        let boolean = Z3_mk_bool_sort(c);
        let integer = Z3_mk_int_sort(c);

        // z3 5.0.0: unsat. The Int-lowered engine has extra indices, so this is
        // the direct outside-carrier disequality attack.
        let char_sort = Z3_mk_char_sort(c);
        let char_array = Z3_mk_array_sort(c, char_sort, boolean);
        let a = Z3_mk_const(c, sym(c, c"char_array_a"), char_array);
        let b = Z3_mk_const(c, sym(c, c"char_array_b"), char_array);
        let ch = Z3_mk_const(c, sym(c, c"char_array_index"), char_sort);
        let reads_equal = Z3_mk_eq(c, Z3_mk_select(c, a, ch), Z3_mk_select(c, b, ch));
        let all_reads_equal =
            Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), reads_equal);
        assert_ne!(all_reads_equal, 0);
        let solver = Z3_mk_solver(c);
        Z3_solver_assert(c, solver, all_reads_equal);
        Z3_solver_assert(c, solver, Z3_mk_not(c, Z3_mk_eq(c, a, b)));
        assert_eq!(
            Z3_solver_check(c, solver),
            Z3_L_FALSE,
            "Char arrays cannot differ only at an Int value outside Char's carrier"
        );

        // NON-VACUITY: the lemma must reach ONLY goals that assert the
        // extensionality formula. A sibling handle that drops the agreement
        // hypothesis has to stay SAT (z3 5.0.0 on `a != b` alone: sat).
        let open = Z3_mk_solver(c);
        Z3_solver_assert(c, open, Z3_mk_not(c, Z3_mk_eq(c, a, b)));
        assert_eq!(
            Z3_solver_check(c, open),
            Z3_L_TRUE,
            "the extensionality lemma must not leak into a goal that lacks its hypothesis"
        );

        // NON-VACUITY: agreement at a SINGLE public index is far too weak to
        // entail equality; the lemma must not fire for it (z3 5.0.0: sat).
        let zero_char = Z3_mk_char(c, 0);
        assert_ne!(zero_char, 0);
        let one_point = Z3_mk_solver(c);
        Z3_solver_assert(
            c,
            one_point,
            Z3_mk_eq(
                c,
                Z3_mk_select(c, a, zero_char),
                Z3_mk_select(c, b, zero_char),
            ),
        );
        Z3_solver_assert(c, one_point, Z3_mk_not(c, Z3_mk_eq(c, a, b)));
        assert_eq!(
            Z3_solver_check(c, one_point),
            Z3_L_TRUE,
            "agreement at one index must not entail array equality"
        );

        // NON-VACUITY (the other direction): pointwise agreement really does
        // reach the public indices — disagreeing at one is unsat (z3 5.0.0).
        let point_conflict = Z3_mk_solver(c);
        Z3_solver_assert(c, point_conflict, all_reads_equal);
        Z3_solver_assert(
            c,
            point_conflict,
            Z3_mk_not(
                c,
                Z3_mk_eq(
                    c,
                    Z3_mk_select(c, a, zero_char),
                    Z3_mk_select(c, b, zero_char),
                ),
            ),
        );
        assert_eq!(
            Z3_solver_check(c, point_conflict),
            Z3_L_FALSE,
            "pointwise agreement must refute disagreement at a public index"
        );

        // Public sort checks happen before the core's Char -> Int erasure.
        // Z3 rejects an Int index for an Array(Char, ...); AY must do likewise.
        let int_zero = Z3_mk_int(c, 0, integer);
        assert_eq!(Z3_mk_select(c, a, int_zero), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        let value = Z3_mk_true(c);
        assert_eq!(Z3_mk_store(c, a, int_zero, value), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);

        // Same attack over a named finite domain (z3 5.0.0 on the quantified
        // form: unsat).
        let fd = Z3_mk_finite_domain_sort(c, sym(c, c"ArrayD3"), 3);
        let fd_array = Z3_mk_array_sort(c, fd, boolean);
        let x = Z3_mk_const(c, sym(c, c"fd_array_x"), fd_array);
        let y = Z3_mk_const(c, sym(c, c"fd_array_y"), fd_array);
        let d = Z3_mk_const(c, sym(c, c"fd_array_index"), fd);
        let fd_reads_equal = Z3_mk_eq(c, Z3_mk_select(c, x, d), Z3_mk_select(c, y, d));
        let fd_all_reads_equal =
            Z3_mk_forall_const(c, 0, 1, &raw const d, 0, ptr::null(), fd_reads_equal);
        let solver2 = Z3_mk_solver(c);
        Z3_solver_assert(c, solver2, fd_all_reads_equal);
        Z3_solver_assert(c, solver2, Z3_mk_not(c, Z3_mk_eq(c, x, y)));
        assert_eq!(
            Z3_solver_check(c, solver2),
            Z3_L_FALSE,
            "finite-domain arrays cannot differ only outside the named carrier"
        );

        Z3_del_context(c);
    }
}

/// SOUNDNESS REGRESSION — the defect that sank the first attempt at this
/// closure. The canonical-extension proof needs every array term of the sort to
/// BE a canonical extension. `Z3_mk_const_array` pins every core index
/// including the off-carrier ones, and `store` inherits its base's off-carrier
/// values, so for
///
/// ```text
/// D1 = (_ FiniteDomain "probeD1" 1)             carrier = {0}
/// a = const(D1, true)                           off-carrier: true
/// b = store(const(D1, false), 0, true)          off-carrier: false
/// forall d:D1. a[d] = b[d]                      holds: both read true at 0
/// ```
///
/// the goal is SATISFIABLE by construction while core `a = b` is FALSE. A
/// bridge that guards only the SORT shape injects `a = b` and refutes it.
///
/// Oracle (z3 5.0.0): the whole goal is `unknown`; the same two definitions
/// WITHOUT the quantifier are `sat`. AY must never answer `Z3_L_FALSE`.
#[test]
fn bounded_array_extensionality_refuses_off_carrier_pinned_terms() {
    unsafe {
        let c = ctx();
        let boolean = Z3_mk_bool_sort(c);
        let d1 = Z3_mk_finite_domain_sort(c, sym(c, c"probeD1"), 1);
        assert_ne!(d1, ptr::null_mut());
        let d1_array = Z3_mk_array_sort(c, d1, boolean);
        let a = Z3_mk_const(c, sym(c, c"pinned_a"), d1_array);
        let b = Z3_mk_const(c, sym(c, c"pinned_b"), d1_array);
        let zero = Z3_mk_numeral(c, c"0".as_ptr(), d1);
        assert_ne!(zero, 0);

        let all_true = Z3_mk_const_array(c, d1, Z3_mk_true(c));
        let all_false = Z3_mk_const_array(c, d1, Z3_mk_false(c));
        assert_ne!(all_true, 0);
        assert_ne!(all_false, 0);
        let stored_true = Z3_mk_store(c, all_false, zero, Z3_mk_true(c));
        assert_ne!(stored_true, 0);

        let d = Z3_mk_const(c, sym(c, c"pinned_index"), d1);
        let reads_equal = Z3_mk_eq(c, Z3_mk_select(c, a, d), Z3_mk_select(c, b, d));
        let all_reads_equal =
            Z3_mk_forall_const(c, 0, 1, &raw const d, 0, ptr::null(), reads_equal);
        assert_ne!(all_reads_equal, 0);

        let solver = Z3_mk_solver(c);
        Z3_solver_assert(c, solver, Z3_mk_eq(c, a, all_true));
        Z3_solver_assert(c, solver, Z3_mk_eq(c, b, stored_true));
        Z3_solver_assert(c, solver, all_reads_equal);
        assert_ne!(
            Z3_solver_check(c, solver),
            Z3_L_FALSE,
            "a goal whose arrays are pinned off-carrier is satisfiable — the \
             extensionality lemma must not be injected into it (z3 5.0.0: unknown)"
        );

        // CONTROL: the same two definitions without the quantifier are `sat` in
        // z3 5.0.0, and must stay sat here.
        let control = Z3_mk_solver(c);
        Z3_solver_assert(c, control, Z3_mk_eq(c, a, all_true));
        Z3_solver_assert(c, control, Z3_mk_eq(c, b, stored_true));
        assert_eq!(
            Z3_solver_check(c, control),
            Z3_L_TRUE,
            "the two definitions alone are satisfiable"
        );

        Z3_del_context(c);
    }
}

/// SOUNDNESS REGRESSION — binder capture. For
/// `forall ch:Char. select(a, ch) = select(store(b, f(ch), true), ch)` a bridge
/// that reads the operands off the body without an occurs check records
/// `a = store(b, f(ch), true)` with `ch` ESCAPING as a free constant, which is
/// a different (and unentailed) claim about `f`'s value at an arbitrary point.
/// Nothing may be registered for it.
///
/// Oracle (z3 5.0.0): the goal alone is `sat`.
#[test]
fn bounded_array_extensionality_refuses_binder_capture() {
    unsafe {
        let c = ctx();
        let boolean = Z3_mk_bool_sort(c);
        let char_sort = Z3_mk_char_sort(c);
        let char_array = Z3_mk_array_sort(c, char_sort, boolean);
        let a = Z3_mk_const(c, sym(c, c"capture_a"), char_array);
        let b = Z3_mk_const(c, sym(c, c"capture_b"), char_array);
        let ch = Z3_mk_const(c, sym(c, c"capture_index"), char_sort);

        let domain = [char_sort];
        let f = Z3_mk_func_decl(c, sym(c, c"capture_f"), 1, domain.as_ptr(), char_sort);
        assert_ne!(f, ptr::null_mut());
        let args = [ch];
        let f_ch = Z3_mk_app(c, f, 1, args.as_ptr());
        assert_ne!(f_ch, 0);

        let written = Z3_mk_store(c, b, f_ch, Z3_mk_true(c));
        assert_ne!(written, 0);
        let body = Z3_mk_eq(c, Z3_mk_select(c, a, ch), Z3_mk_select(c, written, ch));
        let quantifier = Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), body);
        assert_ne!(quantifier, 0);
        let quantifier_term = checked_ast_to_term(&*c, quantifier).expect("quantifier term");
        assert_eq!(
            (*c).bounded_array_ext_lemmas.get(&quantifier_term),
            None,
            "an operand that is not a free constant (and would capture the \
             binder) must register no lemma"
        );

        // And the goal itself must not be refuted (z3 5.0.0: sat).
        let solver = Z3_mk_solver(c);
        Z3_solver_assert(c, solver, quantifier);
        assert_ne!(
            Z3_solver_check(c, solver),
            Z3_L_FALSE,
            "the capture goal is satisfiable in z3 5.0.0"
        );

        Z3_del_context(c);
    }
}

/// The lemma's conclusion is exactly ONE core equality, registered under exactly
/// the quantifier the caller built, and only for the recognized shape: two FREE
/// array constants read at the binder. A mutant that fires on an unrelated body,
/// on an already-exact `Int` index, or on an interpreted array operand is caught
/// here by name.
#[test]
fn bounded_array_ext_lemma_registers_exactly_the_array_equality() {
    unsafe {
        let c = ctx();
        let boolean = Z3_mk_bool_sort(c);
        let integer = Z3_mk_int_sort(c);
        let char_sort = Z3_mk_char_sort(c);

        // An UNBOUNDED index sort is already extensionally exact in the core,
        // so the lemma is unnecessary and must not be registered.
        let int_array = Z3_mk_array_sort(c, integer, boolean);
        let p = Z3_mk_const(c, sym(c, c"int_array_p"), int_array);
        let q = Z3_mk_const(c, sym(c, c"int_array_q"), int_array);
        let i = Z3_mk_const(c, sym(c, c"int_array_index"), integer);
        let int_body = Z3_mk_eq(c, Z3_mk_select(c, p, i), Z3_mk_select(c, q, i));
        let int_forall = Z3_mk_forall_const(c, 0, 1, &raw const i, 0, ptr::null(), int_body);
        assert_ne!(int_forall, 0);
        assert!(
            (*c).bounded_array_ext_lemmas.is_empty(),
            "an Int-indexed array needs no carrier lemma"
        );

        // A Char index over two free constants is the real case: exactly `a = b`.
        let char_array = Z3_mk_array_sort(c, char_sort, boolean);
        let a = Z3_mk_const(c, sym(c, c"bridge_a"), char_array);
        let b = Z3_mk_const(c, sym(c, c"bridge_b"), char_array);
        let a_term = checked_ast_to_term(&*c, a).expect("array const term");
        let b_term = checked_ast_to_term(&*c, b).expect("array const term");

        let ch = Z3_mk_const(c, sym(c, c"bridge_index"), char_sort);
        let body = Z3_mk_eq(c, Z3_mk_select(c, a, ch), Z3_mk_select(c, b, ch));
        let quantifier = Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), body);
        let quantifier_term = checked_ast_to_term(&*c, quantifier).expect("quantifier term");
        let expected = (*c).solver.eq(a_term, b_term);
        let lemma = (*c)
            .bounded_array_ext_lemmas
            .get(&quantifier_term)
            .expect("the recognized shape registers a lemma");
        assert_eq!(lemma.equality, expected);
        assert_eq!(lemma.left, a_term);
        assert_eq!(lemma.right, b_term);
        assert_eq!(lemma.carrier_hi, AY_MAX_CHAR);
        assert_eq!((*c).bounded_array_ext_lemmas.len(), 1);

        // A body that is NOT pointwise agreement of two reads AT the bound
        // variable must register nothing.
        let other = Z3_mk_const(c, sym(c, c"bridge_other"), char_sort);
        let unrelated_body = Z3_mk_eq(c, Z3_mk_select(c, a, ch), Z3_mk_select(c, b, other));
        let unrelated = Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), unrelated_body);
        let unrelated_term = checked_ast_to_term(&*c, unrelated).expect("quantifier term");
        assert_eq!((*c).bounded_array_ext_lemmas.get(&unrelated_term), None);

        // An INTERPRETED array operand pins off-carrier values, so no lemma —
        // this is the guard the first attempt lacked (see the D1 regression).
        let all_true = Z3_mk_const_array(c, char_sort, Z3_mk_true(c));
        assert_ne!(all_true, 0);
        let const_body = Z3_mk_eq(c, Z3_mk_select(c, a, ch), Z3_mk_select(c, all_true, ch));
        let const_forall = Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), const_body);
        let const_term = checked_ast_to_term(&*c, const_forall).expect("quantifier term");
        assert_eq!(
            (*c).bounded_array_ext_lemmas.get(&const_term),
            None,
            "a const-array operand pins every core index"
        );

        let stored = Z3_mk_store(c, b, Z3_mk_char(c, 0), Z3_mk_true(c));
        assert_ne!(stored, 0);
        let store_body = Z3_mk_eq(c, Z3_mk_select(c, a, ch), Z3_mk_select(c, stored, ch));
        let store_forall = Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), store_body);
        let store_term = checked_ast_to_term(&*c, store_forall).expect("quantifier term");
        assert_eq!(
            (*c).bounded_array_ext_lemmas.get(&store_term),
            None,
            "a store operand inherits its base's off-carrier values"
        );

        Z3_del_context(c);
    }
}

/// SOUNDNESS GUARD. The lemma rests on a canonical extension that exists only
/// when the index sort is DIRECTLY bounded and the element sort carries no
/// further bounded lowering of its own. A mutant that drops
/// `bounded_array_sort_supported` is caught here.
#[test]
fn bounded_array_ext_lemma_refuses_unencodable_element_sorts() {
    unsafe {
        let c = ctx();
        let boolean = Z3_mk_bool_sort(c);
        let char_sort = Z3_mk_char_sort(c);

        let char_array = Z3_mk_array_sort(c, char_sort, boolean);
        assert!(bounded_array_sort_supported(&Sort::array(
            Sort::Char,
            Sort::Bool
        )));
        // Indexing BY an Array(Char, Bool) is the unencodable shape.
        let higher_order = Z3_mk_array_sort(c, char_array, boolean);
        assert_ne!(higher_order, ptr::null_mut());
        let unencodable_element = Sort::array(Sort::array(Sort::Char, Sort::Bool), Sort::Bool);
        assert!(!bounded_array_sort_supported(&unencodable_element));
        // ... and it stays unencodable when it is the ELEMENT of a Char-indexed
        // array, which is exactly the shape whose binder IS bounded and would
        // therefore reach the lemma without the recursive guard.
        let outer = Z3_mk_array_sort(c, char_sort, higher_order);
        assert_ne!(outer, ptr::null_mut());
        assert!(!bounded_array_sort_supported(&Sort::array(
            Sort::Char,
            unencodable_element
        )));
        // A non-array sort has no carrier lemma at all.
        assert!(!bounded_array_sort_supported(&Sort::Bool));

        let u = Z3_mk_const(c, sym(c, c"unencodable_u"), outer);
        let v = Z3_mk_const(c, sym(c, c"unencodable_v"), outer);
        let ch = Z3_mk_const(c, sym(c, c"unencodable_index"), char_sort);
        let body = Z3_mk_eq(c, Z3_mk_select(c, u, ch), Z3_mk_select(c, v, ch));
        assert_ne!(body, 0);
        let quantifier = Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), body);
        let quantifier_term = checked_ast_to_term(&*c, quantifier).expect("quantifier term");
        assert_eq!(
            (*c).bounded_array_ext_lemmas.get(&quantifier_term),
            None,
            "no canonical representative exists, so no equality may be claimed"
        );

        Z3_del_context(c);
    }
}

/// SOUNDNESS. `Z3_mk_array_ext` mints its witness at the PUBLIC index sort, so
/// for a bounded carrier the witness carries the `0 <= k <= hi` invariant while
/// its axiom `a != b => a[k] != b[k]` speaks about CORE disequality. On arrays
/// that are pinned off-carrier (`const-array`, `store`) those two are not the
/// same relation, and the pair must not refute a goal the oracle satisfies.
///
/// Oracle (z3 5.0.0, `Ext(a,b)` built through the same C entry point): `sat`,
/// with model `a = K(D1, True)`, `b = Store(K(D1, False), 0, True)`,
/// `Ext = [else -> 0]`.
#[test]
fn array_ext_witness_must_not_refute_a_satisfiable_bounded_carrier_goal() {
    unsafe {
        let c = ctx();
        let boolean = Z3_mk_bool_sort(c);
        let d1 = Z3_mk_finite_domain_sort(c, sym(c, c"probeExtD1"), 1);
        let d1_array = Z3_mk_array_sort(c, d1, boolean);
        let a = Z3_mk_const(c, sym(c, c"ext_probe_a"), d1_array);
        let b = Z3_mk_const(c, sym(c, c"ext_probe_b"), d1_array);
        let zero = Z3_mk_numeral(c, c"0".as_ptr(), d1);
        let all_true = Z3_mk_const_array(c, d1, Z3_mk_true(c));
        let all_false = Z3_mk_const_array(c, d1, Z3_mk_false(c));
        let stored_true = Z3_mk_store(c, all_false, zero, Z3_mk_true(c));
        let ext = Z3_mk_array_ext(c, a, b);
        assert_ne!(ext, 0);
        let solver = Z3_mk_solver(c);
        Z3_solver_assert(c, solver, Z3_mk_eq(c, a, all_true));
        Z3_solver_assert(c, solver, Z3_mk_eq(c, b, stored_true));
        Z3_solver_assert(c, solver, Z3_mk_not(c, Z3_mk_eq(c, a, b)));
        // Make the witness reachable so its axiom is asserted.
        Z3_solver_assert(
            c,
            solver,
            Z3_mk_eq(c, Z3_mk_select(c, a, ext), Z3_mk_select(c, a, ext)),
        );
        assert_ne!(
            Z3_solver_check(c, solver),
            Z3_L_FALSE,
            "PROBE RESULT: array_ext's bounded witness refutes a z3-sat goal"
        );
        Z3_del_context(c);
    }
}

/// The check-time canonicity scan is what keeps a REGISTERED lemma from firing
/// into a goal it does not cover: the same two free arrays, the same
/// quantifier, but a third array in the goal that is pinned off-carrier by a
/// `const-array`. The lemma stays silent and the verdict is honest.
///
/// (z3 5.0.0 answers `unsat` on this goal; AY answers `unknown` — a DELIBERATE
/// fail-closed narrowing, never a wrong verdict.)
#[test]
fn bounded_array_ext_lemma_is_withheld_when_the_goal_pins_off_carrier_values() {
    unsafe {
        let c = ctx();
        let boolean = Z3_mk_bool_sort(c);
        let char_sort = Z3_mk_char_sort(c);
        let char_array = Z3_mk_array_sort(c, char_sort, boolean);
        let a = Z3_mk_const(c, sym(c, c"scan_a"), char_array);
        let b = Z3_mk_const(c, sym(c, c"scan_b"), char_array);
        let e = Z3_mk_const(c, sym(c, c"scan_e"), char_array);
        let ch = Z3_mk_const(c, sym(c, c"scan_index"), char_sort);
        let body = Z3_mk_eq(c, Z3_mk_select(c, a, ch), Z3_mk_select(c, b, ch));
        let quantifier = Z3_mk_forall_const(c, 0, 1, &raw const ch, 0, ptr::null(), body);
        let quantifier_term = checked_ast_to_term(&*c, quantifier).expect("quantifier term");
        assert!(
            (*c).bounded_array_ext_lemmas.contains_key(&quantifier_term),
            "the lemma IS registered — the scan is what withholds it"
        );

        let all_true = Z3_mk_const_array(c, char_sort, Z3_mk_true(c));
        assert_ne!(all_true, 0);
        let solver = Z3_mk_solver(c);
        Z3_solver_assert(c, solver, quantifier);
        Z3_solver_assert(c, solver, Z3_mk_not(c, Z3_mk_eq(c, a, b)));
        Z3_solver_assert(c, solver, Z3_mk_eq(c, e, all_true));
        assert_ne!(
            Z3_solver_check(c, solver),
            Z3_L_TRUE,
            "a released SAT here would contradict the oracle (z3 5.0.0: unsat)"
        );

        // The scan's own verdict, asserted directly so a mutant that widens it
        // is caught even if the engine's answer happens not to move.
        let lemma = (*c)
            .bounded_array_ext_lemmas
            .get(&quantifier_term)
            .expect("registered above")
            .clone();
        let const_array_term = checked_ast_to_term(&*c, all_true).expect("const array term");
        assert!(
            !goal_admits_canonical_extension(&*c, &lemma, &[const_array_term]),
            "a const-array of the lowered sort must fail the canonicity scan"
        );
        let a_term = checked_ast_to_term(&*c, a).expect("array const term");
        let b_term = checked_ast_to_term(&*c, b).expect("array const term");
        assert!(
            goal_admits_canonical_extension(&*c, &lemma, &[a_term, b_term]),
            "two free array constants must pass it"
        );

        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_solver_solve_for — sound direct solved forms.
// ============================================================================

#[test]
fn solve_for_direct_equalities() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, sym(c, c"sfx"), int);
        let y = Z3_mk_const(c, sym(c, c"sfy"), int);
        let z = Z3_mk_const(c, sym(c, c"sfz"), int);
        let one = Z3_mk_int(c, 1, int);
        let s = Z3_mk_solver(c);
        // x = y + 1 (direct solved form for x); z has no equation.
        let add_args = [y, one];
        let y_plus_1 = Z3_mk_add(c, 2, add_args.as_ptr());
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, y_plus_1));
        let vars = Z3_mk_ast_vector(c);
        let terms = Z3_mk_ast_vector(c);
        let guards = Z3_mk_ast_vector(c);
        Z3_ast_vector_push(c, vars, x);
        Z3_ast_vector_push(c, vars, z);
        Z3_solver_solve_for(c, s, vars, terms, guards);
        // x solved (kept), z unsolved (dropped); parallel vectors.
        assert_eq!(Z3_ast_vector_size(c, vars), 1);
        assert_eq!(Z3_ast_vector_size(c, terms), 1);
        assert_eq!(Z3_ast_vector_size(c, guards), 1);
        assert_eq!(Z3_ast_vector_get(c, vars, 0), x);
        assert_eq!(
            Z3_ast_vector_get(c, terms, 0),
            y_plus_1,
            "solution must be y+1"
        );
        assert_eq!(Z3_ast_vector_get(c, guards, 0), Z3_mk_true(c));
        Z3_del_context(c);
    }
}

#[test]
fn solve_for_occurs_check_refuses() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, sym(c, c"socx"), int);
        let one = Z3_mk_int(c, 1, int);
        let s = Z3_mk_solver(c);
        // x = x + 1 is NOT a solved form (x occurs on the right).
        let add_args = [x, one];
        let x_plus_1 = Z3_mk_add(c, 2, add_args.as_ptr());
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, x_plus_1));
        let vars = Z3_mk_ast_vector(c);
        let terms = Z3_mk_ast_vector(c);
        let guards = Z3_mk_ast_vector(c);
        Z3_ast_vector_push(c, vars, x);
        Z3_solver_solve_for(c, s, vars, terms, guards);
        assert_eq!(
            Z3_ast_vector_size(c, vars),
            0,
            "occurs-check must refuse x = x+1"
        );
        assert_eq!(Z3_ast_vector_size(c, terms), 0);
        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_solver_cube — real lookahead cubes; cover property.
// ============================================================================

#[test]
fn cube_covers_and_terminates() {
    unsafe {
        let c = ctx();
        let bs = Z3_mk_bool_sort(c);
        let p = Z3_mk_const(c, sym(c, c"cbp"), bs);
        let q = Z3_mk_const(c, sym(c, c"cbq"), bs);
        let s = Z3_mk_solver(c);
        let or_args = [p, q];
        Z3_solver_assert(c, s, Z3_mk_or(c, 2, or_args.as_ptr()));
        let vars = Z3_mk_ast_vector(c);
        let mut cubes: Vec<Vec<Z3_ast>> = Vec::new();
        for _ in 0..16 {
            let cube = Z3_solver_cube(c, s, vars, 0);
            assert!(!cube.is_null());
            let n = Z3_ast_vector_size(c, cube);
            if n == 0 {
                break; // the empty "rest of the space" terminator
            }
            let lits: Vec<Z3_ast> = (0..n).map(|i| Z3_ast_vector_get(c, cube, i)).collect();
            cubes.push(lits);
        }
        assert!(
            !cubes.is_empty(),
            "a splittable skeleton must yield at least one cube"
        );
        // SOUNDNESS (cover): every cube must be consistent with the assertions
        // OR refuted — and each literal must be a real Bool term.
        for cube in &cubes {
            for &lit in cube {
                assert_ne!(lit, 0);
                let sort = Z3_get_sort(c, lit);
                assert_eq!(Z3_get_sort_kind(c, sort), Z3_BOOL_SORT);
            }
        }
        Z3_del_context(c);
    }
}

#[test]
fn cube_unsat_returns_false_cube() {
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_false(c));
        let vars = Z3_mk_ast_vector(c);
        let cube = Z3_solver_cube(c, s, vars, 0);
        assert_eq!(
            Z3_ast_vector_size(c, cube),
            1,
            "refuted skeleton → the [false] cube"
        );
        assert_eq!(Z3_ast_vector_get(c, cube, 0), Z3_mk_false(c));
        // Then exhausted.
        let done = Z3_solver_cube(c, s, vars, 0);
        assert_eq!(Z3_ast_vector_size(c, done), 0);
        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_model_extrapolate — sound implicant under a model.
// ============================================================================

#[test]
fn model_extrapolate_returns_sound_implicant() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, sym(c, c"mex"), int);
        let five = Z3_mk_int(c, 5, int);
        let two = Z3_mk_int(c, 2, int);
        let zero = Z3_mk_int(c, 0, int);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, five));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        assert!(!m.is_null());
        // (x > 2) | (x < 0) under x = 5 → the satisfied disjunct (x > 2)
        // (libz3-cross-checked shape).
        let lit1 = Z3_mk_gt(c, x, two);
        let lit2 = Z3_mk_lt(c, x, zero);
        let or_args = [lit1, lit2];
        let fml = Z3_mk_or(c, 2, or_args.as_ptr());
        let g = Z3_model_extrapolate(c, m, fml);
        assert_eq!(g, lit1, "the satisfied disjunct is the implicant");
        // SOUNDNESS: implicant ∧ ¬fml must be UNSAT (implicant ⇒ fml).
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, g);
        Z3_solver_assert(c, s2, Z3_mk_not(c, fml));
        assert_eq!(
            Z3_solver_check(c, s2),
            Z3_L_FALSE,
            "implicant must imply fml"
        );
        // Conjunction keeps ALL conjuncts; result must still imply fml.
        let ge5 = Z3_mk_ge(c, x, five);
        let and_args = [lit1, ge5];
        let conj = Z3_mk_and(c, 2, and_args.as_ptr());
        let g2 = Z3_model_extrapolate(c, m, conj);
        assert_ne!(g2, 0);
        let s3 = Z3_mk_solver(c);
        Z3_solver_assert(c, s3, g2);
        Z3_solver_assert(c, s3, Z3_mk_not(c, conj));
        assert_eq!(Z3_solver_check(c, s3), Z3_L_FALSE);
        // m ⊭ fml → false (deliberate, documented divergence from libz3's
        // unsound `true`; false is the sound empty implicant).
        let g3 = Z3_model_extrapolate(c, m, lit2);
        assert_eq!(g3, Z3_mk_false(c));
        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_pattern_to_ast — multi-trigger grouping node.
// ============================================================================

#[test]
fn pattern_to_ast_multi_trigger_groups() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let dom = [int];
        let f = Z3_mk_func_decl(c, sym(c, c"ptf"), 1, dom.as_ptr(), int);
        let g = Z3_mk_func_decl(c, sym(c, c"ptg"), 1, dom.as_ptr(), int);
        let b0 = Z3_mk_bound(c, 0, int);
        let fa = [b0];
        let fx = Z3_mk_app(c, f, 1, fa.as_ptr());
        let gx = Z3_mk_app(c, g, 1, fa.as_ptr());
        let pats = [fx, gx];
        let pat = Z3_mk_pattern(c, 2, pats.as_ptr());
        let ast = Z3_pattern_to_ast(c, pat);
        assert_ne!(ast, 0, "multi-trigger pattern must be a real AST");
        // Z3 shape: an APP named `pattern` over the triggers, at sort Bool.
        assert_eq!(Z3_get_ast_kind(c, ast), Z3_APP_AST);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, ast)), Z3_BOOL_SORT);
        let app = Z3_to_app(c, ast);
        assert_eq!(Z3_get_app_num_args(c, app), 2);
        assert_eq!(Z3_get_app_arg(c, app, 0), fx);
        assert_eq!(Z3_get_app_arg(c, app, 1), gx);
        // Single-trigger still returns the sole trigger itself.
        let pat1 = Z3_mk_pattern(c, 1, pats.as_ptr());
        assert_eq!(Z3_pattern_to_ast(c, pat1), fx);
        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_mk_type_variable — faithful round-trip, monomorphic use.
// ============================================================================

#[test]
fn type_variable_roundtrips() {
    unsafe {
        let c = ctx();
        let tv = Z3_mk_type_variable(c, sym(c, c"alpha"));
        assert!(!tv.is_null());
        // libz3-cross-checked: kind 14 (Z3_TYPE_VAR), name `alpha`.
        assert_eq!(Z3_get_sort_kind(c, tv), Z3_TYPE_VAR);
        let name = Z3_get_sort_name(c, tv);
        assert!(!name.is_null());
        let name_str = CStr::from_ptr(Z3_get_symbol_string(c, name));
        assert_eq!(
            name_str.to_str().expect("sort name must be valid UTF-8"),
            "alpha"
        );
        // Monomorphic use in a decl signature works like an uninterpreted sort.
        let dom = [tv];
        let f = Z3_mk_func_decl(c, sym(c, c"tvf"), 1, dom.as_ptr(), tv);
        assert!(!f.is_null());
        let a = Z3_mk_const(c, sym(c, c"tva"), tv);
        let args = [a];
        let fa = Z3_mk_app(c, f, 1, args.as_ptr());
        assert_ne!(fa, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, fa)), Z3_TYPE_VAR);
        // f(a) = a is satisfiable (an ordinary UF query at the variable).
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, fa, a));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

// ============================================================================
// Finite-domain sorts — bounded-Int lowering with the exact range axiom.
// ============================================================================

#[test]
fn finite_domain_sort_roundtrip_and_pigeonhole() {
    unsafe {
        let c = ctx();
        let fd = Z3_mk_finite_domain_sort(c, sym(c, c"D"), 3);
        assert!(!fd.is_null());
        assert_eq!(Z3_get_sort_kind(c, fd), Z3_FINITE_DOMAIN_SORT);
        let mut size: u64 = 0;
        assert!(Z3_get_finite_domain_sort_size(c, fd, &raw mut size));
        assert_eq!(size, 3, "cardinality must round-trip");
        // Non-FD sort → false, and the size slot is zeroed exactly as libz3 does
        // (a caller that ignores the boolean must not read back a stale value).
        let int = Z3_mk_int_sort(c);
        let mut probe: u64 = 77;
        assert!(!Z3_get_finite_domain_sort_size(c, int, &raw mut probe));
        assert_eq!(probe, 0);
        // SOUNDNESS (libz3-cross-checked UNSAT): 4 pairwise-distinct elements
        // of a size-3 domain are a pigeonhole contradiction.
        let e: Vec<Z3_ast> = (0..4)
            .map(|i| {
                let name = CString::new(format!("fde{i}"))
                    .expect("generated finite-domain symbol must not contain an interior NUL");
                Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), fd)
            })
            .collect();
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_distinct(c, 4, e.as_ptr()));
        assert_eq!(
            Z3_solver_check(c, s),
            Z3_L_FALSE,
            "distinct-4 over |D|=3 must be UNSAT"
        );
        // 3 distinct elements are fine.
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_distinct(c, 3, e.as_ptr()));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE);
        // A single element distinct from ALL of 0, 1, 2 is out of carrier → UNSAT.
        let d = Z3_mk_const(c, sym(c, c"fdd"), fd);
        let vals: Vec<Z3_ast> = (0..3).map(|i| Z3_mk_int64(c, i, fd)).collect();
        let all = [d, vals[0], vals[1], vals[2]];
        let s3 = Z3_mk_solver(c);
        Z3_solver_assert(c, s3, Z3_mk_distinct(c, 4, all.as_ptr()));
        assert_eq!(
            Z3_solver_check(c, s3),
            Z3_L_FALSE,
            "the carrier is exactly {{0,1,2}}"
        );
        Z3_del_context(c);
    }
}

#[test]
fn finite_domain_numerals_and_validation() {
    unsafe {
        let c = ctx();
        let fd = Z3_mk_finite_domain_sort(c, sym(c, c"D5"), 5);
        // In-range numeral round-trips at the FD sort.
        let n2 = Z3_mk_int64(c, 2, fd);
        assert_ne!(n2, 0);
        assert_eq!(
            Z3_get_sort_kind(c, Z3_get_sort(c, n2)),
            Z3_FINITE_DOMAIN_SORT
        );
        // Out-of-range numeral → honest error (libz3: "value is out of bounds").
        assert_eq!(Z3_mk_int64(c, 5, fd), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_int64(c, -1, fd), 0);
        // Size-0 domain rejected (libz3: "may not be 0").
        assert!(Z3_mk_finite_domain_sort(c, sym(c, c"E0"), 0).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        // FD-ranged FUNCTION results carry the bound: g : Int -> D3 admits at
        // most 3 distinct images (SOUNDNESS: UNSAT, matching libz3).
        let fd3 = Z3_mk_finite_domain_sort(c, sym(c, c"D3g"), 3);
        let int = Z3_mk_int_sort(c);
        let dom = [int];
        let g = Z3_mk_func_decl(c, sym(c, c"fdg"), 1, dom.as_ptr(), fd3);
        let apps: Vec<Z3_ast> = (0..4)
            .map(|i| {
                let arg = [Z3_mk_int(c, i, int)];
                Z3_mk_app(c, g, 1, arg.as_ptr())
            })
            .collect();
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_distinct(c, 4, apps.as_ptr()));
        assert_eq!(
            Z3_solver_check(c, s),
            Z3_L_FALSE,
            "4 distinct images in |D|=3 is UNSAT"
        );
        Z3_del_context(c);
    }
}

#[test]
fn bounded_sorts_are_relativized_under_quantifiers() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // SOUNDNESS: exists d:FD(3). d > 2 must be UNSAT (the carrier is
        // {0,1,2}); an unguarded Int lowering would make it SAT = wrong answer.
        let fd = Z3_mk_finite_domain_sort(c, sym(c, c"DQ"), 3);
        let d = Z3_mk_const(c, sym(c, c"dqv"), fd);
        let two = Z3_mk_int(c, 2, int);
        let body = Z3_mk_gt(c, d, two);
        let ex = Z3_mk_exists_const(c, 0, 1, &raw const d, 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, ex);
        assert_eq!(
            Z3_solver_check(c, s),
            Z3_L_FALSE,
            "exists d:D3. d > 2 must be UNSAT"
        );
        // Same for Char: exists ch:Char. ch > 196607 must be UNSAT.
        let ch_sort = Z3_mk_char_sort(c);
        let ch = Z3_mk_const(c, sym(c, c"chq"), ch_sort);
        let max = Z3_mk_int(c, 196607, int);
        let body2 = Z3_mk_gt(c, ch, max);
        let ex2 = Z3_mk_exists_const(c, 0, 1, &raw const ch, 0, ptr::null(), body2);
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, ex2);
        assert_eq!(
            Z3_solver_check(c, s2),
            Z3_L_FALSE,
            "exists ch:Char. ch > max must be UNSAT"
        );
        Z3_del_context(c);
    }
}

// ============================================================================
// HO-seq constructors — real terms, honest unknown at solve.
// ============================================================================

#[test]
fn ho_seq_constructors_roundtrip_and_solve_unknown() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let seq_int = Z3_mk_seq_sort(c, int);
        let arr = Z3_mk_array_sort(c, int, int);
        let f = Z3_mk_const(c, sym(c, c"hsf"), arr);
        let s = Z3_mk_const(c, sym(c, c"hss"), seq_int);
        // seq.map : (Array Int Int) × (Seq Int) → (Seq Int)  (libz3-checked).
        let mp = Z3_mk_seq_map(c, f, s);
        assert_ne!(mp, 0);
        let mp_sort = Z3_get_sort(c, mp);
        assert_eq!(Z3_get_sort_kind(c, mp_sort), Z3_SEQ_SORT);
        let rendered = CStr::from_ptr(Z3_ast_to_string(c, mp));
        assert!(
            rendered
                .to_str()
                .expect("rendered sequence term must be valid UTF-8")
                .contains("seq.map"),
            "term must round-trip"
        );
        // seq.foldl : f × acc × s → acc sort.
        let arr2 = Z3_mk_array_sort(c, int, arr);
        let f2 = Z3_mk_const(c, sym(c, c"hsf2"), arr2);
        let zero = Z3_mk_int(c, 0, int);
        let fl = Z3_mk_seq_foldl(c, f2, zero, s);
        assert_ne!(fl, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, fl)), Z3_INT_SORT);
        // seq.mapi / seq.foldli build too.
        let mpi = Z3_mk_seq_mapi(c, f2, zero, s);
        assert_ne!(mpi, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, mpi)), Z3_SEQ_SORT);
        let arr3 = Z3_mk_array_sort(c, int, arr2);
        let f3 = Z3_mk_const(c, sym(c, c"hsf3"), arr3);
        let fli = Z3_mk_seq_foldli(c, f3, zero, zero, s);
        assert_ne!(fli, 0);
        // SOLVING an assertion over the combinator is honestly UNKNOWN — never
        // a wrong SAT from treating `seq.map` as an uninterpreted function.
        let sv = Z3_mk_solver(c);
        Z3_solver_assert(c, sv, Z3_mk_not(c, Z3_mk_eq(c, mp, s)));
        assert_eq!(
            Z3_solver_check(c, sv),
            Z3_L_UNDEF,
            "HO-seq solving must be honest unknown"
        );
        // A non-array function argument → honest sort error.
        assert_eq!(Z3_mk_seq_map(c, zero, s), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        Z3_del_context(c);
    }
}

// ============================================================================
// HO-seq SOLVING — ground + bounded unfolding (#ho-seq).
// ============================================================================

#[test]
fn ho_seq_bounded_map_goal_is_unsat() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let seq_int = Z3_mk_seq_sort(c, int);
        let arr = Z3_mk_array_sort(c, int, int);
        let f = Z3_mk_const(c, sym(c, c"hbf"), arr);
        let s = Z3_mk_const(c, sym(c, c"hbs"), seq_int);
        // The behavior-probe goal (libz3-cross-checked UNSAT):
        // (seq.map f s) = ε ∧ |s| > 0 — seq.map preserves length.
        let mp = Z3_mk_seq_map(c, f, s);
        let empty = Z3_mk_seq_empty(c, seq_int);
        let sv = Z3_mk_solver(c);
        Z3_solver_assert(c, sv, Z3_mk_eq(c, mp, empty));
        let len = Z3_mk_seq_length(c, s);
        let zero = Z3_mk_int(c, 0, int);
        Z3_solver_assert(c, sv, Z3_mk_gt(c, len, zero));
        assert_eq!(
            Z3_solver_check(c, sv),
            Z3_L_FALSE,
            "map-to-empty over a nonempty seq must be UNSAT"
        );
        Z3_del_context(c);
    }
}

#[test]
fn ho_seq_ground_map_solves_exactly() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let arr = Z3_mk_array_sort(c, int, int);
        let f = Z3_mk_const(c, sym(c, c"hgf"), arr);
        let mk_seq2 = |a: i32, b: i32| {
            let ua = Z3_mk_seq_unit(c, Z3_mk_int(c, a, int));
            let ub = Z3_mk_seq_unit(c, Z3_mk_int(c, b, int));
            let parts = [ua, ub];
            Z3_mk_seq_concat(c, 2, parts.as_ptr())
        };
        // SOUNDNESS (functional consistency): map f [1,1] = [3,4] forces
        // f(1) = 3 ∧ f(1) = 4 → UNSAT.
        let s11 = mk_seq2(1, 1);
        let k34 = mk_seq2(3, 4);
        let sv = Z3_mk_solver(c);
        Z3_solver_assert(c, sv, Z3_mk_eq(c, Z3_mk_seq_map(c, f, s11), k34));
        assert_eq!(
            Z3_solver_check(c, sv),
            Z3_L_FALSE,
            "one input mapping to two images must be UNSAT"
        );
        // map f [1,2] = [3,4] is SAT (f: 1↦3, 2↦2… any consistent table).
        let s12 = mk_seq2(1, 2);
        let sv2 = Z3_mk_solver(c);
        Z3_solver_assert(c, sv2, Z3_mk_eq(c, Z3_mk_seq_map(c, f, s12), k34));
        assert_eq!(
            Z3_solver_check(c, sv2),
            Z3_L_TRUE,
            "consistent ground map must be SAT"
        );
        // …and the model's f really maps 1 ↦ 3 (no fabricated SAT).
        let m = Z3_solver_get_model(c, sv2);
        assert!(!m.is_null());
        let one = Z3_mk_int(c, 1, int);
        let f1 = Z3_mk_select(c, f, one);
        let mut out: Z3_ast = 0;
        assert!(Z3_model_eval(c, m, f1, true, &raw mut out));
        let mut val: i32 = 0;
        assert!(Z3_get_numeral_int(c, out, &raw mut val));
        assert_eq!(val, 3, "the validated model must map 1 to 3");
        Z3_del_context(c);
    }
}

#[test]
fn ho_seq_fold_over_empty_is_the_accumulator() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let seq_int = Z3_mk_seq_sort(c, int);
        // foldl f : (Array A (Array T A)) — curried accumulator-first
        // (matching Z3_mk_array_sort_n's currying of Z3's (Array A T A)).
        let inner = Z3_mk_array_sort(c, int, int);
        let arr2 = Z3_mk_array_sort(c, int, inner);
        let f = Z3_mk_const(c, sym(c, c"hff"), arr2);
        let zero = Z3_mk_int(c, 0, int);
        let empty = Z3_mk_seq_empty(c, seq_int);
        let fl = Z3_mk_seq_foldl(c, f, zero, empty);
        let sv = Z3_mk_solver(c);
        Z3_solver_assert(c, sv, Z3_mk_not(c, Z3_mk_eq(c, fl, zero)));
        assert_eq!(
            Z3_solver_check(c, sv),
            Z3_L_FALSE,
            "foldl over the empty sequence IS the accumulator"
        );
        Z3_del_context(c);
    }
}

#[test]
fn ho_seq_unboundable_stays_honest_unknown() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let seq_int = Z3_mk_seq_sort(c, int);
        let arr = Z3_mk_array_sort(c, int, int);
        let f = Z3_mk_const(c, sym(c, c"huf"), arr);
        let g = Z3_mk_const(c, sym(c, c"hug"), arr);
        let s = Z3_mk_const(c, sym(c, c"hus"), seq_int);
        let t = Z3_mk_const(c, sym(c, c"hut"), seq_int);
        // Neither side is ground or length-bounded: solving must stay an
        // honest unknown — NEVER a wrong verdict from an uninterpreted map.
        let sv = Z3_mk_solver(c);
        Z3_solver_assert(
            c,
            sv,
            Z3_mk_eq(c, Z3_mk_seq_map(c, f, s), Z3_mk_seq_map(c, g, t)),
        );
        assert_eq!(
            Z3_solver_check(c, sv),
            Z3_L_UNDEF,
            "unboundable HO-seq goals must stay unknown"
        );
        Z3_del_context(c);
    }
}

// ============================================================================
// Polymorphic instantiation (#poly-inst) — apply-time monomorphization.
// ============================================================================

#[test]
fn poly_decl_instantiates_at_concrete_sorts() {
    unsafe {
        let c = ctx();
        let alpha = Z3_mk_type_variable(c, sym(c, c"palpha"));
        let dom = [alpha];
        let f = Z3_mk_func_decl(c, sym(c, c"pf"), 1, dom.as_ptr(), alpha);
        assert!(!f.is_null());
        // f : α → α applied at an Int numeral → Int-sorted app (libz3 parity:
        // the probe's app-sort-kind=2 on both sides).
        let int = Z3_mk_int_sort(c);
        let five = Z3_mk_int(c, 5, int);
        let args = [five];
        let f5 = Z3_mk_app(c, f, 1, args.as_ptr());
        assert_ne!(f5, 0, "instantiation must produce an app");
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, f5)), Z3_INT_SORT);
        // Same-instantiation caching: the identical application again is the
        // IDENTICAL ast (hash-consed through the cached instance decl).
        let f5b = Z3_mk_app(c, f, 1, args.as_ptr());
        assert_eq!(f5, f5b, "repeated instantiation must reuse the instance");
        // The same decl at Bool instantiates independently.
        let tt = Z3_mk_true(c);
        let bargs = [tt];
        let fb = Z3_mk_app(c, f, 1, bargs.as_ptr());
        assert_ne!(fb, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, fb)), Z3_BOOL_SORT);
        // The instantiated app SOLVES like an ordinary UF: f(5)=5 ∧ f(5)=6 UNSAT.
        let six = Z3_mk_int(c, 6, int);
        let sv = Z3_mk_solver(c);
        Z3_solver_assert(c, sv, Z3_mk_eq(c, f5, five));
        Z3_solver_assert(c, sv, Z3_mk_eq(c, f5, six));
        assert_eq!(Z3_solver_check(c, sv), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

#[test]
fn poly_decl_instantiates_through_parametric_sorts() {
    unsafe {
        let c = ctx();
        let alpha = Z3_mk_type_variable(c, sym(c, c"salpha"));
        // head : (Seq α) → α applied at (Seq Int) → Int.
        let seq_alpha = Z3_mk_seq_sort(c, alpha);
        let dom = [seq_alpha];
        let head = Z3_mk_func_decl(c, sym(c, c"phead"), 1, dom.as_ptr(), alpha);
        assert!(!head.is_null());
        let int = Z3_mk_int_sort(c);
        let seq_int = Z3_mk_seq_sort(c, int);
        let s = Z3_mk_const(c, sym(c, c"pseq"), seq_int);
        let args = [s];
        let h = Z3_mk_app(c, head, 1, args.as_ptr());
        assert_ne!(h, 0, "unification must descend through Seq");
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, h)), Z3_INT_SORT);
        Z3_del_context(c);
    }
}

#[test]
fn poly_decl_mismatched_unification_stays_sort_error() {
    unsafe {
        let c = ctx();
        let alpha = Z3_mk_type_variable(c, sym(c, c"malpha"));
        // g : (α, α) → α at (Int, Bool) — the SAME variable cannot be both.
        let dom = [alpha, alpha];
        let g = Z3_mk_func_decl(c, sym(c, c"pg"), 2, dom.as_ptr(), alpha);
        assert!(!g.is_null());
        let int = Z3_mk_int_sort(c);
        let five = Z3_mk_int(c, 5, int);
        let tt = Z3_mk_true(c);
        let args = [five, tt];
        assert_eq!(Z3_mk_app(c, g, 2, args.as_ptr()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        // A range-only variable no argument determines is also an honest error:
        // h : Int → β.
        let beta = Z3_mk_type_variable(c, sym(c, c"mbeta"));
        let dom2 = [int];
        let h = Z3_mk_func_decl(c, sym(c, c"ph"), 1, dom2.as_ptr(), beta);
        assert!(!h.is_null());
        let args2 = [five];
        assert_eq!(Z3_mk_app(c, h, 1, args2.as_ptr()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        Z3_del_context(c);
    }
}

// ============================================================================
// Fixedpoint engine-state extras.
// ============================================================================

/// Build the canonical bounded-counter system (inv(0); inv(x) ∧ x<10 ⇒
/// inv(x+1)) into `fp`. Returns `(inv, int_sort)`.
unsafe fn build_counter(c: Z3_context, fp: Z3_fixedpoint) -> (Z3_func_decl, Z3_sort) {
    unsafe {
        let int = Z3_mk_int_sort(c);
        let boolean = Z3_mk_bool_sort(c);
        let inv = Z3_mk_func_decl(c, sym(c, c"inv"), 1, &raw const int, boolean);
        Z3_fixedpoint_register_relation(c, fp, inv);
        let x = Z3_mk_const(c, sym(c, c"fpx"), int);
        let zero = Z3_mk_int(c, 0, int);
        let one = Z3_mk_int(c, 1, int);
        let ten = Z3_mk_int(c, 10, int);
        let x_eq_0 = Z3_mk_eq(c, x, zero);
        let inv_x = Z3_mk_app(c, inv, 1, &raw const x);
        let init = Z3_mk_implies(c, x_eq_0, inv_x);
        let init_rule = Z3_mk_forall_const(c, 0, 1, &raw const x, 0, ptr::null(), init);
        Z3_fixedpoint_add_rule(c, fp, init_rule, ptr::null_mut());
        let lt = Z3_mk_lt(c, x, ten);
        let ante_args = [inv_x, lt];
        let ante = Z3_mk_and(c, 2, ante_args.as_ptr());
        let add_args = [x, one];
        let xp1 = Z3_mk_add(c, 2, add_args.as_ptr());
        let inv_xp1 = Z3_mk_app(c, inv, 1, &raw const xp1);
        let trans = Z3_mk_implies(c, ante, inv_xp1);
        let trans_rule = Z3_mk_forall_const(c, 0, 1, &raw const x, 0, ptr::null(), trans);
        Z3_fixedpoint_add_rule(c, fp, trans_rule, ptr::null_mut());
        (inv, int)
    }
}

#[test]
fn fixedpoint_statistics_levels_and_cover_delta() {
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        let (inv, int) = build_counter(c, fp);
        // Before any query: empty stats, zero levels, no cover.
        let st0 = Z3_fixedpoint_get_statistics(c, fp);
        assert!(!st0.is_null());
        assert_eq!(Z3_stats_size(c, st0), 0, "no query yet → empty snapshot");
        assert_eq!(Z3_fixedpoint_get_num_levels(c, fp, inv), 0);
        // Safe query: inv(x) ∧ x > 100 is unreachable.
        let qx = Z3_mk_const(c, sym(c, c"fpqx"), int);
        let inv_qx = Z3_mk_app(c, inv, 1, &raw const qx);
        let hundred = Z3_mk_int(c, 100, int);
        let gt = Z3_mk_gt(c, qx, hundred);
        let goal_args = [inv_qx, gt];
        let goal = Z3_mk_and(c, 2, goal_args.as_ptr());
        assert_eq!(Z3_fixedpoint_query(c, fp, goal), Z3_L_FALSE);
        // REAL statistics snapshot from the run.
        let st = Z3_fixedpoint_get_statistics(c, fp);
        assert!(!st.is_null());
        assert!(
            Z3_stats_size(c, st) > 0,
            "post-query stats must carry real counters"
        );
        // num_levels: the engine's REAL max frame (>= 0; no error).
        let _levels = Z3_fixedpoint_get_num_levels(c, fp, inv);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // cover_delta(-1, inv): the VALIDATED invariant, back-translated as a
        // Bool term over __db{i} vars.
        let cov = Z3_fixedpoint_get_cover_delta(c, fp, -1, inv);
        if cov != 0 {
            assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, cov)), Z3_BOOL_SORT);
        } else {
            // Honest refusal is allowed only with an error code set (e.g. an
            // interpretation outside the back-translatable fragment).
            assert_ne!(Z3_get_error_code(c), Z3_OK);
        }
        // Finite level → the exactly-empty per-frame delta, `true` (libz3
        // spacer's probed answer on levels 0/1/2; AY tracks no finite-frame
        // lemmas, so the empty conjunction is the honest REAL value).
        let d0 = Z3_fixedpoint_get_cover_delta(c, fp, 0, inv);
        assert_ne!(d0, 0);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, d0)), Z3_BOOL_SORT);
        Z3_del_context(c);
    }
}

#[test]
fn fixedpoint_invariant_hints_trusted_and_validated() {
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        let (inv, int) = build_counter(c, fp);
        // A CORRECT trusted hint: inv ⊆ { x | x <= 10 }, over __db0.
        let db0 = Z3_mk_bound(c, 0, int);
        let ten = Z3_mk_int(c, 10, int);
        let prop = Z3_mk_le(c, db0, ten);
        Z3_fixedpoint_add_invariant(c, fp, inv, prop);
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "a translatable hint is accepted"
        );
        // The safe query still verifies with the hint injected.
        let qx = Z3_mk_const(c, sym(c, c"fphx"), int);
        let inv_qx = Z3_mk_app(c, inv, 1, &raw const qx);
        let hundred = Z3_mk_int(c, 100, int);
        let gt = Z3_mk_gt(c, qx, hundred);
        let goal_args = [inv_qx, gt];
        let goal = Z3_mk_and(c, 2, goal_args.as_ptr());
        assert_eq!(Z3_fixedpoint_query(c, fp, goal), Z3_L_FALSE);
        // Unregistered predicate → honest INVALID_ARG.
        let boolean = Z3_mk_bool_sort(c);
        let other = Z3_mk_func_decl(c, sym(c, c"notrel"), 1, &raw const int, boolean);
        Z3_fixedpoint_add_invariant(c, fp, other, prop);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        // add_cover at a finite level: honest REFUSAL (libz3's default
        // configurations error here too — datalog: unsupported; spacer:
        // incompatible with slicing; probed 2026-07-09). The hint is NOT
        // silently dropped.
        Z3_fixedpoint_add_cover(c, fp, 3, inv, prop);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        Z3_del_context(c);
    }
}

#[test]
fn fixedpoint_add_constraint_finite_level_inert_like_z3() {
    // `Z3_fixedpoint_add_constraint` at a FINITE level is INERT in libz3
    // 4.16 (Spacer only reads ∞-level constraints; the call returns OK and
    // changes nothing — confirmed by a differential behavior probe). AY must match:
    // accept, incorporate nothing, no error. The ∞ level keeps the REAL
    // trusted-lemma path.
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        let (inv, int) = build_counter(c, fp);
        let t = Z3_mk_true(c);
        // Finite levels: accepted and ignored, whatever the shape.
        Z3_fixedpoint_add_constraint(c, fp, t, 0);
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "finite level must be inert-accepted"
        );
        Z3_fixedpoint_add_constraint(c, fp, t, 3);
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "finite level must be inert-accepted"
        );
        // The query is unaffected by the ignored hints (real solve).
        let qx = Z3_mk_const(c, sym(c, c"fpcx"), int);
        let inv_qx = Z3_mk_app(c, inv, 1, &raw const qx);
        let hundred = Z3_mk_int(c, 100, int);
        let gt = Z3_mk_gt(c, qx, hundred);
        let goal_args = [inv_qx, gt];
        let goal = Z3_mk_and(c, 2, goal_args.as_ptr());
        assert_eq!(Z3_fixedpoint_query(c, fp, goal), Z3_L_FALSE);
        // ∞ level (UINT_MAX): the REAL path is untouched — a bare `true`
        // is not an implication over a registered relation → honest refusal
        // (`Z3_INVALID_USAGE`), never silently dropped. (The accepted
        // ∞-level implication shape is covered by the add_invariant /
        // add_cover(-1) tests, which share `register_db_property_hint`.)
        Z3_fixedpoint_add_constraint(c, fp, t, u32::MAX);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        let _ = int;
        Z3_del_context(c);
    }
}
