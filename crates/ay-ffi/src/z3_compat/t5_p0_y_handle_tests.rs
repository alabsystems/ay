// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T5 P0.2 quarantine, implementer Y: Q7 (`x^0` in text), Q10 (parameters
//! per handle, interrupt) and Q11 (model translate / print).
//!
//! Every pin cites its libz3 5.1.0 measurement: z3py 5.1.0 over the real
//! library, one case of the T5 P0 implementer-Y pin script `ypins.py`
//! (`~/ay-bench/t5y-bench`), each case in its own process.

use std::ffi::{c_int, c_uint};
use std::ptr;

use super::t5_p0_y_tests::{app1, ctx, int, int_const, int_decl, sym, text};
use crate::z3_compat::*;

/// libz3 5.1.0 (ypins.py q10_interrupt_solver, q10_interrupt_optimize): a check after
/// `Z3_interrupt` answers sat; the flag is not sticky.
#[test]
fn q10_interrupt_is_cleared_at_check_entry() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_gt(c, int_const(c, c"x"), int(c, 0)));
        Z3_interrupt(c);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_lt(c, int_const(c, c"y"), int(c, 3)));
        Z3_interrupt(c);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

unsafe fn set_timeout(c: Z3_context, ms: c_uint) -> Z3_params {
    // SAFETY: the caller passes a live context `c` owned by this test.
    unsafe {
        let p = Z3_mk_params(c);
        Z3_params_set_uint(c, p, sym(c, c"timeout"), ms);
        p
    }
}

/// libz3 5.1.0 (ypins.py q10_timeout_leak_to_other_solver, q10_optimize_timeout_leak): `s1.set("timeout", 1)` governs `s1`
/// only (a fresh `s2` answers the pigeonhole unsat); so does an Optimize's.
/// The handle's parameters reach the engine for its own checks only.
#[test]
fn q10_parameters_are_per_handle() {
    // SAFETY: all handles belong to `c`, freed at the end; `(*c)` is read
    // between API calls only.
    unsafe {
        let c = ctx();
        let s1 = Z3_mk_solver(c);
        Z3_solver_set_params(c, s1, set_timeout(c, 1));
        assert_eq!((*c).solver.timeout(), None, "set_params writes the handle");
        assert_eq!((*s1).params.over((*c).default_params), {
            let mut expected = handle_params::ParamSet::default();
            expected.record(&[("timeout".to_string(), "1".to_string())]);
            expected
        });
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_gt(c, int_const(c, c"x"), int(c, 0)));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE);
        Z3_solver_assert(c, s1, Z3_mk_gt(c, int_const(c, c"x"), int(c, 0)));
        let _ = Z3_solver_check(c, s1);
        assert_eq!((*c).solver.timeout(), None, "restored after s1's check");
        let o = Z3_mk_optimize(c);
        Z3_optimize_set_params(c, o, set_timeout(c, 1));
        assert_eq!((*c).solver.timeout(), None);

        Z3_solver_set_proof_production(c, s1, true);
        assert!(Z3_solver_get_proof_production(c, s1));
        assert!(
            !Z3_solver_get_proof_production(c, s2),
            "proofs are per handle"
        );
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q11_symbolic_else_translate_1ary): z3 carries
/// `g`'s symbolic else `[else -> 1 + Var(0)]` across contexts (`g(4)`
/// evaluates to 5 there). AY dropped it, leaving `g` uninterpreted; the
/// cross-context translation is now an error, and a same-context one keeps
/// the else.
#[test]
fn q11_model_translate_refuses_to_drop_a_symbolic_else() {
    // SAFETY: all handles belong to their contexts, freed at the end.
    unsafe {
        let c = ctx();
        let g = int_decl(c, c"g", false);
        let a = int_const(c, c"a");
        let body = Z3_mk_eq(c, app1(c, g, a), Z3_mk_add(c, 2, [a, int(c, 1)].as_ptr()));
        let q = Z3_mk_forall_const(c, 0, 1, [a].as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, q);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        assert!(!m.is_null());
        assert!((*m).func_interps.iter().any(|fi| fi.else_term.is_some()));
        let c2 = ctx();
        assert!(
            Z3_model_translate(c, m, c2).is_null(),
            "a symbolic else is never dropped"
        );
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        let same = Z3_model_translate(c, m, c);
        assert!(!same.is_null());
        assert_eq!((*same).func_interps.len(), (*m).func_interps.len());
        Z3_del_context(c2);
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q7_text, `~/ay-bench/t5-p0fix/p0fix.py` case
/// `c_power`): `(assert (= r (^ 0.0 0.0))) (assert (not (= r 1.0)))` is sat
/// (z3 keeps `0^0` as `^0`), and so is `(^ 0 0)`; `(^ 2.0 0.0)` with
/// `r != 1`, and `(^ a 0.0)` with `a != 0` and `r != 1`, are unsat; `x > 3`
/// with `(^ x 0) = 1` is sat. AY folded every `x^0` to 1 (the first two
/// unsat); 7c46d84d85 kept a raw `^` for a possibly-zero base and answered
/// every row but `(^ 2.0 0.0)` unknown. `0^0` is now one free value per sort.
#[test]
fn q7_text_zero_power_of_zero_is_free_and_nonzero_bases_fold() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        for (text_input, expected) in [
            (
                c"(declare-const r Real) (assert (= r (^ 0.0 0.0))) (assert (not (= r 1.0)))",
                Z3_L_TRUE,
            ),
            (
                c"(declare-const r Real) (assert (= r (^ 0 0))) (assert (not (= r 1.0)))",
                Z3_L_TRUE,
            ),
            (
                c"(declare-const q Real) (assert (= q (^ 2.0 0.0))) (assert (not (= q 1.0)))",
                Z3_L_FALSE,
            ),
            (
                c"(declare-const a Real) (declare-const r Real) (assert (not (= a 0.0))) \
                  (assert (= r (^ a 0.0))) (assert (not (= r 1.0)))",
                Z3_L_FALSE,
            ),
            (
                c"(declare-const x Int) (assert (> x 3)) (assert (= (^ x 0) 1))",
                Z3_L_TRUE,
            ),
        ] {
            let s = Z3_mk_solver(c);
            Z3_solver_from_string(c, s, text_input.as_ptr());
            assert_eq!(Z3_get_error_code(c), Z3_OK);
            assert_eq!(Z3_solver_check(c, s), expected, "{text_input:?}");
        }
        Z3_del_context(c);
    }
}

/// Seven pigeons into six holes (unsat; AY needs well over 1 ms).
unsafe fn pigeonhole(c: Z3_context, s: Z3_solver) {
    // SAFETY: the caller passes a live context `c` and its solver `s`.
    unsafe {
        let holes: usize = 6;
        let mut p = Vec::new();
        for i in 0..=holes {
            let row: Vec<Z3_ast> = (0..holes)
                .map(|j| {
                    let name = Z3_mk_int_symbol(c, (1000 + i * 10 + j) as c_int);
                    Z3_mk_const(c, name, Z3_mk_bool_sort(c))
                })
                .collect();
            Z3_solver_assert(c, s, Z3_mk_or(c, row.len() as c_uint, row.as_ptr()));
            p.push(row);
        }
        for j in 0..holes {
            for i in 0..=holes {
                for k in (i + 1)..=holes {
                    let both = [p[i][j], p[k][j]];
                    Z3_solver_assert(c, s, Z3_mk_not(c, Z3_mk_and(c, 2, both.as_ptr())));
                }
            }
        }
    }
}

/// libz3 5.1.0 (ypins.py q10_timeout_leak_to_other_solver, PHP6 and PHP8):
/// `('unknown', 'unsat')`: the first solver's 1 ms timeout does not reach
/// the second solver.
#[test]
fn q10_timeout_does_not_leak_to_another_solver() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let s1 = Z3_mk_solver(c);
        Z3_solver_set_params(c, s1, set_timeout(c, 1));
        pigeonhole(c, s1);
        assert_ne!(Z3_solver_check(c, s1), Z3_L_TRUE);
        let s2 = Z3_mk_solver(c);
        pigeonhole(c, s2);
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q11_rec_sexpr_vs_interp):
/// a recursive function never appears in `Z3_model_to_string`; AY's model
/// text and `Z3_model_get_func_interp` agree that it has no table.
#[test]
fn q11_model_text_omits_recursive_functions() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let f = int_decl(c, c"fact", true);
        let n = int_const(c, c"n");
        let rec = app1(c, f, Z3_mk_sub(c, 2, [n, int(c, 1)].as_ptr()));
        let step = Z3_mk_mul(c, 2, [n, rec].as_ptr());
        let body = Z3_mk_ite(c, Z3_mk_le(c, n, int(c, 0)), int(c, 1), step);
        Z3_add_rec_def(c, f, 1, [n].as_ptr(), body);
        let s = Z3_mk_solver(c);
        let z = int_const(c, c"z");
        Z3_solver_assert(c, s, Z3_mk_eq(c, z, app1(c, f, int(c, 5))));
        assert_ne!(Z3_solver_check(c, s), Z3_L_FALSE);
        let m = Z3_solver_get_model(c, s);
        if !m.is_null() {
            assert!(!text(Z3_model_to_string(c, m)).contains("fact"));
            assert!(Z3_model_get_func_interp(c, m, f).is_null());
        }
        Z3_del_context(c);
    }
}
