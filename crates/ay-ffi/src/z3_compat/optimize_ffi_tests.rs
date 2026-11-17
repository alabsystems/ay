// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible Optimize completion C API (`optimize.rs`).
//!
//! Every expected value is what libz3 reports for the same problem
//! (cross-checked by `tests/capi_optimize_consumer.c` compiled against both
//! ay-ffi and libz3). Coverage:
//! - `push`/`pop` scoping of hard assertions + objectives (optimum changes in a
//!   scope and is restored after `pop`).
//! - `assert_and_track` + `get_unsat_core` (a jointly-infeasible tracked pair
//!   yields a non-empty core; a SAT problem yields an empty core).
//! - `get_objectives` / `get_assertions` sizes.
//! - `get_upper` / `get_lower` (scalar) and `get_upper_as_vector` /
//!   `get_lower_as_vector` (`[a, b, c]` = `a*inf + b + c*eps`).
//! - `from_string` parsing a `(minimize ...)` script.
//! - `get_statistics` / `get_reason_unknown`.
//! - `set_params` / `get_help` / `get_param_descrs` (+ the `Z3_param_descrs_*`
//!   accessors).
//! - HONEST no-ops: `set_initial_value` / `register_model_eh` do not crash.

use super::super::*;
use std::ffi::{c_uint, CStr, CString};

/// Build a fresh (non-RC) context.
///
/// # Safety
/// The returned context must be freed with `Z3_del_context`.
unsafe fn mk_ctx() -> Z3_context {
    // SAFETY: standard context construction; single-threaded test.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        ctx
    }
}

/// An Int-sorted constant named `n`.
///
/// # Safety
/// `c` must be a valid context handle.
unsafe fn int_var(c: Z3_context, n: &str) -> Z3_ast {
    // SAFETY: `c` valid; the symbol string is a valid C string for the call.
    unsafe {
        let name = CString::new(n).expect("integer variable name must not contain an interior NUL");
        Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), Z3_mk_int_sort(c))
    }
}

/// A Bool-sorted constant named `n`.
///
/// # Safety
/// `c` must be a valid context handle.
unsafe fn bool_var(c: Z3_context, n: &str) -> Z3_ast {
    // SAFETY: `c` valid; the symbol string is a valid C string for the call.
    unsafe {
        let name = CString::new(n).expect("Boolean variable name must not contain an interior NUL");
        Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), Z3_mk_bool_sort(c))
    }
}

/// Read the integer value of a numeral AST.
///
/// # Safety
/// `c` must be a valid context handle; `a` a valid numeral AST handle.
unsafe fn numeral(c: Z3_context, a: Z3_ast) -> Option<i32> {
    // SAFETY: `c`/`a` valid; `v` is a live stack slot for the out-param.
    unsafe {
        let mut v: c_int = 0;
        if a != 0 && Z3_get_numeral_int(c, a, &raw mut v) {
            Some(v)
        } else {
            None
        }
    }
}

#[test]
fn bounded_maximize_optimum_and_bounds() {
    // SAFETY: single-threaded FFI test; all handles are freed via del_context.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        Z3_optimize_inc_ref(c, o);

        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        let ten = Z3_mk_int(c, 10, Z3_mk_int_sort(c));
        Z3_optimize_assert(c, o, Z3_mk_ge(c, x, zero));
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, ten));
        let obj = Z3_optimize_maximize(c, o, x);
        assert_eq!(obj, 0);

        // Introspection sizes.
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)), 2);
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o)), 1);

        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);

        // Scalar optimum == 9 (matches libz3).
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, obj)), Some(9));
        assert_eq!(numeral(c, Z3_optimize_get_lower(c, o, obj)), Some(9));

        // Vector optimum: [a, b, c] = [0, 9, 0].
        let uv = Z3_optimize_get_upper_as_vector(c, o, obj);
        assert_eq!(Z3_ast_vector_size(c, uv), 3);
        assert_eq!(numeral(c, Z3_ast_vector_get(c, uv, 0)), Some(0));
        assert_eq!(numeral(c, Z3_ast_vector_get(c, uv, 1)), Some(9));
        assert_eq!(numeral(c, Z3_ast_vector_get(c, uv, 2)), Some(0));

        // Statistics + reason-unknown are queryable after a check.
        let st = Z3_optimize_get_statistics(c, o);
        assert!(!st.is_null());
        assert!(!Z3_stats_to_string(c, st).is_null());
        assert!(!Z3_optimize_get_reason_unknown(c, o).is_null());

        Z3_optimize_dec_ref(c, o);
        Z3_del_context(c);
    }
}

#[test]
fn push_pop_scopes_the_optimum() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);

        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        let ten = Z3_mk_int(c, 10, Z3_mk_int_sort(c));
        Z3_optimize_assert(c, o, Z3_mk_ge(c, x, zero));
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, ten));
        let obj = Z3_optimize_maximize(c, o, x);

        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, obj)), Some(9));

        // In a scope, add x < 5: optimum drops to 4.
        Z3_optimize_push(c, o);
        let five = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, five));
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)), 3);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, obj)), Some(4));

        // Pop restores the original problem: optimum back to 9.
        Z3_optimize_pop(c, o);
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)), 2);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, obj)), Some(9));

        Z3_del_context(c);
    }
}

#[test]
fn pop_underflow_is_rejected() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        // Pop with no matching push -> Z3_EXCEPTION, no crash.
        Z3_optimize_pop(c, o);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        Z3_del_context(c);
    }
}

#[test]
fn assert_and_track_unsat_core() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);

        let x = int_var(c, "x");
        let five = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
        let three = Z3_mk_int(c, 3, Z3_mk_int_sort(c));
        let p1 = bool_var(c, "p1");
        let p2 = bool_var(c, "p2");
        // x >= 5 AND x <= 3 -> jointly infeasible; both tracked assertions needed.
        Z3_optimize_assert_and_track(c, o, Z3_mk_ge(c, x, five), p1);
        Z3_optimize_assert_and_track(c, o, Z3_mk_le(c, x, three), p2);

        // The tracked constraints ARE enforced, so the verdict is correctly UNSAT.
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
        let core = Z3_optimize_get_unsat_core(c, o);
        // Both literals take part (libz3: {p1, p2}); an empty core would claim
        // the untracked hard constraints alone are unsatisfiable.
        assert_eq!(Z3_ast_vector_size(c, core), 2);
        let mut members = [Z3_ast_vector_get(c, core, 0), Z3_ast_vector_get(c, core, 1)];
        members.sort_unstable();
        let mut expected = [p1, p2];
        expected.sort_unstable();
        assert_eq!(members, expected);

        Z3_del_context(c);
    }
}

/// The tracking literals of the last optimize core, in order.
unsafe fn core_of(c: Z3_context, o: Z3_optimize) -> Vec<Z3_ast> {
    // SAFETY: `c`/`o` are live; the vector is read within its context.
    unsafe {
        let core = Z3_optimize_get_unsat_core(c, o);
        (0..Z3_ast_vector_size(c, core))
            .map(|i| Z3_ast_vector_get(c, core, i))
            .collect()
    }
}

/// The O1 problem in `c`: `(xi > 0, p1)`, `(xi != 1, p2)`, `(xi < 0, p3)`.
unsafe fn o1_tracked(c: Z3_context) -> [(Z3_ast, Z3_ast); 3] {
    // SAFETY: `c` is live; every handle is built in it.
    unsafe {
        let x = int_var(c, "xi");
        let int_sort = Z3_mk_int_sort(c);
        let zero = Z3_mk_int(c, 0, int_sort);
        let one = Z3_mk_int(c, 1, int_sort);
        [
            (Z3_mk_gt(c, x, zero), bool_var(c, "p1")),
            (Z3_mk_not(c, Z3_mk_eq(c, x, one)), bool_var(c, "p2")),
            (Z3_mk_lt(c, x, zero), bool_var(c, "p3")),
        ]
    }
}

/// Critic probe O1 (z3py `Optimize.assert_and_track` doctest shape): z3 says
/// unsat with core `[p1, p3]`. AY used to return an EMPTY core, which claims
/// the untracked assertions alone (here: none) are unsat. The core must hold
/// p1 and p3 and be unsat together with the tracked implications.
#[test]
fn optimize_core_is_never_empty_when_tracking_literals_conflict() {
    // SAFETY: single-threaded FFI test; each context's handles stay in it.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let tracked = o1_tracked(c);
        for (formula, p) in tracked {
            Z3_optimize_assert_and_track(c, o, formula, p);
        }
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
        let core = core_of(c, o);
        let in_core = tracked.map(|(_, p)| core.contains(&p));
        assert!(in_core[0] && in_core[2], "{in_core:?}");
        assert_eq!(core.len(), in_core.iter().filter(|&&hit| hit).count());

        // The core is a real core: with the tracked implications it is unsat
        // (checked by a plain solver in a second context).
        let check = mk_ctx();
        let s = Z3_mk_solver(check);
        let mirror = o1_tracked(check);
        for (formula, p) in mirror {
            Z3_solver_assert(check, s, Z3_mk_implies(check, p, formula));
        }
        let assumptions: Vec<Z3_ast> = mirror
            .iter()
            .zip(in_core)
            .filter_map(|(&(_, p), hit)| hit.then_some(p))
            .collect();
        let n = assumptions.len() as c_uint;
        assert_eq!(
            Z3_solver_check_assumptions(check, s, n, assumptions.as_ptr()),
            Z3_L_FALSE
        );
        Z3_del_context(check);
        Z3_del_context(c);
    }
}

/// z3 assumes each tracking literal at every check, so tracking `x >= 0` with
/// `p` while asserting `not p` is unsat with core `[p]`. AY asserted only the
/// formula and answered sat.
#[test]
fn optimize_tracking_literal_holds_like_a_z3_assumption() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        let p = bool_var(c, "p");
        Z3_optimize_assert(c, o, Z3_mk_not(c, p));
        Z3_optimize_assert_and_track(c, o, Z3_mk_ge(c, x, zero), p);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
        assert_eq!(core_of(c, o), vec![p]);

        // In a fresh scope without `not p`, the model makes `p` true (z3: the
        // assumption holds in the model).
        let c2 = mk_ctx();
        let o2 = Z3_mk_optimize(c2);
        let p2 = bool_var(c2, "p");
        let y = int_var(c2, "y");
        let y_ge_0 = Z3_mk_ge(c2, y, Z3_mk_int(c2, 0, Z3_mk_int_sort(c2)));
        Z3_optimize_assert_and_track(c2, o2, y_ge_0, p2);
        assert_eq!(Z3_optimize_check(c2, o2, 0, ptr::null()), Z3_L_TRUE);
        let m = Z3_optimize_get_model(c2, o2);
        let mut value: Z3_ast = 0;
        assert!(Z3_model_eval(c2, m, p2, true, &raw mut value));
        assert_eq!(Z3_get_bool_value(c2, value), Z3_L_TRUE);
        Z3_del_context(c2);
        Z3_del_context(c);
    }
}

#[test]
fn sat_problem_has_empty_unsat_core() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        let p = bool_var(c, "p");
        Z3_optimize_assert_and_track(c, o, Z3_mk_ge(c, x, zero), p);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        // A SAT check leaves no unsat core.
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_unsat_core(c, o)), 0);
        Z3_del_context(c);
    }
}

#[test]
fn tracking_literal_must_be_boolean() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        // Non-Boolean tracking literal `x` -> Z3_INVALID_ARG, nothing asserted.
        Z3_optimize_assert_and_track(c, o, Z3_mk_ge(c, x, zero), x);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

#[test]
fn from_string_minimize() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let script = CString::new(
            "(declare-const y Int)\n\
             (assert (>= y 3))\n\
             (assert (<= y 100))\n\
             (minimize y)\n",
        )
        .expect("optimization script must not contain an interior NUL");
        Z3_optimize_from_string(c, o, script.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o)), 1);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_lower(c, o, 0)), Some(3));
        Z3_del_context(c);
    }
}

#[test]
fn assumptions_hold_for_one_check() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        let five = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
        let ten = Z3_mk_int(c, 10, Z3_mk_int_sort(c));
        let a = Z3_mk_ge(c, x, zero);
        Z3_optimize_assert(c, o, a);
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, ten));
        let objective = Z3_optimize_maximize(c, o, x);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(9));

        // z3 assumes check-time assumptions for that check only.
        let below_five = Z3_mk_lt(c, x, five);
        assert_eq!(Z3_optimize_check(c, o, 1, [below_five].as_ptr()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(4));
        let negative = Z3_mk_lt(c, x, zero);
        assert_eq!(Z3_optimize_check(c, o, 1, [negative].as_ptr()), Z3_L_FALSE);
        let core = Z3_optimize_get_unsat_core(c, o);
        assert_eq!(Z3_ast_vector_size(c, core), 1);
        assert!(Z3_optimize_get_model(c, o).is_null());

        // A null array for a positive count is rejected without a dereference.
        assert_eq!(Z3_optimize_check(c, o, 1, ptr::null()), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        // The assumptions were not kept.
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert!(!Z3_optimize_get_model(c, o).is_null());
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(9));
        Z3_del_context(c);
    }
}

#[test]
fn successful_mutations_retire_optimize_outcomes() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let int_sort = Z3_mk_int_sort(c);
        let zero = Z3_mk_int(c, 0, int_sort);
        let ten = Z3_mk_int(c, 10, int_sort);
        Z3_optimize_assert(c, o, Z3_mk_ge(c, x, zero));
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, ten));
        let maximize_x = Z3_optimize_maximize(c, o, x);

        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert!(!Z3_optimize_get_model(c, o).is_null());
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, maximize_x)), Some(9));

        // A successful formula mutation invalidates every copied FFI artefact,
        // even though the optimize handle still owns the previous model.
        Z3_optimize_assert(c, o, bool_var(c, "p"));
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, maximize_x), 0);
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_unsat_core(c, o)), 0);
        assert_eq!(
            CStr::from_ptr(Z3_optimize_get_reason_unknown(c, o)).to_bytes(),
            &[] as &[u8]
        );

        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert!(!Z3_optimize_get_model(c, o).is_null());

        // Objective registration is a mutation too; bounds/model are not
        // authoritative again until the next admitted SAT check.
        let _minimize_x = Z3_optimize_minimize(c, o, x);
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, maximize_x), 0);

        Z3_del_context(c);
    }
}

#[test]
fn transitive_closure_downgrade_revokes_backend_sat_outcomes() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let int_sort = Z3_mk_int_sort(c);
        let zero = Z3_mk_int(c, 0, int_sort);
        let ten = Z3_mk_int(c, 10, int_sort);
        Z3_optimize_assert(c, o, Z3_mk_ge(c, x, zero));
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, ten));
        let objective = Z3_optimize_maximize(c, o, x);

        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert!(!Z3_optimize_get_model(c, o).is_null());
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(9));

        // Registering a TC relation activates the optimize SAT trust gate. The
        // backend can still find/capture SAT and its objective value, but the
        // FFI must downgrade it and revoke both outcome surfaces.
        let bool_sort = Z3_mk_bool_sort(c);
        let relation_name =
            CString::new("R").expect("relation name must not contain an interior NUL");
        let relation = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, relation_name.as_ptr()),
            2,
            [bool_sort, bool_sort].as_ptr(),
            bool_sort,
        );
        assert!(!Z3_mk_transitive_closure(c, relation).is_null());
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_UNDEF);

        let reason = CStr::from_ptr(Z3_optimize_get_reason_unknown(c, o)).to_string_lossy();
        assert!(
            reason.contains("transitive-closure model verification"),
            "{reason}"
        );
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, objective), 0);
        assert_eq!(
            Z3_ast_vector_size(c, Z3_optimize_get_upper_as_vector(c, o, objective)),
            0
        );
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_unsat_core(c, o)), 0);

        Z3_del_context(c);
    }
}

#[test]
fn optimize_and_solver_handles_share_one_context() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        // z3py's default context mixes Solver and Optimize freely (measured:
        // `Z3_mk_optimize` used to fail once a Solver existed). A Solver check
        // resets the shared engine; the Optimize handle replays its state.
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        assert!(!o.is_null());
        // A second Optimize handle shares the context too (z3 allows any
        // number); it replays its own state, so it leaves `o`'s alone.
        let o2 = Z3_mk_optimize(c);
        assert!(!o2.is_null());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let x = int_var(c, "x");
        let int_sort = Z3_mk_int_sort(c);
        let k = |v: i32| Z3_mk_int(c, v, int_sort);
        Z3_optimize_assert(c, o, Z3_mk_ge(c, x, k(0)));
        Z3_optimize_push(c, o);
        Z3_optimize_assert(c, o, Z3_mk_le(c, x, k(10)));
        let objective = Z3_optimize_maximize(c, o, x);
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        let s = Z3_mk_solver(c);
        assert!(!s.is_null(), "a Solver may join an Optimize context");
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, k(-5)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);

        // The Optimize problem is unchanged by the Solver's goal x = -5.
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(10));
        // The optimum survives a later Solver check on the same context.
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(10));
        // Scopes replay too: popping the bound leaves x unbounded above.
        Z3_optimize_pop(c, o);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)), 1);
        Z3_optimize_assert(c, o, Z3_mk_le(c, x, k(3)));
        let objective = Z3_optimize_maximize(c, o, x);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(3));
        // And the Solver never sees the Optimize constraints.
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        // Parsed Optimize content is recorded on the handle like asserted
        // content (`parse_binding`), so it replays beside Solver handles.
        Z3_optimize_from_string(c, o, c"(assert true)".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(3));
        // Fixedpoint is intentionally compatible: it solves in its own CHC
        // engine and only reads the context term arena.
        assert!(!Z3_mk_fixedpoint(c).is_null());
        Z3_del_context(c);

        // Solver first, then Optimize.
        let c = mk_ctx();
        let s = Z3_mk_solver(c);
        assert!(!s.is_null());
        let o = Z3_mk_optimize(c);
        assert!(!o.is_null());
        let y = int_var(c, "y");
        let int_sort = Z3_mk_int_sort(c);
        Z3_solver_assert(c, s, Z3_mk_gt(c, y, Z3_mk_int(c, 100, int_sort)));
        Z3_optimize_assert(c, o, Z3_mk_le(c, y, Z3_mk_int(c, 7, int_sort)));
        let objective = Z3_optimize_maximize(c, o, y);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(7));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        Z3_del_context(c);

        // Parsed Optimize content is recorded on the handle, so a Solver may
        // join afterwards and the Optimize replays its parsed problem.
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        Z3_optimize_from_string(
            c,
            o,
            c"(declare-const z Int)(maximize z)(assert (< z 4))".as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let s = Z3_mk_solver(c);
        assert!(!s.is_null());
        let z = int_var(c, "z");
        Z3_solver_assert(c, s, Z3_mk_gt(c, z, Z3_mk_int(c, 100, Z3_mk_int_sort(c))));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, 0)), Some(3));
        Z3_del_context(c);
    }
}

#[test]
fn global_parser_leaves_an_optimize_problem_intact() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_true(c));

        let script = CString::new("(assert false)")
            .expect("SMT-LIB script must not contain an interior NUL");
        let parsed = Z3_parse_smtlib2_string(
            c,
            script.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_ast_vector_size(c, parsed), 1);
        // The parsed `false` is returned to the caller, never added to the
        // Optimize problem.
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        Z3_del_context(c);

        // A semantic global parse claims the ordinary solver family even when
        // no explicit solver handle has been created; Optimize may still join.
        let c = mk_ctx();
        let script =
            CString::new("(assert true)").expect("SMT-LIB script must not contain an interior NUL");
        let _ = Z3_parse_smtlib2_string(
            c,
            script.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(!Z3_mk_optimize(c).is_null());
        Z3_del_context(c);
    }
}

#[test]
fn optimize_parse_late_error_rolls_back_and_leaves_the_handle_usable() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let int_sort = Z3_mk_int_sort(c);
        let zero = Z3_mk_int(c, 0, int_sort);
        let ten = Z3_mk_int(c, 10, int_sort);
        Z3_optimize_assert(c, o, Z3_mk_ge(c, x, zero));
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, ten));
        let objective = Z3_optimize_maximize(c, o, x);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);

        let hard_before = Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o));
        let objectives_before = Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o));

        // The last command is well-formed syntax but semantically invalid, so
        // all preceding commands have already executed when it fails. The
        // bound parse runs inside a scope that is popped, so nothing of the
        // text remains: z3's parser error, and the handle as it was.
        let script = CString::new(
            "(declare-const y Int)\n\
             (assert (>= y 0))\n\
             (assert-soft true :weight 2)\n\
             (maximize y)\n\
             (assert 1)\n",
        )
        .expect("optimization script must not contain an interior NUL");
        Z3_optimize_from_string(c, o, script.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        assert_eq!(
            Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)),
            hard_before
        );
        assert_eq!(
            Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o)),
            objectives_before
        );
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(9));
        Z3_del_context(c);
    }
}

#[test]
fn optimize_parse_rejects_context_poison_and_open_user_scope() {
    unsafe {
        // Context poison is authoritative for parser entrypoints too.
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let before = Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o));
        (*c).decision_engine_poisoned = Some("test poison".to_string());
        Z3_optimize_from_string(c, o, c"(assert true)".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        assert_eq!(
            Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)),
            before
        );
        Z3_del_context(c);

        // A bound parse inside a user scope records its formulas at that
        // scope, as `Z3_optimize_assert` does, and the pop removes them.
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_true(c));
        Z3_optimize_push(c, o);
        Z3_optimize_from_string(c, o, c"(assert false)".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!((*o).scope_markers.len(), 1);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
        Z3_optimize_pop(c, o);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

#[test]
fn optimize_priority_param_is_validated_wired_and_retires_artifacts() {
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "priority_x");
        let int_sort = Z3_mk_int_sort(c);
        Z3_optimize_assert(c, o, Z3_mk_ge(c, x, Z3_mk_int(c, 0, int_sort)));
        Z3_optimize_assert(c, o, Z3_mk_le(c, x, Z3_mk_int(c, 10, int_sort)));
        let maximize_x = Z3_optimize_maximize(c, o, x);
        let minimize_x = Z3_optimize_minimize(c, o, x);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(
            numeral(c, Z3_optimize_get_upper(c, o, maximize_x)),
            Some(10)
        );
        assert_eq!(
            numeral(c, Z3_optimize_get_lower(c, o, minimize_x)),
            Some(10)
        );
        assert!(!Z3_optimize_get_model(c, o).is_null());

        // Invalid priority is rejected before mutation; the admitted previous
        // result remains a valid snapshot.
        let invalid = Z3_mk_params(c);
        Z3_params_set_symbol(
            c,
            invalid,
            Z3_mk_string_symbol(c, c"priority".as_ptr()),
            Z3_mk_string_symbol(c, c"bogus".as_ptr()),
        );
        Z3_optimize_set_params(c, o, invalid);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert!(!Z3_optimize_get_model(c, o).is_null());

        // Box is a real independent-objective policy, not a descriptor-only
        // compatibility key. A successful config change retires old results.
        let boxed = Z3_mk_params(c);
        Z3_params_set_symbol(
            c,
            boxed,
            Z3_mk_string_symbol(c, c"priority".as_ptr()),
            Z3_mk_string_symbol(c, c"box".as_ptr()),
        );
        Z3_optimize_set_params(c, o, boxed);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, maximize_x), 0);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(
            numeral(c, Z3_optimize_get_upper(c, o, maximize_x)),
            Some(10)
        );
        assert_eq!(numeral(c, Z3_optimize_get_lower(c, o, minimize_x)), Some(0));

        // The per-context update API reaches the same frontend option and
        // retires all copied decision artifacts.
        Z3_update_param_value(c, c"opt.priority".as_ptr(), c"lex".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(
            numeral(c, Z3_optimize_get_lower(c, o, minimize_x)),
            Some(10)
        );

        Z3_del_context(c);
    }
}

#[test]
fn optimize_translate_is_exclusive_and_preserves_soft_groups() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let source = mk_ctx();
        let source_opt = Z3_mk_optimize(source);
        let a = bool_var(source, "a");
        Z3_optimize_assert(source, source_opt, Z3_mk_true(source));
        let weight = CString::new("3").expect("soft weight must not contain an interior NUL");
        let group_name =
            CString::new("group_a").expect("group name must not contain an interior NUL");
        let group = Z3_mk_string_symbol(source, group_name.as_ptr());
        Z3_optimize_assert_soft(source, source_opt, a, weight.as_ptr(), group);

        assert!(Z3_optimize_translate(source, source_opt, source).is_null());
        assert_eq!(Z3_get_error_code(source), Z3_INVALID_USAGE);

        let target = mk_ctx();
        let translated = Z3_optimize_translate(source, source_opt, target);
        assert!(!translated.is_null());
        let rendered = CStr::from_ptr(Z3_optimize_to_string(target, translated)).to_string_lossy();
        assert!(rendered.contains(":id group_a"), "{rendered}");
        // `:id` is semantically a grouped objective. AY preserves it through
        // translation; one group is one MaxSMT objective, which it solves.
        assert_eq!(
            Z3_optimize_check(target, translated, 0, ptr::null()),
            Z3_L_TRUE
        );
        assert!(!Z3_optimize_get_model(target, translated).is_null());

        // Arithmetic objectives are rejected before claiming or mutating the
        // target, because they are not represented on OptimizeHandle yet.
        let x = int_var(source, "x");
        Z3_optimize_maximize(source, source_opt, x);
        let objective_target = mk_ctx();
        assert!(Z3_optimize_translate(source, source_opt, objective_target).is_null());
        assert_eq!(Z3_get_error_code(objective_target), Z3_INVALID_USAGE);
        assert!(!Z3_mk_optimize(objective_target).is_null());

        Z3_del_context(objective_target);
        Z3_del_context(target);
        Z3_del_context(source);
    }
}

#[test]
fn params_help_and_descrs() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);

        assert!(Z3_optimize_get_statistics(c, ptr::null_mut()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        // set_params honors `timeout`.
        let p = Z3_mk_params(c);
        let key = CString::new("timeout").expect("parameter name must not contain an interior NUL");
        Z3_params_set_uint(c, p, Z3_mk_string_symbol(c, key.as_ptr()), 5000);
        Z3_optimize_set_params(c, o, p);
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        // get_help is a real, non-empty string.
        let help = Z3_optimize_get_help(c, o);
        assert!(!help.is_null());
        assert_ne!(CStr::from_ptr(help).to_bytes(), &[] as &[u8]);

        // get_param_descrs is a real, queryable set.
        let pd = Z3_optimize_get_param_descrs(c, o);
        assert!(!pd.is_null());
        let n = Z3_param_descrs_size(c, pd);
        assert!(n >= 1);
        assert!(!Z3_param_descrs_to_string(c, pd).is_null());

        // Every descriptor resolves a name and a kind; at least one is UINT
        // (the `timeout` parameter).
        let mut found_uint = false;
        for i in 0..n {
            let name = Z3_param_descrs_get_name(c, pd, i);
            assert!(!name.is_null());
            let kind = Z3_param_descrs_get_kind(c, pd, name);
            assert_ne!(kind, Z3_PK_INVALID, "known descriptor must have a kind");
            if kind == Z3_PK_UINT {
                found_uint = true;
            }
        }
        assert!(found_uint, "expected a UINT-kinded parameter (timeout)");

        Z3_del_context(c);
    }
}

#[test]
fn honest_noops_do_not_crash() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        // set_initial_value: documented no-op (hint ignored, optimum unchanged).
        Z3_optimize_set_initial_value(c, o, x, zero);
        // register_model_eh: documented no-op (no callback hook).
        Z3_optimize_register_model_eh(c, o, ptr::null_mut(), ptr::null_mut(), None);
        Z3_del_context(c);
    }
}

/// An unbounded objective reports z3's objective-infinity AST from
/// `get_lower`/`get_upper` (measured libz3 5.1.0): `oo` / `-oo`
/// rendered `oo` / `(* (- 1) oo)` in libz3, app-kind, Int-sorted, not a
/// numeral, and equal across both accessors and repeated calls.
/// It is z3's `oo` constant term (DR-60): term building accepts it
/// as an ordinary Int constant, as libz3 does.
#[test]
fn unbounded_objective_reports_oo_ast() {
    // SAFETY: test-scope unsafe block; all handles are created here
    // and freed by `Z3_del_context`.
    unsafe {
        // AY's API multiplication normalizes `-1 * t` to its negation
        // node, so `-oo` renders `(- oo)` where libz3 renders
        // `(* (- 1) oo)` — the same rendering AY gives any negated
        // product built through the C API.
        for (minimize, want) in [(false, "oo"), (true, "(- oo)")] {
            let c = mk_ctx();
            let real_sort = Z3_mk_real_sort(c);
            let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), real_sort);
            let o = Z3_mk_optimize(c);
            if minimize {
                Z3_optimize_minimize(c, o, x);
            } else {
                Z3_optimize_maximize(c, o, x);
            }
            assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
            let lo = Z3_optimize_get_lower(c, o, 0);
            let up = Z3_optimize_get_upper(c, o, 0);
            assert_ne!(lo, 0);
            assert_eq!(lo, up, "both bounds are the optimum itself");
            let text = CStr::from_ptr(Z3_ast_to_string(c, lo))
                .to_str()
                .expect("utf8");
            assert_eq!(text, want);
            assert_eq!(Z3_get_ast_kind(c, lo), Z3_APP_AST);
            assert!(!Z3_is_numeral_ast(c, lo));
            let sort = Z3_get_sort(c, lo);
            assert!(!sort.is_null());
            let sort_text = CStr::from_ptr(Z3_sort_to_string(c, sort))
                .to_str()
                .expect("utf8");
            assert_eq!(sort_text, "Int");
            // Term building accepts `oo` as an ordinary Int constant
            // (libz3: `Z3_mk_add(oo, 1)` succeeds, rendering
            // `(+ oo 1)`); it is a free Int to every decision
            // procedure, so no verdict can rest on it (DR-60).
            let one = Z3_mk_numeral(c, c"1".as_ptr(), Z3_mk_int_sort(c));
            let args = [lo, one];
            let sum = Z3_mk_add(c, 2, args.as_ptr());
            assert_ne!(sum, 0);
            let sum_text = CStr::from_ptr(Z3_ast_to_string(c, sum))
                .to_str()
                .expect("utf8");
            assert!(sum_text.contains("oo"), "sum over oo: {sum_text}");
            Z3_del_context(c);
        }
    }
}
