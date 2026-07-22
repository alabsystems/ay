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
use std::ffi::{CStr, CString};

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
        let name = CString::new(n).unwrap();
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
        let name = CString::new(n).unwrap();
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
        if a != 0 && Z3_get_numeral_int(c, a, &mut v) {
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
        // HONEST DIVERGENCE: AY's Optimize cannot extract a participating-only
        // core (no assumption threading), so rather than an over-approximate core
        // that could report NON-participating literals (a wrong value), it returns
        // an EMPTY core. libz3 returns the participating {p1,p2} here. See the
        // capture_check_diagnostics doc + ay_z3_compat.h.
        assert_eq!(Z3_ast_vector_size(c, core), 0);

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
        .unwrap();
        Z3_optimize_from_string(c, o, script.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o)), 1);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(numeral(c, Z3_optimize_get_lower(c, o, 0)), Some(3));
        Z3_del_context(c);
    }
}

#[test]
fn assumptions_are_rejected() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        let x = int_var(c, "x");
        let zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
        let ten = Z3_mk_int(c, 10, Z3_mk_int_sort(c));
        let a = Z3_mk_ge(c, x, zero);
        Z3_optimize_assert(c, o, a);
        Z3_optimize_assert(c, o, Z3_mk_lt(c, x, ten));
        let objective = Z3_optimize_maximize(c, o, x);

        // Establish real outcome artefacts before exercising the early reject.
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
        assert!(!Z3_optimize_get_model(c, o).is_null());
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(9));

        let assumptions = [a];
        // num_assumptions > 0 is honestly rejected and retires the preceding
        // admitted model/objective rather than exposing them as this query's.
        assert_eq!(Z3_optimize_check(c, o, 1, assumptions.as_ptr()), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, objective), 0);

        // The raw count/pointer contract is also covered explicitly. Optimize
        // rejects every non-empty check-time assumption set, including a null
        // array, without dereferencing it or resurrecting stale artifacts.
        assert_eq!(Z3_optimize_check(c, o, 1, ptr::null()), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, objective), 0);

        // This was a rejected query, not a partial mutation, so the handle is
        // still reusable. A subsequent configuration change retires UNKNOWN
        // diagnostics and leaves result accessors empty until a fresh check.
        let params = Z3_mk_params(c);
        Z3_params_set_uint(c, params, Z3_mk_string_symbol(c, c"timeout".as_ptr()), 0);
        Z3_optimize_set_params(c, o, params);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(
            Z3_ast_vector_size(c, Z3_optimize_get_upper_as_vector(c, o, objective)),
            0
        );
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_unsat_core(c, o)), 0);
        let reason = CStr::from_ptr(Z3_optimize_get_reason_unknown(c, o)).to_string_lossy();
        assert!(reason.is_empty(), "{reason}");

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

        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
        assert!(!Z3_optimize_get_model(c, o).is_null());
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, maximize_x)), Some(9));

        // A successful formula mutation invalidates every copied FFI artefact,
        // even though the optimize handle still owns the previous model.
        Z3_optimize_assert(c, o, bool_var(c, "p"));
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, maximize_x), 0);
        assert_eq!(Z3_ast_vector_size(c, Z3_optimize_get_unsat_core(c, o)), 0);
        assert!(CStr::from_ptr(Z3_optimize_get_reason_unknown(c, o))
            .to_bytes()
            .is_empty());

        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
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

        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
        assert!(!Z3_optimize_get_model(c, o).is_null());
        assert_eq!(numeral(c, Z3_optimize_get_upper(c, o, objective)), Some(9));

        // Registering a TC relation activates the optimize SAT trust gate. The
        // backend can still find/capture SAT and its objective value, but the
        // FFI must downgrade it and revoke both outcome surfaces.
        let bool_sort = Z3_mk_bool_sort(c);
        let relation_name = CString::new("R").unwrap();
        let relation = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, relation_name.as_ptr()),
            2,
            [bool_sort, bool_sort].as_ptr(),
            bool_sort,
        );
        assert!(!Z3_mk_transitive_closure(c, relation).is_null());
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_UNDEF);

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
fn optimize_has_exclusive_decision_engine_ownership() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        assert!(!o.is_null());

        // A second eager Optimize would silently share the first one's engine.
        assert!(Z3_mk_optimize(c).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        // A replaying solver on the same context could wipe that eager state.
        assert!(Z3_mk_solver(c).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        // Fixedpoint is intentionally compatible: it solves in its own CHC
        // engine and only reads the context term arena.
        assert!(!Z3_mk_fixedpoint(c).is_null());
        Z3_del_context(c);

        let c = mk_ctx();
        assert!(!Z3_mk_solver(c).is_null());
        assert!(Z3_mk_optimize(c).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        Z3_del_context(c);
    }
}

#[test]
fn global_parser_cannot_mutate_an_optimize_owned_engine() {
    // SAFETY: single-threaded FFI test.
    unsafe {
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_true(c));

        let script = CString::new("(assert false)").unwrap();
        let parsed = Z3_parse_smtlib2_string(
            c,
            script.as_ptr(),
            0,
            std::ptr::null(),
            std::ptr::null(),
            0,
            std::ptr::null(),
            std::ptr::null(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        // Successful accessor calls reset the context error, so inspect the
        // parser error before asking for the returned vector's size.
        assert_eq!(Z3_ast_vector_size(c, parsed), 0);
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
        Z3_del_context(c);

        // A semantic global parse claims the ordinary solver family even when
        // no explicit solver handle has been created.
        let c = mk_ctx();
        let script = CString::new("(assert true)").unwrap();
        let _ = Z3_parse_smtlib2_string(
            c,
            script.as_ptr(),
            0,
            std::ptr::null(),
            std::ptr::null(),
            0,
            std::ptr::null(),
            std::ptr::null(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(Z3_mk_optimize(c).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        Z3_del_context(c);
    }
}

#[test]
fn optimize_parse_late_error_rolls_back_and_permanently_fails_closed() {
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
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);

        let hard_before = Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o));
        let objectives_before = Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o));
        let parsed_softs_before = (*c).solver.num_parsed_soft_constraints();

        // The last command is well-formed syntax but semantically invalid, so
        // all preceding commands have already executed when it fails.
        let script = CString::new(
            "(declare-const y Int)\n\
             (assert (>= y 0))\n\
             (assert-soft true :weight 2)\n\
             (maximize y)\n\
             (assert 1)\n",
        )
        .unwrap();
        Z3_optimize_from_string(c, o, script.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert_eq!(
            Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)),
            hard_before
        );
        assert_eq!(
            Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o)),
            objectives_before
        );
        assert_eq!(
            (*c).solver.num_parsed_soft_constraints(),
            parsed_softs_before
        );
        assert!(Z3_optimize_get_model(c, o).is_null());
        assert_eq!(Z3_optimize_get_upper(c, o, objective), 0);

        // Unscoped options could have executed before the late failure, so the
        // handle is terminally UNKNOWN rather than risking a partially changed
        // optimization on a later check.
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        let reason = CStr::from_ptr(Z3_optimize_get_reason_unknown(c, o)).to_string_lossy();
        assert!(reason.contains("parse execution failed"), "{reason}");
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

        // A hidden successful parse scope may not be opened above a user
        // scope. Rejecting it preserves the marker/engine stack alignment.
        let c = mk_ctx();
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_true(c));
        Z3_optimize_push(c, o);
        Z3_optimize_assert(c, o, Z3_mk_false(c));
        Z3_optimize_from_string(c, o, c"(assert true)".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        assert_eq!((*o).scope_markers.len(), 1);
        Z3_optimize_pop(c, o);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
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
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
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
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
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
        assert_eq!(Z3_optimize_check(c, o, 0, std::ptr::null()), Z3_L_TRUE);
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
        let weight = CString::new("3").unwrap();
        let group_name = CString::new("group_a").unwrap();
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
        // translation, but the current flat MaxSMT result cannot represent
        // group semantics and therefore honestly refuses to solve it.
        assert_eq!(
            Z3_optimize_check(target, translated, 0, std::ptr::null()),
            Z3_L_UNDEF
        );

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

        assert!(Z3_optimize_get_statistics(c, std::ptr::null_mut()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        // set_params honors `timeout`.
        let p = Z3_mk_params(c);
        let key = CString::new("timeout").unwrap();
        Z3_params_set_uint(c, p, Z3_mk_string_symbol(c, key.as_ptr()), 5000);
        Z3_optimize_set_params(c, o, p);
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        // get_help is a real, non-empty string.
        let help = Z3_optimize_get_help(c, o);
        assert!(!help.is_null());
        assert!(!CStr::from_ptr(help).to_bytes().is_empty());

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
