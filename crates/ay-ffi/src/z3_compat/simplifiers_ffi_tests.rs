// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible simplifier C API (`simplifiers.rs`).
//!
//! Coverage:
//! - `Z3_mk_simplifier` builds every supported name; an unknown name (and a
//!   tactic-only control name like `skip`/`split-clause`, which is NOT a
//!   simplifier) returns NULL + `Z3_INVALID_ARG` (honest).
//! - `Z3_simplifier_and_then` / `Z3_simplifier_using_params` compose; null
//!   operands error.
//! - `Z3_simplifier_get_descr` returns a real per-name string; unknown -> NULL.
//! - `Z3_simplifier_get_help` / `Z3_simplifier_get_param_descrs` are real
//!   (non-null / honest-empty) and validate their handle.
//! - inc_ref/dec_ref are bookkeeping no-ops.
//! - SOUNDNESS: a solver with a `solve-eqs and_then propagate-values` simplifier
//!   attached gives the SAME verdict as a plain solver on SAT and UNSAT LIA goals
//!   and yields a usable model — the acceptance criterion.

use super::super::*;
use std::ffi::{CStr, CString};
use std::ptr::{null, null_mut};

/// Assert the LIA goal `{x = y + 1, y = 2, x > 2}` (SAT: x = 3) on `s`.
/// Returns the `x` const AST for model checks.
///
/// # Safety
/// `ctx`/`s` must be valid handles allocated by this test module.
unsafe fn assert_lia_sat(ctx: Z3_context, s: Z3_solver) -> Z3_ast {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let is = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), is);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), is);
        let one = Z3_mk_int(ctx, 1, is);
        let two = Z3_mk_int(ctx, 2, is);
        let add_args = [y, one];
        let yp1 = Z3_mk_add(ctx, 2, add_args.as_ptr());
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, yp1));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, y, two));
        Z3_solver_assert(ctx, s, Z3_mk_gt(ctx, x, two));
        x
    }
}

/// Assert the LIA goal `{x = y + 1, y = 2, x < 3}` (UNSAT: x would be 3) on `s`.
///
/// # Safety
/// `ctx`/`s` must be valid handles allocated by this test module.
unsafe fn assert_lia_unsat(ctx: Z3_context, s: Z3_solver) {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let is = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), is);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), is);
        let one = Z3_mk_int(ctx, 1, is);
        let two = Z3_mk_int(ctx, 2, is);
        let three = Z3_mk_int(ctx, 3, is);
        let add_args = [y, one];
        let yp1 = Z3_mk_add(ctx, 2, add_args.as_ptr());
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, yp1));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, y, two));
        Z3_solver_assert(ctx, s, Z3_mk_lt(ctx, x, three));
    }
}

/// Every supported simplifier name builds; tactic-only names and an
/// unknown name are honestly rejected with NULL + `Z3_INVALID_ARG`.
#[test]
fn test_mk_simplifier_supported_and_rejected_names() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        for name in SUPPORTED_SIMPLIFIER_NAMES {
            let cname = CString::new(*name).expect("reference name must be a valid C string");
            let simp = Z3_mk_simplifier(ctx, cname.as_ptr());
            assert!(!simp.is_null(), "supported simplifier {name} should build");
            assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        }

        // `elim-and` and `nnf` were AY-only registry entries. They are tactics,
        // but Z3 5.0.0 does not expose them as simplifiers.
        for name in ["elim-and", "nnf", "skip", "fail", "split-clause", "cnf"] {
            let cname = CString::new(name).expect("test name must be a valid C string");
            let bad = Z3_mk_simplifier(ctx, cname.as_ptr());
            assert!(
                bad.is_null(),
                "{name} is not a simplifier and must be rejected"
            );
            assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        }

        // Genuinely unknown name and null name -> honest NULL + error.
        let unk = Z3_mk_simplifier(ctx, c"definitely-not-a-simplifier".as_ptr());
        assert!(unk.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        let nul = Z3_mk_simplifier(ctx, null());
        assert!(nul.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// Construction parity is not enough: every catalog entry must also be
/// attachable and preserve an elementary UNSAT verdict. This exercises aliases
/// and conservative identity implementations through the real solver path.
#[test]
fn test_every_z3_5_simplifier_preserves_boolean_smoke_verdict() {
    // SAFETY: all handles are arena-owned by `ctx` and used single-threadedly.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let p = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"p".as_ptr()), bool_sort);
        let not_p = Z3_mk_not(ctx, p);

        for name in SUPPORTED_SIMPLIFIER_NAMES {
            let cname = CString::new(*name).expect("reference name must be a valid C string");
            let simplifier = Z3_mk_simplifier(ctx, cname.as_ptr());
            assert!(!simplifier.is_null(), "{name} must build");
            let plain = Z3_mk_solver(ctx);
            let solver = Z3_solver_add_simplifier(ctx, plain, simplifier);
            assert!(!solver.is_null(), "{name} must attach to a solver");
            Z3_solver_assert(ctx, solver, p);
            Z3_solver_assert(ctx, solver, not_p);
            assert_eq!(
                Z3_solver_check(ctx, solver),
                Z3_L_FALSE,
                "{name} must preserve the contradictory Boolean goal"
            );
        }

        Z3_del_context(ctx);
    }
}

/// `Z3_simplifier_and_then` / `Z3_simplifier_using_params` compose; null operands
/// error.
#[test]
fn test_simplifier_combinators() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s1 = Z3_mk_simplifier(ctx, c"solve-eqs".as_ptr());
        let s2 = Z3_mk_simplifier(ctx, c"propagate-values".as_ptr());
        assert!(!s1.is_null() && !s2.is_null());

        let comp = Z3_simplifier_and_then(ctx, s1, s2);
        assert!(!comp.is_null(), "and_then should compose");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        // Nested composition is also fine.
        let nested = Z3_simplifier_and_then(ctx, comp, s1);
        assert!(!nested.is_null());

        let params = Z3_mk_params(ctx);
        let with = Z3_simplifier_using_params(ctx, comp, params);
        assert!(!with.is_null(), "using-params should compose");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        // Null operands -> NULL + Z3_INVALID_ARG.
        let bad = Z3_simplifier_and_then(ctx, s1, null_mut());
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        let bad2 = Z3_simplifier_using_params(ctx, null_mut(), params);
        assert!(bad2.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// inc_ref/dec_ref are bookkeeping no-ops and never crash.
#[test]
fn test_simplifier_inc_dec_ref_noop() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = Z3_mk_simplifier(ctx, c"solve-eqs".as_ptr());
        Z3_simplifier_inc_ref(ctx, s);
        Z3_simplifier_inc_ref(ctx, s);
        Z3_simplifier_dec_ref(ctx, s);
        Z3_simplifier_dec_ref(ctx, s);
        // Extra dec is still a no-op (no early free, no error fabrication).
        Z3_simplifier_dec_ref(ctx, s);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// `Z3_simplifier_get_descr` returns a real per-name string; unknown -> NULL +
/// error.
#[test]
fn test_simplifier_get_descr() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        for name in SUPPORTED_SIMPLIFIER_NAMES {
            let cname = CString::new(*name).expect("reference name must be a valid C string");
            let d = Z3_simplifier_get_descr(ctx, cname.as_ptr());
            assert!(
                !d.is_null(),
                "supported simplifier {name} must have a description"
            );
            let s = CStr::from_ptr(d).to_string_lossy();
            assert!(!s.is_empty(), "description must be a non-empty real string");
            assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        }

        // Unknown name -> NULL + Z3_INVALID_ARG (honest).
        let bad = Z3_simplifier_get_descr(ctx, c"not-a-real-simplifier".as_ptr());
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// `Z3_simplifier_get_help` is a real non-empty string; `Z3_simplifier_get_param_descrs`
/// is a REAL honest-empty (size 0) descriptor set. Both validate their handle.
#[test]
fn test_simplifier_get_help_and_param_descrs() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = Z3_mk_simplifier(ctx, c"solve-eqs".as_ptr());

        let help = Z3_simplifier_get_help(ctx, s);
        assert!(!help.is_null());
        let hs = CStr::from_ptr(help).to_string_lossy();
        assert!(!hs.is_empty(), "help must be a non-empty real string");
        assert!(hs.contains("solve-eqs"), "help should list solve-eqs: {hs}");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let pd = Z3_simplifier_get_param_descrs(ctx, s);
        assert!(
            !pd.is_null(),
            "param descrs handle must be a real (non-null) set"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!(
            Z3_param_descrs_size(ctx, pd),
            0,
            "ay simplifiers expose no per-simplifier params (honest empty)"
        );

        // Null handle -> NULL + Z3_INVALID_ARG.
        let bh = Z3_simplifier_get_help(ctx, null_mut());
        assert!(bh.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        let bp = Z3_simplifier_get_param_descrs(ctx, null_mut());
        assert!(bp.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// SOUNDNESS (acceptance): a solver with a `solve-eqs and_then propagate-values`
/// simplifier attached gives the SAME SAT verdict as a plain solver on the LIA
/// goal, and still produces a model on SAT.
///
/// The returned model must satisfy every ORIGINAL assertion, including values
/// of variables a pass may eliminate. Verdict preservation alone is insufficient.
#[test]
fn test_add_simplifier_preserves_sat_verdict_and_model() {
    // SAFETY: see above.
    unsafe {
        // Plain baseline.
        let cfg_b = Z3_mk_config();
        let ctx_b = Z3_mk_context(cfg_b);
        Z3_del_config(cfg_b);
        let s_b = Z3_mk_solver(ctx_b);
        let _ = assert_lia_sat(ctx_b, s_b);
        let base = Z3_solver_check(ctx_b, s_b);
        assert_eq!(base, Z3_L_TRUE, "baseline LIA goal should be SAT");
        Z3_del_context(ctx_b);

        // Simplifier path: attach solve-eqs and_then propagate-values.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let plain = Z3_mk_solver(ctx);
        let se = Z3_mk_simplifier(ctx, c"solve-eqs".as_ptr());
        let pv = Z3_mk_simplifier(ctx, c"propagate-values".as_ptr());
        let comp = Z3_simplifier_and_then(ctx, se, pv);
        let s = Z3_solver_add_simplifier(ctx, plain, comp);
        assert!(!s.is_null(), "add_simplifier must return a solver");
        assert!(
            s != plain,
            "add_simplifier returns a NEW solver (matches z3)"
        );

        let _x = assert_lia_sat(ctx, s);
        let original = Z3_solver_get_assertions(ctx, s);
        Z3_ast_vector_inc_ref(ctx, original);
        let res = Z3_solver_check(ctx, s);
        assert_eq!(res, base, "simplifier verdict must equal baseline verdict");

        let model = Z3_solver_get_model(ctx, s);
        assert!(
            !model.is_null(),
            "simplifier solver must produce a model on SAT"
        );
        for index in 0..Z3_ast_vector_size(ctx, original) {
            let mut value: Z3_ast = 0;
            assert!(Z3_model_eval(
                ctx,
                model,
                Z3_ast_vector_get(ctx, original, index),
                true,
                &raw mut value,
            ));
            assert_eq!(Z3_get_bool_value(ctx, value), Z3_L_TRUE);
        }
        Z3_ast_vector_dec_ref(ctx, original);

        Z3_del_context(ctx);
    }
}

/// SOUNDNESS (acceptance): the same attached simplifier preserves an UNSAT
/// verdict; and null operands to `Z3_solver_add_simplifier` are honest errors.
#[test]
fn test_add_simplifier_preserves_unsat_and_null_errors() {
    // SAFETY: see above.
    unsafe {
        // Plain baseline.
        let cfg_b = Z3_mk_config();
        let ctx_b = Z3_mk_context(cfg_b);
        Z3_del_config(cfg_b);
        let s_b = Z3_mk_solver(ctx_b);
        assert_lia_unsat(ctx_b, s_b);
        let base = Z3_solver_check(ctx_b, s_b);
        assert_eq!(base, Z3_L_FALSE, "baseline LIA goal should be UNSAT");
        Z3_del_context(ctx_b);

        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let plain = Z3_mk_solver(ctx);
        let se = Z3_mk_simplifier(ctx, c"solve-eqs".as_ptr());
        let pv = Z3_mk_simplifier(ctx, c"propagate-values".as_ptr());
        let comp = Z3_simplifier_and_then(ctx, se, pv);
        let s = Z3_solver_add_simplifier(ctx, plain, comp);
        assert!(!s.is_null());
        assert_lia_unsat(ctx, s);
        let res = Z3_solver_check(ctx, s);
        assert_eq!(
            res, base,
            "simplifier verdict must equal baseline UNSAT verdict"
        );

        // Null solver / null simplifier -> NULL + Z3_INVALID_ARG.
        let bad1 = Z3_solver_add_simplifier(ctx, null_mut(), comp);
        assert!(bad1.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        let bad2 = Z3_solver_add_simplifier(ctx, plain, null_mut());
        assert!(bad2.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

include!("simplifiers_ffi_tests/registry_enumeration.rs");

#[test]
fn converted_solver_reconstructs_source_values_across_scopes_and_assumptions() {
    // SAFETY: every C handle belongs to this live, single-threaded context.
    unsafe {
        for attached in [true, false] {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            let solver = if attached {
                let se = Z3_mk_simplifier(ctx, c"solve-eqs".as_ptr());
                let pv = Z3_mk_simplifier(ctx, c"propagate-values".as_ptr());
                let comp = Z3_simplifier_and_then(ctx, se, pv);
                Z3_solver_add_simplifier(ctx, Z3_mk_solver(ctx), comp)
            } else {
                let se = Z3_mk_tactic(ctx, c"solve-eqs".as_ptr());
                let pv = Z3_mk_tactic(ctx, c"propagate-values".as_ptr());
                Z3_mk_solver_from_tactic(ctx, Z3_tactic_and_then(ctx, se, pv))
            };
            assert!(!solver.is_null());
            let x = assert_lia_sat(ctx, solver);
            let three = Z3_mk_int(ctx, 3, Z3_mk_int_sort(ctx));
            let original_value = Z3_mk_eq(ctx, x, three);
            assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
            let snapshot = Z3_solver_get_model(ctx, solver);
            let mut value = 0;
            assert!(Z3_model_eval(
                ctx,
                snapshot,
                original_value,
                false,
                &raw mut value
            ));
            assert_eq!(Z3_get_bool_value(ctx, value), Z3_L_TRUE);
            Z3_solver_push(ctx, solver);
            Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, original_value));
            assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
            assert!(Z3_solver_get_model(ctx, solver).is_null());
            Z3_solver_pop(ctx, solver, 1);
            assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
            let impossible = Z3_mk_not(ctx, original_value);
            assert_eq!(
                Z3_solver_check_assumptions(ctx, solver, 1, &raw const impossible),
                Z3_L_FALSE
            );
            let core = Z3_solver_get_unsat_core(ctx, solver);
            assert!(!core.is_null());
            assert_eq!(Z3_ast_vector_size(ctx, core), 1);
            assert!(Z3_is_eq_ast(
                ctx,
                Z3_ast_vector_get(ctx, core, 0),
                impossible
            ));
            // Independently decide the original source with only returned
            // assumptions: the core must not be an empty reduced-core alias.
            let replay = Z3_mk_solver(ctx);
            let source = Z3_solver_get_assertions(ctx, solver);
            for index in 0..Z3_ast_vector_size(ctx, source) {
                Z3_solver_assert(ctx, replay, Z3_ast_vector_get(ctx, source, index));
            }
            for index in 0..Z3_ast_vector_size(ctx, core) {
                Z3_solver_assert(ctx, replay, Z3_ast_vector_get(ctx, core, index));
            }
            assert_eq!(Z3_solver_check(ctx, replay), Z3_L_FALSE);
            assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
            assert!(Z3_model_eval(
                ctx,
                snapshot,
                original_value,
                false,
                &raw mut value
            ));
            assert_eq!(Z3_get_bool_value(ctx, value), Z3_L_TRUE);
            Z3_del_context(ctx);
        }
    }
}

#[test]
fn converted_field_sat_solver_reads_the_actual_authored_boolean_and_field_witness() {
    // SAFETY: all handles are owned by this live single-threaded context.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let tactic = Z3_mk_tactic(ctx, c"ff-sat".as_ptr());
        let solver = Z3_mk_solver_from_tactic(ctx, tactic);
        Z3_solver_from_string(ctx, solver, c"(declare-const p Bool) (declare-const x (_ FiniteField 7)) (assert p) (assert (= x #f3m7))".as_ptr());
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        let roots = Z3_solver_get_assertions(ctx, solver);
        assert_eq!(Z3_ast_vector_size(ctx, roots), 2);
        let equality = Z3_to_app(ctx, Z3_ast_vector_get(ctx, roots, 1));
        let x = Z3_get_app_arg(ctx, equality, 0);
        let three = Z3_get_app_arg(ctx, equality, 1);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());
        let mut value = 0;
        assert!(Z3_model_eval(ctx, model, x, false, &raw mut value));
        assert!(Z3_is_eq_ast(ctx, value, three));
        assert!(Z3_model_eval(
            ctx,
            model,
            Z3_ast_vector_get(ctx, roots, 0),
            false,
            &raw mut value
        ));
        assert_eq!(Z3_get_bool_value(ctx, value), Z3_L_TRUE);
        Z3_solver_push(ctx, solver);
        Z3_solver_assert(
            ctx,
            solver,
            Z3_mk_not(ctx, Z3_ast_vector_get(ctx, roots, 1)),
        );
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        Z3_solver_pop(ctx, solver, 1);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(Z3_model_eval(ctx, model, x, false, &raw mut value));
        assert!(Z3_is_eq_ast(ctx, value, three));
        Z3_del_context(ctx);
    }
}
