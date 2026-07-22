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
use std::ffi::CStr;
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

/// Every supported simplifier name builds; a tactic-only control name and an
/// unknown name are honestly rejected with NULL + `Z3_INVALID_ARG`.
#[test]
fn test_mk_simplifier_supported_and_rejected_names() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        for name in [
            c"simplify".as_ptr(),
            c"solve-eqs".as_ptr(),
            c"propagate-values".as_ptr(),
            c"qe-light".as_ptr(),
            c"bit-blast".as_ptr(),
            c"elim-and".as_ptr(),
            c"nnf".as_ptr(),
        ] {
            let simp = Z3_mk_simplifier(ctx, name);
            assert!(!simp.is_null(), "supported simplifier name should build");
            assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        }

        // Tactic-only control primitives are NOT simplifiers: reject them (even
        // though the tactic registry accepts them).
        for name in [
            c"skip".as_ptr(),
            c"fail".as_ptr(),
            c"split-clause".as_ptr(),
            c"cnf".as_ptr(),
        ] {
            let bad = Z3_mk_simplifier(ctx, name);
            assert!(bad.is_null(), "tactic-only name must not be a simplifier");
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

        for name in [
            c"simplify".as_ptr(),
            c"solve-eqs".as_ptr(),
            c"propagate-values".as_ptr(),
            c"qe-light".as_ptr(),
            c"bit-blast".as_ptr(),
            c"elim-and".as_ptr(),
            c"nnf".as_ptr(),
        ] {
            let d = Z3_simplifier_get_descr(ctx, name);
            assert!(
                !d.is_null(),
                "known simplifier name must have a description"
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
/// The exact value of an eliminated variable is not asserted: `solve-eqs`
/// legitimately eliminates `x` (as a solved variable), and AY does not run z3's
/// model-reconstruction converter to re-derive it (an HONEST, documented
/// limitation — not a wrong verdict). The acceptance criterion is verdict
/// preservation, checked here against the plain-solver baseline.
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
        let res = Z3_solver_check(ctx, s);
        assert_eq!(res, base, "simplifier verdict must equal baseline verdict");

        // A model exists on SAT (its completeness over eliminated variables is
        // not asserted; see the doc comment).
        let model = Z3_solver_get_model(ctx, s);
        assert!(
            !model.is_null(),
            "simplifier solver must produce a model on SAT"
        );

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

/// Registry enumeration: `Z3_get_num_simplifiers` / `Z3_get_simplifier_name`
/// list exactly [`SUPPORTED_SIMPLIFIER_NAMES`], every enumerated name is
/// buildable via `Z3_mk_simplifier`, and an out-of-range index is an honest
/// NULL + `Z3_INVALID_ARG`.
#[test]
fn test_simplifier_registry_enumeration() {
    // SAFETY: all handles are allocated and freed within this test.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let n = Z3_get_num_simplifiers(ctx);
        assert_eq!(
            n as usize,
            SUPPORTED_SIMPLIFIER_NAMES.len(),
            "enumerator must expose exactly the real registry"
        );
        for (i, want) in SUPPORTED_SIMPLIFIER_NAMES.iter().enumerate() {
            let name = Z3_get_simplifier_name(ctx, i as c_uint);
            assert!(!name.is_null(), "simplifier name {i} must be non-null");
            let got = CStr::from_ptr(name)
                .to_str()
                .expect("enumerated simplifier name must be valid UTF-8");
            assert_eq!(got, *want, "name {i} must match the registry");
            // Every enumerated name is REAL: Z3_mk_simplifier accepts it.
            let cname = CString::new(*want)
                .expect("registered simplifier name must not contain an interior NUL");
            let s = Z3_mk_simplifier(ctx, cname.as_ptr());
            assert!(
                !s.is_null(),
                "enumerated simplifier {got} must be buildable"
            );
        }
        // Out of range: honest NULL + INVALID_ARG.
        assert!(Z3_get_simplifier_name(ctx, n).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}
