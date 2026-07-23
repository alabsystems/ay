// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible proof production/retrieval surface
//! (#phase3-proof).
//!
//! Honesty is the load-bearing property under test:
//! - UNSAT + proofs enabled  -> non-null handle, real Alethe text (rule markers)
//! - SAT + proofs enabled     -> NULL (never a proof for a SAT result)
//! - UNSAT + proofs disabled  -> NULL (never a proof when production is off)
//!
//! The UNSAT instance is the Boolean contradiction `p AND (not p)`, the same
//! known-good proof path used by the ay-dpll API proof tests.

use std::ffi::{c_char, CStr};

use crate::z3_compat::*;

/// Build a fresh context + solver and assert `p` and `(not p)` (an UNSAT
/// Boolean contradiction). Returns `(ctx, solver)`; the caller owns `ctx` and
/// must `Z3_del_context` it.
///
/// # Safety
/// Test-only helper; the returned context must be freed exactly once.
unsafe fn unsat_context() -> (Z3_context, Z3_solver) {
    // SAFETY: all handles are produced by the `Z3_mk_*` calls below and live in
    // the context arena; no pointer escapes beyond the returned context.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"p".as_ptr());
        let p = Z3_mk_const(ctx, sym, bool_sort);
        let not_p = Z3_mk_not(ctx, p);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, p);
        Z3_solver_assert(ctx, solver, not_p);
        (ctx, solver)
    }
}

/// Read a context-owned C string handle into an owned `String` (panics if null).
///
/// # Safety
/// `ptr` must be a valid, null-terminated, context-owned C string.
unsafe fn cstr_to_string(ptr: *const c_char) -> String {
    assert!(!ptr.is_null(), "expected non-null C string");
    // SAFETY: caller guarantees `ptr` is a valid context-owned C string.
    unsafe { CStr::from_ptr(ptr) }
        .to_str()
        .expect("proof text is valid UTF-8")
        .to_string()
}

/// Assert that the rendered text looks like a real Alethe proof: it must carry
/// at least one of the structural rule markers the exporter emits.
fn assert_looks_like_alethe(text: &str) {
    assert!(!text.is_empty(), "proof text must be non-empty");
    assert!(
        text.contains("assume") || text.contains("step") || text.contains("(cl"),
        "proof text must contain Alethe rule markers (assume/step/cl), got:\n{text}"
    );
    // It must NOT be the generic placeholder or an error sexpr.
    assert!(
        !text.starts_with("(ast "),
        "proof handle stringified to the generic AST placeholder, not Alethe text:\n{text}"
    );
    assert!(
        !text.starts_with("(error"),
        "proof export returned an error sexpr instead of a proof:\n{text}"
    );
}

/// UNSAT + proofs enabled: `Z3_solver_get_proof` returns a non-null handle whose
/// `Z3_ast_to_string` is the real Alethe proof.
#[test]
fn proof_unsat_enabled_returns_alethe() {
    // SAFETY: see `unsat_context`; the context is freed at the end of the block.
    unsafe {
        let (ctx, solver) = unsat_context();
        Z3_solver_set_proof_production(ctx, solver, true);
        assert!(Z3_solver_get_proof_production(ctx, solver));

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let proof = Z3_solver_get_proof(ctx, solver);
        assert_ne!(proof, 0, "expected a non-null proof handle for UNSAT");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        // The handle must carry the proof tag and never alias a real term.
        assert_ne!(proof & PROOF_AST_TAG, 0, "proof handle must carry the tag");

        let text = cstr_to_string(Z3_ast_to_string(ctx, proof));
        assert_looks_like_alethe(&text);

        Z3_del_context(ctx);
    }
}

#[test]
fn proof_handles_are_authenticated_to_their_context() {
    // SAFETY: each proof and solver stays live until its owning context is
    // deleted at the end of the block.
    unsafe {
        let (local, local_solver) = unsat_context();
        let (foreign, foreign_solver) = unsat_context();
        Z3_solver_set_proof_production(local, local_solver, true);
        Z3_solver_set_proof_production(foreign, foreign_solver, true);
        assert_eq!(Z3_solver_check(local, local_solver), Z3_L_FALSE);
        assert_eq!(Z3_solver_check(foreign, foreign_solver), Z3_L_FALSE);

        assert_eq!(Z3_solver_get_proof(local, foreign_solver), 0);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        let local_proof = Z3_solver_get_proof(local, local_solver);
        let foreign_proof = Z3_solver_get_proof(foreign, foreign_solver);
        assert_ne!(local_proof, 0);
        assert_ne!(foreign_proof, 0);
        assert_eq!(
            local_proof & TAGGED_AST_INDEX_MASK,
            foreign_proof & TAGGED_AST_INDEX_MASK,
            "fixture must exercise colliding proof-arena indices"
        );
        assert_ne!(local_proof, foreign_proof);

        assert!(proof_text_for_ast(&*local, foreign_proof).is_none());
        assert!(Z3_ast_to_string(local, foreign_proof).is_null());
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert_looks_like_alethe(&cstr_to_string(Z3_ast_to_string(local, local_proof)));

        Z3_del_context(foreign);
        Z3_del_context(local);
    }
}

/// UNSAT + proofs enabled: `Z3_solver_get_proof_string` yields the same kind of
/// real Alethe text directly.
#[test]
fn proof_string_unsat_enabled_returns_alethe() {
    // SAFETY: see `unsat_context`.
    unsafe {
        let (ctx, solver) = unsat_context();
        Z3_solver_set_proof_production(ctx, solver, true);

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let s = Z3_solver_get_proof_string(ctx, solver);
        assert!(!s.is_null(), "expected non-null proof string for UNSAT");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_looks_like_alethe(&cstr_to_string(s));

        Z3_del_context(ctx);
    }
}

/// SAT + proofs enabled: both accessors must be NULL — never a proof for SAT.
#[test]
fn proof_sat_enabled_returns_null() {
    // SAFETY: all handles live in the context arena; freed at block end.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"q".as_ptr());
        let q = Z3_mk_const(ctx, sym, bool_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_set_proof_production(ctx, solver, true);
        Z3_solver_assert(ctx, solver, q);

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        let proof = Z3_solver_get_proof(ctx, solver);
        assert_eq!(proof, 0, "must not return a proof handle for a SAT result");
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);

        let s = Z3_solver_get_proof_string(ctx, solver);
        assert!(
            s.is_null(),
            "must not return a proof string for a SAT result"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);

        Z3_del_context(ctx);
    }
}

/// UNSAT + proofs DISABLED: both accessors must be NULL with an honest error.
#[test]
fn proof_unsat_disabled_returns_null() {
    // SAFETY: see `unsat_context`.
    unsafe {
        let (ctx, solver) = unsat_context();
        // Proof production is OFF (default). Confirm it.
        assert!(!Z3_solver_get_proof_production(ctx, solver));

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let proof = Z3_solver_get_proof(ctx, solver);
        assert_eq!(proof, 0, "must not return a proof when production is off");
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);

        let s = Z3_solver_get_proof_string(ctx, solver);
        assert!(
            s.is_null(),
            "must not return a proof string when production is off"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);

        Z3_del_context(ctx);
    }
}

/// No check run yet + proofs enabled: must be NULL (no proof to return).
#[test]
fn proof_before_check_returns_null() {
    // SAFETY: see `unsat_context`.
    unsafe {
        let (ctx, solver) = unsat_context();
        Z3_solver_set_proof_production(ctx, solver, true);

        // No Z3_solver_check call.
        let proof = Z3_solver_get_proof(ctx, solver);
        assert_eq!(proof, 0, "must not return a proof before any check");
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);

        Z3_del_context(ctx);
    }
}

/// Enabling proofs via the Z3 global `proof` config param (no explicit setter)
/// still produces a real proof — matching Z3's `Z3_set_param_value(cfg,
/// "proof", "true")` surface.
#[test]
fn proof_enabled_via_config_param() {
    // SAFETY: all handles live in the context arena; freed at block end.
    unsafe {
        let cfg = Z3_mk_config();
        Z3_set_param_value(cfg, c"proof".as_ptr(), c"true".as_ptr());
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"p".as_ptr());
        let p = Z3_mk_const(ctx, sym, bool_sort);
        let not_p = Z3_mk_not(ctx, p);

        let solver = Z3_mk_solver(ctx);
        assert!(
            Z3_solver_get_proof_production(ctx, solver),
            "config `proof=true` must enable proof production"
        );
        Z3_solver_assert(ctx, solver, p);
        Z3_solver_assert(ctx, solver, not_p);

        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let s = Z3_solver_get_proof_string(ctx, solver);
        assert!(!s.is_null());
        assert_looks_like_alethe(&cstr_to_string(s));

        Z3_del_context(ctx);
    }
}

/// The tag-routing helper only matches real proof handles, never term handles.
#[test]
fn proof_text_for_ast_rejects_non_proof_handles() {
    // SAFETY: all handles live in the context arena; freed at block end.
    unsafe {
        let (ctx, solver) = unsat_context();
        Z3_solver_set_proof_production(ctx, solver, true);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        let proof = Z3_solver_get_proof(ctx, solver);
        assert_ne!(proof, 0);

        let ctx_ref = &*ctx;
        // An ordinary (untagged) AST value must never resolve to proof text.
        assert!(proof_text_for_ast(ctx_ref, 1).is_none());
        // The real proof handle does resolve.
        assert!(proof_text_for_ast(ctx_ref, proof).is_some());
        // A bare forged tag has no context salt and must not decode.
        assert!(proof_text_for_ast(ctx_ref, PROOF_AST_TAG | 0x270f).is_none());
        // An authenticated-but-out-of-range index is likewise None (not a
        // panic / not UB).
        let dangling = encode_indexed_ast(ctx_ref, PROOF_AST_TAG, 0x270f)
            .expect("small test index must be representable");
        assert!(proof_text_for_ast(ctx_ref, dangling).is_none());

        Z3_del_context(ctx);
    }
}
