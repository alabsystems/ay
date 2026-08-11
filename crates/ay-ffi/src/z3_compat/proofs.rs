// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible proof production and retrieval (#phase3-proof).
//!
//! AY produces real Alethe proofs after an UNSAT result when proof production
//! is enabled. This module exposes that artifact through the Z3 C API.
//!
//! # Honesty contract
//!
//! Every function here is fail-closed:
//! - [`Z3_solver_get_proof`] / [`Z3_solver_get_proof_string`] return NULL (and
//!   set an honest error code) unless the last `Z3_solver_check` was UNSAT
//!   **and** proof production was enabled before that check. They NEVER return a
//!   proof for a SAT/Unknown result or when production was off.
//! - The returned text is the solver's own exporter output
//!   ([`Solver::export_last_proof_alethe`]). No proof text is invented here.
//!
//! # Representation deviation from Z3
//!
//! In real Z3, `Z3_solver_get_proof` returns a `Z3_ast` whose
//! `Z3_ast_to_string` yields the proof. AY's proof is an `ay_core::Proof`
//! (a separate DAG), not a `Term`, and ordinary AY `Z3_ast` handles index the
//! context's authenticated term-capability arena — there is no faithful way to
//! encode a proof as an ordinary term handle.
//!
//! To preserve the Z3 surface while staying honest, [`Z3_solver_get_proof`]
//! returns an opaque proof-AST handle tagged with the high bit
//! ([`PROOF_AST_TAG`]); calling [`Z3_ast_to_string`](super::Z3_ast_to_string)
//! on it returns the real Alethe text. The proof-AST handle is otherwise NOT a
//! valid term and must not be passed to term inspection functions. Consumers
//! that want the text directly should prefer the explicitly named
//! [`Z3_solver_get_proof_string`]. This deviation is documented in the header.

use std::ffi::c_char;

use super::{
    cache_string, decode_indexed_ast, encode_indexed_ast, ffi_guard_ast, ffi_guard_const_ptr,
    ffi_guard_void, SolverCheckOutcome, Z3Context, Z3_ast, Z3_context, Z3_solver, Z3_string,
    PROOF_AST_TAG, Z3_INVALID_ARG, Z3_INVALID_USAGE, Z3_OK,
};

/// If `a` is a proof-AST handle owned by `ctx` (tag and context salt match) that
/// indexes a stored Alethe proof, return the text. Otherwise `None`.
///
/// Used by [`Z3_ast_to_string`](super::Z3_ast_to_string) to route proof handles
/// to their real exporter text.
pub(crate) fn proof_text_for_ast(ctx: &Z3Context, a: Z3_ast) -> Option<&str> {
    let index = decode_indexed_ast(ctx, a, PROOF_AST_TAG)?;
    ctx.proof_texts.get(index).map(String::as_str)
}

/// Retrieve the Alethe text of the proof from THIS solver handle's last check,
/// if and only if it is honestly available: proof production was enabled and
/// that check was UNSAT.
///
/// The text was materialized into the handle at check time by
/// `check_solver_handle` (the engine-side artefact is invalidated when the
/// check's working scope pops), so it is always the engine's own exporter
/// output for exactly this handle's goal — never fabricated, and never another
/// solver's proof.
///
/// Returns `None` and leaves `last_error`/`error_msg` set on the context in
/// every other case. This is the single source of truth for both
/// [`Z3_solver_get_proof`] and [`Z3_solver_get_proof_string`].
///
/// # Safety
/// `s`, when non-null, must point to a valid `Z3SolverHandle` owned by the
/// context's handle arena (single-threaded per context, so no race).
unsafe fn last_proof_alethe_or_error(ctx: &mut Z3Context, s: Z3_solver) -> Option<String> {
    if s.is_null() || !ctx.solver_handle_cache.contains(&s) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(
            "Z3_solver_get_proof: solver handle is null or belongs to a different context"
                .to_string(),
        );
        return None;
    }
    // SAFETY: membership in this context's owning arena was checked above.
    let handle = unsafe { s.as_ref() };
    // `last_check_outcome` is the public authority. The backend may retain an
    // UNSAT proof candidate that a later consumer/trust gate rejected, so the
    // mere presence of proof text is not enough to publish it. Conversely the
    // current proof-production setting is irrelevant to an already-admitted
    // snapshot (configuration mutations retire snapshots explicitly).
    match handle.and_then(|h| {
        (h.last_check_outcome == Some(SolverCheckOutcome::Unsat))
            .then(|| h.last_proof_alethe.clone())
            .flatten()
    }) {
        Some(text) => {
            ctx.last_error = Z3_OK;
            Some(text)
        }
        None => {
            ctx.last_error = Z3_INVALID_USAGE;
            ctx.error_msg = Some(
                "Z3_solver_get_proof: no proof available \
                 (last result was not UNSAT, or no check has run)"
                    .to_string(),
            );
            None
        }
    }
}

// ---- Proof production control ----

/// Enable or disable proof production for this context's solver.
///
/// This is AY's named setter for the Z3 `proof` global parameter. Equivalent to
/// `Z3_set_param_value(cfg, "proof", "true")` on the config before context
/// creation. Enable this *before* the `Z3_solver_check` whose proof you want.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_set_proof_production(
    c: Z3_context,
    _s: Z3_solver,
    enabled: bool,
) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_set_proof_production") {
                return;
            }
            ctx.solver.set_produce_proofs(enabled);
            ctx.clear_decision_check_artifacts();
            ctx.last_error = Z3_OK;
        });
    }
}

/// Returns true iff proof production is currently enabled for this context.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_proof_production(c: Z3_context, _s: Z3_solver) -> bool {
    // SAFETY: see Z3_solver_set_proof_production. `ffi_guard_int` null-checks `c`
    // and contains any panic; we re-route its c_int sentinel through a bool.
    unsafe { super::ffi_guard_int(c, 0, |ctx| i32::from(ctx.solver.is_producing_proofs())) != 0 }
}

// ---- Proof retrieval ----

/// Get the proof of unsatisfiability from the last `Z3_solver_check`.
///
/// Returns an opaque proof-AST handle (see the module / header deviation note):
/// `Z3_ast_to_string` on the returned handle yields AY's real Alethe proof text.
///
/// Returns NULL (0) and sets `Z3_INVALID_USAGE` when:
/// - proof production was not enabled before the check, or
/// - the last result was not UNSAT (SAT / Unknown / no check run), or
/// - no proof was produced.
///
/// It NEVER returns a non-null handle for a non-UNSAT result or with production
/// off — the proof text is always the solver's own artifact.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_proof(c: Z3_context, s: Z3_solver) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked inside
    // `last_proof_alethe_or_error`.
    unsafe {
        ffi_guard_ast(c, |ctx| match last_proof_alethe_or_error(ctx, s) {
            Some(text) => {
                let Some(ast) = encode_indexed_ast(ctx, PROOF_AST_TAG, ctx.proof_texts.len())
                else {
                    ctx.last_error = Z3_INVALID_USAGE;
                    ctx.error_msg = Some(
                        "Z3_solver_get_proof: proof handle arena exhausted its representable index space"
                            .to_string(),
                    );
                    return 0;
                };
                ctx.proof_texts.push(text);
                ast
            }
            None => 0,
        })
    }
}

/// Get the last UNSAT proof directly as Alethe text (AY-specific accessor).
///
/// This is the honest, explicitly-named alternative to [`Z3_solver_get_proof`]
/// for consumers that want the proof string without the proof-AST handle dance.
/// The returned string is context-owned (valid until `Z3_del_context`).
///
/// Returns NULL and sets `Z3_INVALID_USAGE` under exactly the same conditions
/// as [`Z3_solver_get_proof`].
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_proof_string(c: Z3_context, s: Z3_solver) -> Z3_string {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic so
    // it cannot cross the FFI boundary. `s` is null-checked inside
    // `last_proof_alethe_or_error`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| match last_proof_alethe_or_error(ctx, s) {
            Some(text) => cache_string(ctx, text),
            None => std::ptr::null::<c_char>(),
        })
    }
}

#[cfg(test)]
#[path = "proofs_tests.rs"]
mod proofs_tests;
