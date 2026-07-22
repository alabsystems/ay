// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Simplifier` interface for incremental preprocessing.
//!
//! A Z3 *simplifier* is a preprocessing goal-to-goal transformer — like a tactic,
//! but *attached to a solver* (via [`Z3_solver_add_simplifier`]) so the solver
//! runs it as a pre-processing step before each `check-sat`. This module exposes
//! the `Z3_simplifier_*` C API that z3's simplifier surface uses, backed by AY's
//! real preprocess passes ([`ay_dpll`]'s `preprocess/`):
//!
//! - `Z3_mk_simplifier(ctx, name)` builds a named simplifier.
//! - `Z3_simplifier_and_then(ctx, s1, s2)` composes two simplifiers sequentially.
//! - `Z3_simplifier_using_params(ctx, s, p)` attaches parameters (accepted for
//!   API compatibility — see the honesty note on that function).
//! - `Z3_simplifier_inc_ref` / `Z3_simplifier_dec_ref` are bookkeeping-only.
//! - `Z3_simplifier_get_descr(ctx, name)` / `Z3_simplifier_get_help(ctx, s)` /
//!   `Z3_simplifier_get_param_descrs(ctx, s)` introspect the surface.
//! - `Z3_solver_add_simplifier(ctx, solver, simp)` attaches `simp` to a solver,
//!   returning a NEW solver that runs `simp` before each check (matching z3, which
//!   returns a fresh solver rather than mutating the input).
//!
//! # Soundness (HARD requirement)
//!
//! Every simplifier built here is **verdict-preserving**: solving via a solver
//! with the simplifier attached yields the SAME SAT/UNSAT verdict as solving the
//! original assertions — a simplifier can never change the answer. This is because
//! each simplifier wraps an AY [`Tactic`] resolved through the exact same
//! name→transform mapping ([`ay_frontend::ApplyTactic::parse`] +
//! [`Tactic::from_apply`]) the verdict-preserving tactic surface uses, and the
//! solver runs it through the SAME `apply_tactic_to_goal` preprocessing path that
//! `Z3_mk_solver_from_tactic` uses (see `solver.rs`). Most simplifiers are
//! additionally equivalence-preserving; `bit-blast` is equisatisfiable (it mints
//! fresh Boolean bits), which still preserves `check-sat`.
//!
//! # Recognized simplifier names (and how unknown names are handled — HONEST)
//!
//! [`SUPPORTED_SIMPLIFIER_NAMES`] is the curated set of AY preprocess passes that
//! act as genuine single-goal simplifiers. The first five —
//! `simplify`, `solve-eqs`, `propagate-values`, `qe-light`, `bit-blast` — are all
//! real Z3 simplifier names (as listed by z3's `(help-simplifier)`), each backed
//! by a real AY pass and each mapping to the identical transform the tactic
//! surface uses (so the two can never drift). `elim-and` and `nnf` are a
//! documented AY superset: real AY passes that Z3 does not expose under those
//! names as simplifiers (Z3 rejects them). For ANY name outside this set —
//! including such Z3-superset names on the twin, and genuinely unknown names —
//! `Z3_mk_simplifier` returns NULL and sets `Z3_INVALID_ARG` (the honest path,
//! matching z3's own "unknown simplifier" rejection). It NEVER silently returns a
//! no-op pretending to be the requested simplifier.

use std::ptr;

use ay_dpll::api::Tactic;
use ay_frontend::{ApplyTactic, SExpr};

use super::{
    cache_string, ffi_guard_const_ptr, ffi_guard_ptr, ffi_read_bounded_text, ParamDescrsHandle,
    SimplifierHandle, Z3Context, Z3SolverHandle, Z3_context, Z3_param_descrs, Z3_params,
    Z3_simplifier, Z3_solver, Z3_string, Z3_INVALID_ARG, Z3_OK,
};

/// The curated set of names [`Z3_mk_simplifier`] accepts — genuine AY
/// single-goal preprocessing passes.
///
/// The first five are real Z3 simplifier names (verified against z3's
/// `(help-simplifier)`): each is cross-checkable against libz3. `elim-and` and
/// `nnf` are a documented AY superset (real AY passes that z3 does not expose as
/// simplifiers). Every name here resolves through the SHARED tactic registry to a
/// verdict-preserving transform, so this surface and the `(apply ...)` / tactic
/// surface can never drift.
pub const SUPPORTED_SIMPLIFIER_NAMES: &[&str] = &[
    "simplify",
    "solve-eqs",
    "propagate-values",
    "qe-light",
    "bit-blast",
    "elim-and",
    "nnf",
];

/// Resolve a simplifier NAME to a verdict-preserving [`Tactic`], or `Err` with an
/// honest diagnostic if the name is not a supported AY simplifier.
///
/// This is the single chokepoint that decides which names are honored. It first
/// gates on the curated [`SUPPORTED_SIMPLIFIER_NAMES`] set (so `skip`/`fail`/
/// `split-clause` — tactic control primitives that are not simplifiers — are
/// rejected here even though the tactic registry would accept them), then
/// delegates to the SHARED front-end registry ([`ApplyTactic::parse`] +
/// [`Tactic::from_apply`]) so the accepted names map to exactly the same
/// verdict-preserving transforms the tactic surface uses. It never returns a
/// transform that is not `check-sat`-preserving, and returns `Err` (so the caller
/// reports NULL + `Z3_INVALID_ARG`) for any name AY does not recognize as a
/// simplifier.
fn simplifier_from_name(name: &str) -> Result<Tactic, String> {
    if !SUPPORTED_SIMPLIFIER_NAMES.contains(&name) {
        return Err(format!("unknown simplifier {name}"));
    }
    // Every accepted name resolves through the SHARED registry — the same parser
    // the SMT-LIB `(apply <name>)` / `Z3_mk_tactic` paths use — so the simplifier
    // surface maps each name to the identical verdict-preserving transform.
    match ApplyTactic::parse(&SExpr::Symbol(name.to_string())) {
        Ok(at) => Ok(Tactic::from_apply(&at)),
        // A name in the allowlist is always a valid registry name, so this arm is
        // only reachable if the two lists drift; surface the honest diagnostic.
        Err(e) => Err(e.to_string()),
    }
}

/// The honest per-name description for [`Z3_simplifier_get_descr`]. Covers exactly
/// [`SUPPORTED_SIMPLIFIER_NAMES`]; every string describes AY's real transform.
/// `None` for any other name (⇒ NULL + `Z3_INVALID_ARG`).
fn simplifier_descr(name: &str) -> Option<&'static str> {
    Some(match name {
        "simplify" => {
            "apply simplification rules and split top-level conjunctions into separate goal formulas."
        }
        "solve-eqs" => "solve variable equalities and eliminate the solved variables.",
        "propagate-values" => "propagate ground (= expr const) equalities.",
        "qe-light" => "apply light-weight quantifier elimination.",
        "bit-blast" => {
            "reduce bit-vector expressions into an equisatisfiable pure-Boolean (SAT) goal."
        }
        "elim-and" => {
            "eliminate top-level conjunctions: split (and (and a b) c) into separate goal formulas {a, b, c}."
        }
        "nnf" => "put goal in negation normal form.",
        _ => return None,
    })
}

/// Create a simplifier by name.
///
/// Recognizes the curated AY simplifier set ([`SUPPORTED_SIMPLIFIER_NAMES`]) via
/// the same registry the tactic / `(apply ...)` paths use. Any unknown or
/// unsupported name returns NULL and sets `Z3_INVALID_ARG` — the honest path,
/// matching z3's unknown-simplifier rejection. A NULL is never a silent no-op
/// pretending to be the requested simplifier.
///
/// # Safety
/// `c` must be a valid context pointer; `name`, when non-null, a null-terminated
/// C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_simplifier(c: Z3_context, name: Z3_string) -> Z3_simplifier {
    // Pre-extract the name string outside the guard (raw-pointer deref).
    let name_str: Option<String> = if name.is_null() {
        None
    } else {
        // SAFETY: the caller's `# Safety` contract guarantees `name`, when non-null, points to a
        // valid null-terminated C string owned by the caller for the duration of this call.
        match unsafe { ffi_read_bounded_text(name) } {
            Ok(s) => Some(s),
            Err(_) => Some(String::new()), // non-UTF-8 -> unsupported below
        }
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(ref n) = name_str else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_simplifier: null simplifier name".to_string());
                return ptr::null_mut();
            };
            match simplifier_from_name(n) {
                Ok(tactic) => store_simplifier(ctx, tactic),
                Err(msg) => {
                    // HONEST: unknown/unsupported simplifier name -> NULL + error.
                    // Never a silent identity pretending to be the request.
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_mk_simplifier: {msg}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Allocate a [`SimplifierHandle`] for `tactic`, register it in the context arena
/// (freed at `Z3_del_context`), and return the handle. Shared by every simplifier
/// constructor here so the arena discipline is single-sourced.
fn store_simplifier(ctx: &mut Z3Context, tactic: Tactic) -> Z3_simplifier {
    ctx.last_error = Z3_OK;
    let handle = Box::into_raw(Box::new(SimplifierHandle { tactic }));
    ctx.simplifier_handle_cache.push(handle);
    handle
}

/// Increment simplifier reference count (bookkeeping no-op).
///
/// Mirrors `Z3_tactic_inc_ref`/`Z3_solver_inc_ref`: the handle is arena-owned by
/// the context and freed only by `Z3_del_context`, so this never frees anything.
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplifier_inc_ref(_c: Z3_context, _t: Z3_simplifier) {}

/// Decrement simplifier reference count (bookkeeping no-op).
///
/// Mirrors `Z3_tactic_dec_ref`/`Z3_solver_dec_ref`: the handle is arena-owned by
/// the context and freed only by `Z3_del_context`, so this never frees an
/// arena-owned handle early.
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplifier_dec_ref(_c: Z3_context, _t: Z3_simplifier) {}

/// Compose two simplifiers sequentially: apply `s1`, then `s2` on the result
/// (Z3's `Z3_simplifier_and_then`).
///
/// Verdict-preserving because both operands are (only simplifiers built by
/// `Z3_mk_simplifier` and this combinator reach here). Returns NULL and sets
/// `Z3_INVALID_ARG` if either operand is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `s1`/`s2`, when non-null, valid simplifier
/// handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplifier_and_then(
    c: Z3_context,
    s1: Z3_simplifier,
    s2: Z3_simplifier,
) -> Z3_simplifier {
    // Pre-extract the operand tactics outside the guard (raw-pointer deref).
    // SAFETY: each handle, when non-null, is a `SimplifierHandle` produced by a
    // prior `Z3_mk_simplifier`/combinator call and kept alive in the context's
    // `simplifier_handle_cache`. The Z3 C API is single-threaded per context, so
    // this shared read does not race. `as_ref` null-checks.
    let first = unsafe { s1.as_ref() }.map(|h| h.tactic.clone());
    let second = unsafe { s2.as_ref() }.map(|h| h.tactic.clone());

    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ptr` handles the
    // null case internally and catches any unwinding panic.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(a), Some(b)) = (first, second) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_simplifier_and_then: null simplifier operand".to_string());
                return ptr::null_mut();
            };
            store_simplifier(ctx, a.then(b))
        })
    }
}

/// Attach parameters to a simplifier (Z3's `Z3_simplifier_using_params`).
///
/// HONEST DIVERGENCE: AY's simplifiers are always the verdict-preserving
/// preprocess transform, so parameters that would only affect output *shape* (not
/// the model/verdict) do not change the transform. This therefore returns a
/// simplifier wrapping the same underlying transform (the `p` handle is accepted
/// for API compatibility). It never silently substitutes a different,
/// possibly-unsound transform. Returns NULL and sets `Z3_INVALID_ARG` if `s` is
/// NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid simplifier
/// handle; `p`, when non-null, a valid params handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplifier_using_params(
    c: Z3_context,
    s: Z3_simplifier,
    _p: Z3_params,
) -> Z3_simplifier {
    // SAFETY: `s`, when non-null, is a `SimplifierHandle` kept alive in the
    // context's cache; single-threaded per context. `as_ref` null-checks.
    let inner = unsafe { s.as_ref() }.map(|h| h.tactic.clone());

    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(inner) = inner else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_simplifier_using_params: null simplifier handle".to_string());
                return ptr::null_mut();
            };
            store_simplifier(ctx, inner)
        })
    }
}

/// Attach `simplifier` to `solver` for incremental pre-processing (Z3's
/// `Z3_solver_add_simplifier`).
///
/// Returns a NEW solver handle (matching z3, which returns a fresh solver rather
/// than mutating the input) carrying a faithful copy of `solver`'s current
/// assertion/tracking state, whose pre-check preprocessing composes the source
/// solver's existing tactic (when any) THEN `simplifier`. Because the simplifier
/// is verdict-preserving and it runs through the SAME `apply_tactic_to_goal`
/// preprocessing path `Z3_mk_solver_from_tactic` uses, the returned solver's
/// SAT/UNSAT verdict is IDENTICAL to solving the original assertions. The source
/// solver is left untouched.
///
/// Returns NULL and sets `Z3_INVALID_ARG` if `solver` or `simplifier` is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `solver`/`simplifier`, when non-null,
/// valid handles owned by `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_add_simplifier(
    c: Z3_context,
    solver: Z3_solver,
    simplifier: Z3_simplifier,
) -> Z3_solver {
    // Pre-extract the source solver's state and the simplifier's tactic outside
    // the guard (raw-pointer derefs; both handles live in `c`).
    // SAFETY: each handle, when non-null, is a live handle kept in `c`'s arena;
    // the Z3 C API is single-threaded per context, so these shared reads do not
    // race. `as_ref` null-checks.
    let solver_data = unsafe { solver.as_ref() }.map(|h| {
        (
            h.assertions.clone(),
            h.scope_markers.clone(),
            h.tracked.clone(),
            h.tracked_scope_markers.clone(),
            h.tactic.clone(),
        )
    });
    let simp = unsafe { simplifier.as_ref() }.map(|h| h.tactic.clone());

    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_add_simplifier") {
                return ptr::null_mut();
            }
            let (
                Some((assertions, scope_markers, tracked, tracked_scope_markers, src_tactic)),
                Some(simp),
            ) = (solver_data, simp)
            else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_solver_add_simplifier: null solver or simplifier handle".to_string());
                return ptr::null_mut();
            };
            // Compose the source solver's existing preprocessing (when any) THEN
            // the newly-attached simplifier, so chaining `add_simplifier` calls
            // (and add-on-top-of-a-tactic-solver) all run in order. Every operand
            // is verdict-preserving, so the composed transform is too.
            let combined = match src_tactic {
                Some(t) => t.then(simp),
                None => simp,
            };
            let mut new_handle = Z3SolverHandle::new(Some(combined));
            new_handle.assertions = assertions;
            new_handle.scope_markers = scope_markers;
            new_handle.tracked = tracked;
            new_handle.tracked_scope_markers = tracked_scope_markers;
            let handle = Box::into_raw(Box::new(new_handle));
            ctx.solver_handle_cache.push(handle);
            ctx.last_error = Z3_OK;
            handle
        })
    }
}

/// Return a description of the simplifier named `name` (Z3's
/// `Z3_simplifier_get_descr`).
///
/// Returns a context-owned string for each name AY's [`Z3_mk_simplifier`] accepts
/// — an HONEST description of AY's actual realization of that simplifier. An
/// unknown/unsupported name returns NULL and sets `Z3_INVALID_ARG` (the honest
/// path; z3 itself sets `Z3_INVALID_ARG` for an unknown simplifier name).
///
/// # Safety
/// `c` must be a valid context pointer; `name`, when non-null, a null-terminated
/// C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplifier_get_descr(c: Z3_context, name: Z3_string) -> Z3_string {
    // Pre-extract the name string outside the guard (raw-pointer deref).
    let name_str: Option<String> = if name.is_null() {
        None
    } else {
        // SAFETY: caller contract guarantees a valid null-terminated C string.
        unsafe { ffi_read_bounded_text(name) }.ok()
    };
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            match name_str.as_deref().and_then(simplifier_descr) {
                Some(descr) => {
                    ctx.last_error = Z3_OK;
                    cache_string(ctx, descr.to_string())
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg =
                        Some("Z3_simplifier_get_descr: unknown simplifier name".to_string());
                    ptr::null()
                }
            }
        })
    }
}

/// Return a help string describing the parameters accepted by simplifier `t`
/// (Z3's `Z3_simplifier_get_help`).
///
/// HONEST: AY's simplifiers are the verdict-preserving preprocess transform and
/// expose no per-simplifier tunable parameters that would change the produced
/// goal's verdict, so the help documents that (parameter-free) and lists the
/// supported simplifier names for convenience — a real, non-empty string, never a
/// fabricated parameter listing. Returns NULL and sets `Z3_INVALID_ARG` if `t` is
/// NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid simplifier
/// handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplifier_get_help(c: Z3_context, t: Z3_simplifier) -> Z3_string {
    // SAFETY: `t`, when non-null, is a live `SimplifierHandle`; `as_ref`
    // null-checks. Single-threaded per context, so no race.
    let has_simplifier = unsafe { t.as_ref() }.is_some();
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if !has_simplifier {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_simplifier_get_help: null simplifier handle".to_string());
                return ptr::null();
            }
            ctx.last_error = Z3_OK;
            let mut help = String::from(
                "AY simplifiers are parameter-free verdict-preserving preprocessing passes.\nSupported simplifiers:\n",
            );
            for name in SUPPORTED_SIMPLIFIER_NAMES {
                help.push_str("  ");
                help.push_str(name);
                help.push('\n');
            }
            cache_string(ctx, help)
        })
    }
}

/// Return the parameter-descriptor set for a simplifier (Z3's
/// `Z3_simplifier_get_param_descrs`).
///
/// HONEST EMPTY (documented): AY's simplifiers are always the verdict-preserving
/// transform, so they expose NO per-simplifier tunable parameters that would
/// change the produced goal's verdict. This therefore returns a REAL, queryable —
/// empty — [`ParamDescrsHandle`] (size 0), never a fabricated parameter set
/// disguised as z3's. The `t` handle is validated (NULL ⇒ `Z3_INVALID_ARG`).
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid simplifier
/// handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplifier_get_param_descrs(
    c: Z3_context,
    t: Z3_simplifier,
) -> Z3_param_descrs {
    // SAFETY: `t`, when non-null, is a live `SimplifierHandle`; `as_ref`
    // null-checks.
    let has_simplifier = unsafe { t.as_ref() }.is_some();
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if !has_simplifier {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_simplifier_get_param_descrs: null simplifier handle".to_string());
                return ptr::null_mut();
            }
            ctx.last_error = Z3_OK;
            // Honest-empty: no per-simplifier params affect AY's verdict-preserving
            // transform. A real (queryable) descr set of size 0 — not a fake.
            let handle = Box::into_raw(Box::new(ParamDescrsHandle {
                entries: Vec::new(),
            }));
            ctx.param_descrs_cache.push(handle);
            handle
        })
    }
}

// ============================================================================
// Simplifier registry enumeration
// ============================================================================

#[cfg(test)]
#[path = "simplifiers_ffi_tests.rs"]
mod simplifiers_ffi_tests;
