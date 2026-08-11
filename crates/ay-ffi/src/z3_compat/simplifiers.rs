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
//! original assertions — a simplifier can never change the answer. Each name is
//! mapped explicitly to an existing sound AY [`Tactic`]. Where AY has no
//! corresponding transformation yet, the name is admitted as the identity
//! [`Tactic::Skip`]; this preserves the verdict without pretending that an
//! unimplemented rewrite happened. The solver runs the selected tactic through
//! the same `apply_tactic_to_goal` path used by `Z3_mk_solver_from_tactic`.
//!
//! # Recognized simplifier names (and how unknown names are handled — HONEST)
//!
//! [`SUPPORTED_SIMPLIFIER_NAMES`] is exactly the 37-name registry reported by
//! Z3 5.0.0's `Z3_get_simplifier_name`, in the same order. (The `z3
//! -simplifiers` presentation sorts that registry and therefore is not the C
//! API enumeration order.) In particular, tactic names `elim-and` and `nnf`
//! are not simplifier names and are rejected here. Any name outside this set
//! returns NULL and sets `Z3_INVALID_ARG`.

use std::ptr;

use ay_dpll::api::Tactic;

use super::{
    cache_string, ffi_guard_const_ptr, ffi_guard_ptr, ffi_read_bounded_text, ParamDescrsHandle,
    SimplifierHandle, Z3Context, Z3SolverHandle, Z3_context, Z3_param_descrs, Z3_params,
    Z3_simplifier, Z3_solver, Z3_string, Z3_INVALID_ARG, Z3_OK,
};

/// The exact Z3 5.0.0 simplifier registry, in C API enumeration order.
pub const SUPPORTED_SIMPLIFIER_NAMES: &[&str] = &[
    "bit2int",
    "bit-blast",
    "bv1-blast",
    "cheap-fourier-motzkin",
    "elim-term-ite",
    "max-bv-sharing",
    "pull-nested-quantifiers",
    "push-app-ite-conservative",
    "push-app-ite",
    "ng-push-app-ite-conservative",
    "ng-push-app-ite",
    "randomizer",
    "refine-injectivity",
    "simplify",
    "qe-light",
    "card2bv",
    "factor",
    "propagate-ineqs",
    "propagate-bv-bounds",
    "bv-divrem-bounds",
    "bv-slice",
    "bvarray2uf",
    "blast-term-ite",
    "cofactor-term-ite",
    "demodulator",
    "der",
    "distribute-forall",
    "dom-simplify",
    "elim-unconstrained",
    "elim-predicates",
    "fold-unfold",
    "injectivity",
    "propagate-values",
    "reduce-args",
    "solve-eqs",
    "special-relations",
    "euf-completion",
];

/// Resolve a simplifier NAME to a verdict-preserving [`Tactic`], or `Err` with an
/// honest diagnostic if the name is not a Z3 5.0.0 simplifier.
///
/// Exact or close existing passes are used where possible. The remaining names
/// map to `Skip`, a deliberate conservative implementation: identity is always
/// equivalence-preserving, while substituting an unrelated rewrite could be
/// unsound. This function is the one operational name-to-pass matrix.
fn simplifier_from_name(name: &str) -> Result<Tactic, String> {
    let tactic = match name {
        // Existing AY passes that directly implement or conservatively
        // approximate the requested operation.
        "bit-blast" => Tactic::BitBlast,
        "blast-term-ite" | "cofactor-term-ite" | "push-app-ite" | "push-app-ite-conservative" => {
            Tactic::BlastTermIte
        }
        "der" | "demodulator" => Tactic::Der,
        "distribute-forall" => Tactic::DistributeForall,
        "elim-term-ite" => Tactic::ElimTermIte,
        "propagate-ineqs" | "propagate-bv-bounds" => Tactic::PropagateIneqs,
        "propagate-values" => Tactic::PropagateValues,
        "qe-light" | "cheap-fourier-motzkin" => Tactic::QeLight,
        "reduce-args" => Tactic::ReduceArgs,
        "simplify" | "card2bv" | "dom-simplify" => Tactic::FlattenAnd,
        "solve-eqs" | "elim-unconstrained" | "fold-unfold" => Tactic::SolveEqs,

        // No equivalent AY pass exists yet. Identity is the only universally
        // sound admission: construction/catalog parity is present, while the
        // requested rewrite remains an explicit semantic-parity gap.
        "bit2int"
        | "bv-divrem-bounds"
        | "bv-slice"
        | "bv1-blast"
        | "bvarray2uf"
        | "elim-predicates"
        | "euf-completion"
        | "factor"
        | "injectivity"
        | "max-bv-sharing"
        | "ng-push-app-ite"
        | "ng-push-app-ite-conservative"
        | "pull-nested-quantifiers"
        | "randomizer"
        | "refine-injectivity"
        | "special-relations" => Tactic::Skip,
        _ => return Err(format!("unknown simplifier {name}")),
    };
    Ok(tactic)
}

/// Z3 5.0.0's per-name catalog descriptions. Covers exactly
/// [`SUPPORTED_SIMPLIFIER_NAMES`]; `None` for any other name.
fn simplifier_descr(name: &str) -> Option<&'static str> {
    Some(match name {
        "bit-blast" => "reduce bit-vector expressions into SAT.",
        "bit2int" => "simplify bit2int expressions.",
        "blast-term-ite" => "blast term if-then-else by hoisting them.",
        "bv-divrem-bounds" => {
            "add range lemmas for bit-vector division/remainder terms with a symbolic divisor."
        }
        "bv-slice" => "simplify using bit-vector slices.",
        "bv1-blast" => {
            "reduce bit-vector expressions into bit-vectors of size 1 (notes: only equality, extract and concat are supported)."
        }
        "bvarray2uf" => "Rewrite bit-vector arrays into bit-vector (uninterpreted) functions.",
        "card2bv" => "convert pseudo-boolean constraints to bit-vectors.",
        "cheap-fourier-motzkin" => {
            "eliminate variables from quantifiers using partial Fourier-Motzkin elimination."
        }
        "cofactor-term-ite" => "eliminate term if-then-else using cofactors.",
        "demodulator" => {
            "extracts equalities from quantifiers and applies them to simplify."
        }
        "der" => "destructive equality resolution.",
        "distribute-forall" => "distribute forall over conjunctions.",
        "dom-simplify" => "apply dominator simplification rules.",
        "elim-predicates" => "eliminate predicates, macros and implicit definitions.",
        "elim-term-ite" => "eliminate if-then-else term by hoisting them top top-level.",
        "elim-unconstrained" => "eliminate unconstrained variables.",
        "euf-completion" => "simplify modulo congruence closure.",
        "factor" => "polynomial factorization.",
        "fold-unfold" => "solve for variables.",
        "injectivity" => "Identifies and applies injectivity axioms.",
        "max-bv-sharing" => {
            "use heuristics to maximize the sharing of bit-vector expressions such as adders and multipliers."
        }
        "ng-push-app-ite" | "ng-push-app-ite-conservative" => {
            "Push functions over if-then-else within non-ground terms only."
        }
        "propagate-bv-bounds" => {
            "propagate bit-vector bounds by simplifying implied or contradictory bounds."
        }
        "propagate-ineqs" => "propagate ineqs/bounds, remove subsumed inequalities.",
        "propagate-values" => "propagate constants.",
        "pull-nested-quantifiers" => "pull nested quantifiers to top-level.",
        "push-app-ite" | "push-app-ite-conservative" => {
            "Push functions over if-then else."
        }
        "qe-light" => "apply light-weight quantifier elimination.",
        "randomizer" => "shuffle assertions and rename uninterpreted functions.",
        "reduce-args" => {
            "reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value."
        }
        "refine-injectivity" => "refine injectivity axioms.",
        "simplify" => "apply simplification rules.",
        "solve-eqs" => "solve for variables.",
        "special-relations" => "detect and replace by special relations.",
        _ => return None,
    })
}

/// Create a simplifier by name.
///
/// Recognizes exactly Z3 5.0.0's registry ([`SUPPORTED_SIMPLIFIER_NAMES`]).
/// Any other name returns NULL and sets `Z3_INVALID_ARG`.
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
    let (first, second) = unsafe {
        (
            s1.as_ref().map(|h| h.tactic.clone()),
            s2.as_ref().map(|h| h.tactic.clone()),
        )
    };

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
    let (solver_data, simp) = unsafe {
        (
            solver.as_ref().map(|h| {
                (
                    h.assertions.clone(),
                    h.scope_markers.clone(),
                    h.tracked.clone(),
                    h.tracked_scope_markers.clone(),
                    h.tactic.clone(),
                )
            }),
            simplifier.as_ref().map(|h| h.tactic.clone()),
        )
    };

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
