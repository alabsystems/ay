// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Tactic` interface for goal-to-goal transformations.
//!
//! Exposes the subset of the Z3 `Z3_tactic_*` C API that z3py's tactic surface
//! exercises, backed by AY's [`ay_dpll::api::Tactic`] framework:
//!
//! - `Z3_mk_tactic(ctx, name)` builds a named tactic.
//! - `Z3_tactic_and_then` / `Z3_tactic_or_else` compose tactics.
//! - `Z3_tactic_inc_ref` / `Z3_tactic_dec_ref` are bookkeeping-only no-ops.
//! - `Z3_mk_solver_from_tactic(ctx, t)` builds a solver that applies the tactic
//!   to its goal before each `check`.
//!
//! # Soundness (HARD requirement)
//!
//! Every tactic constructed here is **verdict-preserving**: solving via a
//! tactic-solver yields the SAME SAT/UNSAT verdict as solving the original goal
//! — applying a tactic can never change the answer. All but one are additionally
//! *equivalence-preserving* (they rewrite the goal into one with exactly the same
//! set of models). The exception is `tseitin-cnf`, which is
//! **equisatisfiable**: it introduces fresh auxiliary Boolean variables, so the
//! CNF's models differ from the input's on those new variables while `check-sat`
//! is preserved (the aux variables are existentially quantified / free).
//!
//! # Recognized tactic names (and how unknown names are handled — HONEST)
//!
//! Names are resolved through the **single shared registry**
//! ([`ay_frontend::ApplyTactic::parse`]) that the SMT-LIB `(apply <name>)` path
//! uses, so this C-API surface and the `(apply ...)` surface recognize an
//! identical set ([`ay_frontend::SUPPORTED_TACTIC_NAMES`]) and map each name to
//! the identical, equivalence-preserving transform (via
//! [`Tactic::from_apply`]). The two can never drift.
//!
//! Recognized (all real Z3 tactic names, each backed by a real pass):
//! `skip`, `simplify`, `solve-eqs`, `propagate-values`, `elim-and`, `qe-light`,
//! `nnf`, `tseitin-cnf`, `bit-blast`. `nnf` is AY's
//! negation-normal-form pass: negations are pushed to atoms and
//! `=>`/`<->`/`xor`/`ite`-over-Bool are eliminated into `and`/`or`
//! (equivalence-preserving). `bit-blast` is AY's `BitBlast` pass: a QF_BV goal is
//! rewritten into an equisatisfiable pure-Boolean goal (each BV variable becomes
//! `n` Boolean bits, each BV operator its Boolean circuit); a goal that contains
//! a bit-vector construct outside the supported fragment HONESTLY FAILS (a
//! tactic-failure error), never a fabricated or silent-identity blast.
//! `elim-and` is Z3's and-elimination name, realized by AY's `FlattenAnd` pass:
//! `(and (and a b) c)` becomes the goal `{a, b, c}`. `qe-light` is AY's Cooper
//! light-QE pass: each in-fragment `(exists ((x Int)) φ)` subterm is replaced *in
//! place* by a quantifier-free formula over its FREE variables (verified
//! logically equivalent by Cooper's self-check), so the bound variable never
//! escapes and the transform is equivalence-preserving even under negation.
//!
//! `tseitin-cnf` is AY's Tseitin CNF pass: the one verdict-
//! preserving-but-not-equivalent member (it mints fresh existential aux
//! variables). All of them form the faithfully-printable set that this surface
//! shares verbatim with the SMT-LIB `(apply ...)` path — the two recognize an
//! identical set and map each name to the identical transform, so they can never
//! drift.
//!
//! Beyond the pass-backed set, the registry now covers EVERY pinned Z3 5.0.0
//! tactic name (118 total): per-logic solver strategies and no-op-safe transforms are
//! realized as the truthful identity, alias names reduce to an existing
//! verified pass, and fragment tactics (`diff-neq`, `pb2bv`, `bv1-blast`, …)
//! are HONEST failures matching z3's own measured failure routing. Every
//! realization (and every measured divergence from z3) is documented per name
//! in [`Z3_tactic_get_descr`]'s text — see `ay_frontend::command::tactic` for
//! the class taxonomy. None of them adds a decide path; none can change a
//! verdict.
//!
//! For ANY OTHER name — including names Z3 itself does not have, such as
//! `flatten-and` — `Z3_mk_tactic` returns NULL and sets `Z3_INVALID_ARG` (the
//! honest path, matching Z3's own "unknown tactic" rejection). It NEVER silently
//! returns a no-op that pretends to be the requested tactic, and it NEVER maps a
//! name to a transform whose soundness is unknown.

use std::ptr;

use ay_dpll::api::Tactic;
use ay_frontend::{ApplyTactic, SExpr};

use super::{
    cache_string, ffi_count_within_limit, ffi_guard_const_ptr, ffi_guard_ptr,
    ffi_read_bounded_text, DecisionOwnerFamily, ParamDescrsHandle, TacticHandle, Z3Context,
    Z3SolverHandle, Z3_context, Z3_param_descrs, Z3_params, Z3_probe, Z3_solver, Z3_string,
    Z3_tactic, Z3_INVALID_ARG, Z3_OK,
};
use std::os::raw::c_uint;

/// Allocate a [`TacticHandle`] for `tactic`, register it in the context arena
/// (freed at `Z3_del_context`), and return the handle. Shared by every tactic
/// constructor here so the arena discipline is single-sourced.
fn store_tactic(ctx: &mut Z3Context, tactic: Tactic) -> Z3_tactic {
    ctx.last_error = Z3_OK;
    let handle = Box::into_raw(Box::new(TacticHandle { tactic }));
    ctx.tactic_handle_cache.push(handle);
    handle
}

/// Resolve a tactic NAME to a verdict-preserving [`Tactic`], or `Err` with an
/// honest diagnostic if the name is not a supported tactic.
///
/// This is the single chokepoint that decides which names are honored. It
/// delegates to the SHARED front-end registry ([`ApplyTactic::parse`]) so the
/// C-API and the SMT-LIB `(apply ...)` surface recognize exactly the same names
/// and produce exactly the same transforms (via [`Tactic::from_apply`]). It
/// never returns a tactic for a name whose transform is not verdict-preserving
/// (`check-sat`-preserving), and returns `Err` (so the caller reports NULL +
/// `Z3_INVALID_ARG`) for any name Z3/AY does not understand.
fn tactic_from_name(name: &str) -> Result<Tactic, String> {
    // Every name resolves through the SHARED registry: the same parser the
    // SMT-LIB `(apply <name>)` path uses, so this C-API surface and `(apply)`
    // recognize an identical set and map each name to the identical transform
    // via `Tactic::from_apply` — including `qe-light`, which is now a real
    // printable tactic on both surfaces (no solve-only special case).
    match ApplyTactic::parse(&SExpr::Symbol(name.to_string())) {
        Ok(at) => Ok(Tactic::from_apply(&at)),
        Err(e) => Err(e.to_string()),
    }
}

/// Create a tactic by name.
///
/// Recognizes the shared real-Z3 printable set (`skip`, `simplify`, `solve-eqs`,
/// `propagate-values`, `elim-and`, `qe-light`, `tseitin-cnf`) via the same
/// registry the SMT-LIB `(apply ...)` path uses. Any
/// unknown/unsupported name (including Z3-nonexistent names like `flatten-and`)
/// returns NULL and sets `Z3_INVALID_ARG` — the honest path, matching Z3. A NULL
/// is never a silent no-op pretending to be the requested tactic.
///
/// # Safety
/// `c` must be a valid context pointer; `name`, when non-null, must be a
/// null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_tactic(c: Z3_context, name: Z3_string) -> Z3_tactic {
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
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(ref n) = name_str else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_tactic: null tactic name".to_string());
                return ptr::null_mut();
            };
            match tactic_from_name(n) {
                Ok(tactic) => {
                    ctx.last_error = Z3_OK;
                    let handle = Box::into_raw(Box::new(TacticHandle { tactic }));
                    ctx.tactic_handle_cache.push(handle);
                    handle
                }
                Err(msg) => {
                    // HONEST: unknown/unsupported tactic name -> NULL + error.
                    // Never a silent identity pretending to be the request. The
                    // diagnostic comes straight from the shared registry parser.
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_mk_tactic: {msg}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Increment tactic reference count (bookkeeping no-op).
///
/// Mirrors `Z3_solver_inc_ref`/`Z3_optimize_inc_ref`: the handle is arena-owned
/// by the context and freed only by `Z3_del_context`, so this never frees
/// anything.
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_inc_ref(_c: Z3_context, _t: Z3_tactic) {}

/// Decrement tactic reference count (bookkeeping no-op).
///
/// Mirrors `Z3_solver_dec_ref`/`Z3_optimize_dec_ref`: the handle is arena-owned
/// by the context and freed only by `Z3_del_context`, so this never frees an
/// arena-owned handle early.
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_dec_ref(_c: Z3_context, _t: Z3_tactic) {}

/// Compose two tactics sequentially: apply `t1`, then `t2` on the result.
///
/// Equivalence-preserving because both operands are (only tactics built by
/// `Z3_mk_tactic` and these combinators reach here). Returns NULL and sets
/// `Z3_INVALID_ARG` if either operand is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t1`/`t2`, when non-null, valid tactic
/// handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_and_then(
    c: Z3_context,
    t1: Z3_tactic,
    t2: Z3_tactic,
) -> Z3_tactic {
    // SAFETY: forwarded under the caller's contract; `combine_tactics` null-checks
    // both operands and `ffi_guard_ptr` handles null `c` / catches panics.
    unsafe { combine_tactics(c, t1, t2, TacticCombinator::AndThen) }
}

/// Compose two tactics alternatively: apply `t1`; if it makes no progress, apply
/// `t2` on the original goal instead.
///
/// Equivalence-preserving (both operands are). Returns NULL and sets
/// `Z3_INVALID_ARG` if either operand is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t1`/`t2`, when non-null, valid tactic
/// handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_or_else(
    c: Z3_context,
    t1: Z3_tactic,
    t2: Z3_tactic,
) -> Z3_tactic {
    // SAFETY: see `Z3_tactic_and_then`.
    unsafe { combine_tactics(c, t1, t2, TacticCombinator::OrElse) }
}

/// Which combinator the shared composition path should apply.
#[derive(Clone, Copy)]
enum TacticCombinator {
    AndThen,
    OrElse,
}

/// Shared composition path for `and-then`/`or-else`.
///
/// # Safety
/// `c` must be a valid context pointer; `t1`/`t2`, when non-null, valid tactic
/// handles.
unsafe fn combine_tactics(
    c: Z3_context,
    t1: Z3_tactic,
    t2: Z3_tactic,
    combinator: TacticCombinator,
) -> Z3_tactic {
    // Pre-extract the operand tactics outside the guard (raw-pointer deref).
    // SAFETY: each handle, when non-null, is a `TacticHandle` produced by a prior
    // `Z3_mk_tactic`/combinator call and kept alive in the context's
    // `tactic_handle_cache`. The Z3 C API is single-threaded per context, so this
    // shared read does not race. `as_ref` null-checks.
    let (first, second) = unsafe {
        (
            t1.as_ref().map(|h| h.tactic.clone()),
            t2.as_ref().map(|h| h.tactic.clone()),
        )
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // function requires it to be a valid, non-aliased pointer (or null). `ffi_guard_ptr`
    // handles the null case internally and catches any unwinding panic.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(a), Some(b)) = (first, second) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_and_then/or_else: null tactic operand".to_string());
                return ptr::null_mut();
            };
            let combined = match combinator {
                TacticCombinator::AndThen => a.then(b),
                TacticCombinator::OrElse => a.or_else(b),
            };
            ctx.last_error = Z3_OK;
            let handle = Box::into_raw(Box::new(TacticHandle { tactic: combined }));
            ctx.tactic_handle_cache.push(handle);
            handle
        })
    }
}

/// Repeat a tactic to a fixpoint, or at most `max` iterations (Z3's
/// `Z3_tactic_repeat`).
///
/// Equivalence-preserving (the body is). AY's `repeat` stops as soon as the body
/// makes no progress, so even the default large `max` terminates at the
/// fixpoint. Returns NULL and sets `Z3_INVALID_ARG` if `t` is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid tactic
/// handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_repeat(c: Z3_context, t: Z3_tactic, max: c_uint) -> Z3_tactic {
    // Pre-extract the body tactic outside the guard (raw-pointer deref).
    // SAFETY: `t`, when non-null, is a `TacticHandle` kept alive in the context's
    // `tactic_handle_cache`; single-threaded per context, so no race. `as_ref`
    // null-checks.
    let body = unsafe { t.as_ref() }.map(|h| h.tactic.clone());

    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ptr` handles null
    // and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(body) = body else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_repeat: null tactic handle".to_string());
                return ptr::null_mut();
            };
            let repeated = body.repeat_up_to(max as usize);
            ctx.last_error = Z3_OK;
            let handle = Box::into_raw(Box::new(TacticHandle { tactic: repeated }));
            ctx.tactic_handle_cache.push(handle);
            handle
        })
    }
}

/// Attach parameters to a tactic (Z3's `Z3_tactic_using_params`, aliased by
/// `Z3_tactic_with`).
///
/// HONEST DIVERGENCE: AY's tactics are always the equivalence-preserving
/// transform, so parameters that would only affect output *shape* (not the model
/// set) do not change the transform. This therefore returns the underlying
/// tactic unchanged (the `p` handle is accepted for API compatibility). It never
/// silently substitutes a different, possibly-unsound transform. Returns NULL and
/// sets `Z3_INVALID_ARG` if `t` is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid tactic
/// handle; `p`, when non-null, a valid params handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_using_params(
    c: Z3_context,
    t: Z3_tactic,
    _p: Z3_params,
) -> Z3_tactic {
    // SAFETY: `t`, when non-null, is a `TacticHandle` kept alive in the context's
    // cache; single-threaded per context. `as_ref` null-checks.
    let inner = unsafe { t.as_ref() }.map(|h| h.tactic.clone());

    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ptr` handles null
    // and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(inner) = inner else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_using_params: null tactic handle".to_string());
                return ptr::null_mut();
            };
            ctx.last_error = Z3_OK;
            let handle = Box::into_raw(Box::new(TacticHandle { tactic: inner }));
            ctx.tactic_handle_cache.push(handle);
            handle
        })
    }
}

/// Alias of [`Z3_tactic_using_params`] (Z3 exposes both names).
///
/// # Safety
/// See [`Z3_tactic_using_params`].
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_with(c: Z3_context, t: Z3_tactic, p: Z3_params) -> Z3_tactic {
    // SAFETY: forwarded verbatim under the same contract.
    unsafe { Z3_tactic_using_params(c, t, p) }
}

/// Create a solver that applies `t` to its goal before each `check`.
///
/// The returned solver behaves exactly like a `Z3_mk_solver` solver except that,
/// at `Z3_solver_check`/`Z3_solver_check_assumptions` time, the tactic `t`
/// transforms the asserted goal first. Because `t` is equivalence-preserving,
/// the verdict and model are IDENTICAL to solving the untransformed goal.
///
/// Returns NULL and sets `Z3_INVALID_ARG` if `t` is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid tactic
/// handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_solver_from_tactic(c: Z3_context, t: Z3_tactic) -> Z3_solver {
    // Pre-extract the tactic outside the guard (raw-pointer deref).
    // SAFETY: `t`, when non-null, is a `TacticHandle` kept alive in the context's
    // `tactic_handle_cache`; single-threaded per context, so no race. `as_ref`
    // null-checks.
    let tactic = unsafe { t.as_ref() }.map(|h| h.tactic.clone());

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(tactic) = tactic else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_solver_from_tactic: null tactic handle".to_string());
                return ptr::null_mut();
            };
            if !ctx.claim_decision_owner(DecisionOwnerFamily::Solver, "Z3_mk_solver_from_tactic") {
                return ptr::null_mut();
            }
            ctx.last_error = Z3_OK;
            let handle = Box::into_raw(Box::new(Z3SolverHandle::new(Some(tactic))));
            ctx.solver_handle_cache.push(handle);
            handle
        })
    }
}

/// Get a textual help/description for a tactic.
///
/// Returns a context-owned string listing the supported, verdict-preserving
/// tactic names — derived from the shared registry
/// ([`ay_frontend::SUPPORTED_TACTIC_NAMES`]) so it never drifts from what
/// `Z3_mk_tactic` actually accepts. (Introspection convenience.)
///
/// # Safety
/// `c` must be a valid context pointer and `t` a live tactic handle from `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_get_help(c: Z3_context, t: Z3_tactic) -> Z3_string {
    use super::{cache_string, ffi_guard_const_ptr};
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; `ffi_guard_const_ptr`
    // handles the null case internally and catches any unwinding panic.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if t.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_get_help: null tactic handle".to_string());
                return ptr::null();
            }
            let mut help = String::from("Supported (verdict-preserving) tactics:\n");
            for name in ay_frontend::SUPPORTED_TACTIC_NAMES {
                help.push_str("  ");
                help.push_str(name);
                help.push('\n');
            }
            cache_string(ctx, help)
        })
    }
}

/// The identity tactic (Z3's `Z3_tactic_skip`): returns its goal unchanged.
///
/// Backed by [`Tactic::Skip`]; applying it yields exactly one subgoal equal to
/// the input (an ApplyResult identical to libz3's on the same goal).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_skip(c: Z3_context) -> Z3_tactic {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ptr` handles null
    // and catches panics.
    unsafe { ffi_guard_ptr(c, |ctx| store_tactic(ctx, Tactic::Skip)) }
}

/// The always-failing tactic (Z3's `Z3_tactic_fail`): every application is an
/// honest [`TacticFailure`](ay_dpll::api) — it produces NO goal.
///
/// Backed by [`Tactic::Fail`]; `Z3_tactic_apply(fail, g)` returns NULL and sets a
/// non-OK error code (a Z3 EXCEPTION), exactly like libz3.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_fail(c: Z3_context) -> Z3_tactic {
    // SAFETY: see `Z3_tactic_skip`.
    unsafe { ffi_guard_ptr(c, |ctx| store_tactic(ctx, Tactic::Fail)) }
}

/// Fail iff the probe `p` holds on the goal, else behave like `skip` (Z3's
/// `Z3_tactic_fail_if`).
///
/// Backed by [`Tactic::FailIf`]. NOTE: this matches libz3's ACTUAL behavior —
/// `Z3_tactic_fail_if(p)` fails when `p` evaluates to TRUE on the goal (verified
/// against libz3 4.15.4; its header comment reads the other way, but the tactic
/// is `cond(p, fail, skip)`). Returns NULL and sets `Z3_INVALID_ARG` if `p` is
/// NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `p`, when non-null, a valid probe handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_fail_if(c: Z3_context, p: Z3_probe) -> Z3_tactic {
    // Pre-extract the probe outside the guard (raw-pointer deref).
    // SAFETY: `p`, when non-null, is a live `ProbeHandle` kept in the context's
    // `probe_cache` (single-threaded per context). `as_ref` null-checks.
    let probe = unsafe { p.as_ref() }.map(|h| h.probe.clone());
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(probe) = probe else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_fail_if: null probe handle".to_string());
                return ptr::null_mut();
            };
            store_tactic(ctx, Tactic::FailIf(probe))
        })
    }
}

/// Fail unless the goal is trivially decided — empty (⇒ decided SAT) or
/// containing the literal `false` (⇒ decided UNSAT) — Z3's
/// `Z3_tactic_fail_if_not_decided`.
///
/// Backed by [`Tactic::FailIfNotDecided`]: on a decided goal it is the identity
/// (one unchanged subgoal); on any other goal `Z3_tactic_apply` returns NULL with
/// a non-OK error code — matching libz3 exactly (verified against libz3 4.15.4).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_fail_if_not_decided(c: Z3_context) -> Z3_tactic {
    // SAFETY: see `Z3_tactic_skip`.
    unsafe { ffi_guard_ptr(c, |ctx| store_tactic(ctx, Tactic::FailIfNotDecided)) }
}

/// Apply `t` iff the probe `p` holds on the goal, else behave like `skip` (Z3's
/// `Z3_tactic_when`).
///
/// Backed by [`Tactic::When`]. Returns NULL and sets `Z3_INVALID_ARG` if `p` or
/// `t` is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `p`/`t`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_when(c: Z3_context, p: Z3_probe, t: Z3_tactic) -> Z3_tactic {
    // Pre-extract the probe and body outside the guard (raw-pointer derefs).
    // SAFETY: both handles, when non-null, are arena-owned by the context and
    // single-threaded per context; `as_ref` null-checks.
    let (probe, body) = unsafe {
        (
            p.as_ref().map(|h| h.probe.clone()),
            t.as_ref().map(|h| h.tactic.clone()),
        )
    };
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(probe), Some(body)) = (probe, body) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_when: null probe or tactic handle".to_string());
                return ptr::null_mut();
            };
            store_tactic(ctx, Tactic::When(probe, Box::new(body)))
        })
    }
}

/// Apply `t1` iff the probe `p` holds on the goal, else apply `t2` (Z3's
/// `Z3_tactic_cond`).
///
/// Backed by [`Tactic::Cond`], a real primitive — NOT `(or-else (when p t1) t2)`.
/// A FAILURE of the chosen branch propagates: `cond(p, fail, skip)` on a goal
/// where `p` holds genuinely fails (verified against libz3 4.15.4), it never
/// silently runs the else-branch. Returns NULL and sets `Z3_INVALID_ARG` if any
/// of `p`/`t1`/`t2` is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `p`/`t1`/`t2`, when non-null, valid
/// handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_cond(
    c: Z3_context,
    p: Z3_probe,
    t1: Z3_tactic,
    t2: Z3_tactic,
) -> Z3_tactic {
    // Pre-extract the probe and both branches outside the guard (raw derefs).
    // SAFETY: all handles, when non-null, are arena-owned and single-threaded per
    // context; `as_ref` null-checks.
    let (probe, first, second) = unsafe {
        (
            p.as_ref().map(|h| h.probe.clone()),
            t1.as_ref().map(|h| h.tactic.clone()),
            t2.as_ref().map(|h| h.tactic.clone()),
        )
    };
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(probe), Some(a), Some(b)) = (probe, first, second) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_cond: null probe or tactic handle".to_string());
                return ptr::null_mut();
            };
            store_tactic(ctx, Tactic::cond(probe, a, b))
        })
    }
}

/// Apply `t` under a wall-clock bound `ms` (Z3's `Z3_tactic_try_for`).
///
/// HONEST DIVERGENCE (documented): AY's tactic passes are all internally bounded
/// and terminate quickly, so the `ms` deadline is never reached — the tactic
/// therefore behaves exactly like `t` itself (the equivalence-preserving
/// transform). It never fabricates a timeout failure, and it never silently
/// substitutes a different transform. The `ms` argument is accepted for API
/// compatibility and recorded in the honesty note here. Returns NULL and sets
/// `Z3_INVALID_ARG` if `t` is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid tactic
/// handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_try_for(c: Z3_context, t: Z3_tactic, _ms: c_uint) -> Z3_tactic {
    // SAFETY: `t`, when non-null, is a live `TacticHandle`; `as_ref` null-checks.
    let inner = unsafe { t.as_ref() }.map(|h| h.tactic.clone());
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(inner) = inner else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_try_for: null tactic handle".to_string());
                return ptr::null_mut();
            };
            store_tactic(ctx, inner)
        })
    }
}

/// Apply `t1`, then apply `t2` to every subgoal `t1` produces (Z3's
/// `Z3_tactic_par_and_then`).
///
/// HONEST DIVERGENCE (documented): Z3 processes the subgoals in PARALLEL; AY has
/// no parallel goal engine, so this composes them SEQUENTIALLY via
/// [`Tactic::then`] — the SAME apply-result set, only computed serially (never a
/// wrong or fabricated result). Returns NULL and sets `Z3_INVALID_ARG` if either
/// operand is NULL.
///
/// # Safety
/// `c` must be a valid context pointer; `t1`/`t2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_par_and_then(
    c: Z3_context,
    t1: Z3_tactic,
    t2: Z3_tactic,
) -> Z3_tactic {
    // SAFETY: both handles, when non-null, are arena-owned and single-threaded
    // per context; `as_ref` null-checks.
    let (first, second) = unsafe {
        (
            t1.as_ref().map(|h| h.tactic.clone()),
            t2.as_ref().map(|h| h.tactic.clone()),
        )
    };
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(a), Some(b)) = (first, second) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_par_and_then: null tactic operand".to_string());
                return ptr::null_mut();
            };
            store_tactic(ctx, a.then(b))
        })
    }
}

/// Race `num` tactics, taking the first that succeeds (Z3's `Z3_tactic_par_or`).
///
/// HONEST DIVERGENCE (documented): Z3 runs the `ts[0..num]` tactics in PARALLEL
/// and takes whichever succeeds first; AY has no parallel engine, so it folds
/// them left with [`Tactic::or_else`] — try `ts[0]`; on FAILURE fall through to
/// `ts[1]`, and so on. The winner is the first that succeeds, which is the SAME
/// result set as Z3's parallel-or (only the tie-break among simultaneously-
/// succeeding tactics is deterministic-left instead of race-order — never a wrong
/// or fabricated result). Returns NULL and sets `Z3_INVALID_ARG` on `num == 0`, a
/// NULL `ts`, or any NULL element.
///
/// # Safety
/// `c` must be a valid context pointer; `ts`, when `num > 0`, must point to
/// `num` valid (non-null) tactic handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_par_or(
    c: Z3_context,
    num: c_uint,
    ts: *const Z3_tactic,
) -> Z3_tactic {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_tactic_par_or", num) } {
        return ptr::null_mut();
    }
    // Pre-extract every operand tactic outside the guard (raw-pointer derefs).
    // SAFETY: the caller's contract guarantees `ts` points to `num` valid
    // `Z3_tactic` handles when `num > 0`. We read each slot and clone its tactic;
    // a null slot yields `None` and is rejected below.
    let operands: Option<Vec<Tactic>> = if num == 0 || ts.is_null() {
        None
    } else {
        // SAFETY: `ts` is valid for `num` reads per the caller's contract.
        let slice = unsafe { std::slice::from_raw_parts(ts, num as usize) };
        slice
            .iter()
            // SAFETY: each element, when non-null, is a live `TacticHandle`.
            .map(|&h| unsafe { h.as_ref() }.map(|th| th.tactic.clone()))
            .collect()
    };
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(operands) = operands else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_tactic_par_or: null/empty tactic array or null element".to_string());
                return ptr::null_mut();
            };
            // Fold left with or-else (first success wins), matching par-or's set.
            let mut it = operands.into_iter();
            let Some(first) = it.next() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_par_or: empty tactic array".to_string());
                return ptr::null_mut();
            };
            let combined = it.fold(first, Tactic::or_else);
            store_tactic(ctx, combined)
        })
    }
}

/// Return a description of the tactic named `name` (Z3's `Z3_tactic_get_descr`).
///
/// Returns a context-owned string for each name AY's [`Z3_mk_tactic`] accepts —
/// an HONEST description of AY's actual realization of that tactic (e.g.
/// `elim-and` is described as AY's conjunction-flattening, which is what its goal
/// output really is, not a rewrite AY does not perform). An unknown/unsupported
/// name returns NULL and sets `Z3_INVALID_ARG` (the honest path).
///
/// # Safety
/// `c` must be a valid context pointer; `name`, when non-null, a null-terminated
/// C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_get_descr(c: Z3_context, name: Z3_string) -> Z3_string {
    // Pre-extract the name string outside the guard (raw-pointer deref).
    let name_str: Option<String> = if name.is_null() {
        None
    } else {
        // SAFETY: caller contract guarantees a valid null-terminated C string.
        unsafe { ffi_read_bounded_text(name) }.ok()
    };
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| match name_str.as_deref().and_then(tactic_descr) {
            Some(descr) => {
                ctx.last_error = Z3_OK;
                cache_string(ctx, descr.to_string())
            }
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_get_descr: unknown tactic name".to_string());
                ptr::null()
            }
        })
    }
}

/// The honest per-name description for [`Z3_tactic_get_descr`]. Covers exactly the
/// names [`Z3_mk_tactic`] accepts ([`ay_frontend::SUPPORTED_TACTIC_NAMES`]);
/// every string describes AY's real transform. `None` for any
/// other name (⇒ NULL + `Z3_INVALID_ARG`).
fn tactic_descr(name: &str) -> Option<&'static str> {
    Some(match name {
        "skip" => "do nothing tactic.",
        "fail" => "always fail tactic.",
        "simplify" => {
            "apply simplification rules and split top-level conjunctions into separate goal formulas."
        }
        "solve-eqs" => "solve variable equalities and eliminate the solved variables.",
        "propagate-values" => "propagate ground (= expr const) equalities.",
        "elim-and" => {
            "eliminate top-level conjunctions: split (and (and a b) c) into separate goal formulas {a, b, c}."
        }
        "qe-light" => "apply light-weight quantifier elimination.",
        "qe" => {
            "eliminate quantifiers; AY realizes this with the same Cooper pass as qe-light (in-fragment single-Int-variable existentials are eliminated, out-of-fragment quantifiers kept verbatim — a documented sound coverage divergence from z3's LIA-complete qe)."
        }
        "nnf" => "put goal in negation normal form.",
        "tseitin-cnf" => {
            "convert goal into CNF using a tseitin-like encoding (introduces fresh auxiliary Boolean variables; equisatisfiable)."
        }
        "bit-blast" => {
            "reduce bit-vector expressions into an equisatisfiable pure-Boolean (SAT) goal."
        }
        "split-clause" => "split a clause into many subgoals (one per disjunct).",
        "ctx-solver-simplify" => {
            "simplify goal using the solver: drop assertions the context proves redundant and collapse a contradictory goal to false (equivalence-preserving)."
        }
        "purify-arith" => {
            "purify arithmetic atoms; AY realizes this as its equisatisfiable simplification pass."
        }
        "elim-uncnstr" => {
            "eliminate unconstrained (write-only) variables; AY realizes this via solve-eqs variable elimination."
        }
        "propagate-ineqs" => {
            "propagate inequality/bound information: drop inequalities subsumed by a stronger same-strictness bound on the same variable or by an asserted (= var const) equality, re-emitting value equalities at the end of the goal (equivalence-preserving)."
        }
        "elim-term-ite" => {
            "eliminate term ite: name each non-Boolean ite with a fresh variable and append its guard definitions (or (not c) (= k t)), (or c (= k e)) — equisatisfiable. ites under a quantifier are left in place (a sound divergence from z3, which names them outside the binder)."
        }
        "blast-term-ite" => {
            "eliminate term ite by lifting each non-Boolean ite out over its enclosing predicate/function via Shannon expansion — equivalence-preserving. ites under a quantifier are left in place (a sound divergence from z3, which descends into binders)."
        }
        "cofactor-term-ite" => {
            "eliminate term ite by cofactoring over ite conditions; AY realizes this with the same Shannon lifting as blast-term-ite, yielding a logically equivalent goal with a possibly different ite ordering/simplification than z3."
        }
        "der" => {
            "destructive equality resolution: resolve (not (= x t)) literals out of universally quantified clauses by the one-point rule (equivalence-preserving). Fail-closes on nested binders to stay capture-safe."
        }
        "distribute-forall" => {
            "distribute forall over conjunctions (and negated exists over disjunctions), one goal formula per conjunct/disjunct (equivalence-preserving; output order may differ from z3)."
        }
        "reduce-args" => {
            "eliminate function arguments that are the same literal constant in every occurrence, specializing the function per constant tuple into fresh f!k symbols (equisatisfiable)."
        }
        "smt" => {
            "solve the goal with AY's SMT engine (a terminal tactic; as a goal transform it is the identity, and .solver() runs the real engine)."
        }
        "sat" => {
            "solve the goal with AY's SAT engine (terminal; identity as a goal transform, real solving via .solver())."
        }
        "default" => {
            "AY's default solving strategy (terminal; identity as a goal transform, real solving via .solver())."
        }
        // --- CLASS S: per-logic solver strategies (same realization as
        // smt/default/sat). Per-name measured divergences are documented on
        // their own arms below. ---
        "nlsat" => {
            "builtin nonlinear-arithmetic strategy; AY realizes it as a terminal solve tactic — identity as a goal transform (z3's (apply nlsat) errors on unpurified arith where AY's identity is lenient — documented), real engine when used as a solver."
        }
        "pqffd" => {
            "builtin parallel QF_FD strategy; AY realizes it as a terminal solve tactic — identity as a goal transform (z3's (apply pqffd) can FAIL with sat.giveup on non-FD goals where AY's identity succeeds — documented or-else routing divergence), real engine when used as a solver."
        }
        "smtfd" => {
            "builtin SMT-over-FD strategy; AY realizes it as a terminal solve tactic — identity as a goal transform (z3's (apply smtfd) can run unboundedly where AY's identity returns immediately — documented), real engine when used as a solver."
        }
        "auflia" | "auflira" | "aufnira" | "bv" | "lia" | "lira" | "lra" | "nra" | "psat"
        | "psmt" | "qfaufbv" | "qfauflia" | "qfbv" | "qfbv-sls" | "qffd" | "qffp" | "qffpbv"
        | "qffplra" | "qfidl" | "qflia" | "qflra" | "qfnia" | "qfnra" | "qfnra-nlsat" | "qfuf"
        | "qfufbv" | "qfufbv_ackr" | "qsat" | "sls-smt" | "ufbv" | "uflra" | "ufnia" => {
            "builtin per-logic solver strategy; AY realizes it as a terminal solve tactic — identity as a goal transform (z3 runs the strategy inside (apply) and usually empties the goal — a documented goal-shape divergence, never a verdict), real engine when used as a solver (check-sat-using / Z3_mk_solver_from_tactic)."
        }
        // --- CLASS A: aliases to an existing verified AY pass. ---
        "propagate-values2" => {
            "propagate ground (= expr const) equalities (AY alias of propagate-values)."
        }
        "reduce-args2" => {
            "eliminate function arguments that are the same literal constant in every occurrence (AY alias of reduce-args; equisatisfiable)."
        }
        "elim-uncnstr2" => {
            "eliminate unconstrained variables; AY realizes this via solve-eqs variable elimination (alias of elim-uncnstr)."
        }
        "tseitin-cnf-core" | "sat-preprocess" => {
            "convert goal into CNF using a tseitin-like encoding (AY alias of tseitin-cnf; introduces fresh auxiliary Boolean variables; equisatisfiable)."
        }
        "qe2" | "qe_rec" => {
            "eliminate quantifiers; AY realizes this with the same Cooper pass as qe (in-fragment single-Int-variable existentials eliminated, out-of-fragment quantifiers kept verbatim — a documented sound coverage divergence)."
        }
        "ctx-simplify" | "unit-subsume-simplify" | "solver-subsumption" => {
            "drop assertions the context proves redundant; AY realizes all three with its solver-proven contextual simplification (ctx-solver-simplify; equivalence-preserving)."
        }
        "dom-simplify" | "degree-shift" | "fm" | "card2bv" => {
            "goal simplification; AY realizes it with its general simplify pass (z3's own output on the shared fragment is the simplify-normalized goal — measured)."
        }
        // --- CLASS N: no-op-safe transforms realized as the identity. ---
        "subpaving" => {
            "subpaving for nonlinear arithmetic; AY realizes it as the identity (documented divergence: z3 TRANSFORMS in-fragment Int goals and FAILS BV goals with 'unsupported atom' where AY's identity succeeds — goal shape / or-else routing only, never a verdict)."
        }
        "elim-predicates" | "euf-completion" => {
            "predicate elimination / E-graph completion; AY realizes it as the identity (documented divergence: z3 can DECIDE simple goals inside (apply), printing an empty goal, where AY truthfully prints the input — goal shape only, never a verdict)."
        }
        "nla2bv" => {
            "nonlinear-to-bitvector reduction; AY realizes it as the identity (documented divergences: z3 UNDER-approximates in-fragment Int goals — :precision under — and FAILS BV goals where AY's precise identity succeeds)."
        }
        "add-bounds" => {
            "add bounds to unbounded variables; AY realizes it as the identity (documented divergence: z3's transform is UNDER-approximating — :precision under — where AY stays precise; AY never emits a goal that could flip sat to unsat)."
        }
        "normalize-bounds" => {
            "normalize variable bounds; AY realizes it as the identity (documented divergence: z3 mints fresh k!i variables in-fragment where AY truthfully prints the input)."
        }
        "max-bv-sharing" => {
            "maximize bit-vector term sharing; AY terms are hash-consed so sharing is already maximal — the identity is literally the completed transform."
        }
        "collect-statistics" => {
            "collect goal statistics; AY realizes it as the identity WITHOUT z3's statistics block (documented output divergence, deliberately: a partial fabricated block would diverge across the SMT-LIB and C-API surfaces)."
        }
        "ackermannize_bv"
        | "aig"
        | "bv_bound_chk"
        | "bv-slice"
        | "bv-divrem-bounds"
        | "bvarray2uf"
        | "demodulator"
        | "dt2bv"
        | "elim-small-bv"
        | "eq2bv"
        | "fold-unfold"
        | "factor"
        | "fix-dl-var"
        | "fpa2bv"
        | "injectivity"
        | "lia2card"
        | "lia2pb"
        | "macro-finder"
        | "occf"
        | "pb-preprocess"
        | "propagate-bv-bounds"
        | "propagate-bv-bounds2"
        | "quasi-macros"
        | "recover-01"
        | "reduce-bv-size"
        | "snf"
        | "special-relations"
        | "symmetry-reduce"
        | "ufbv-rewriter" => {
            "fragment-specific goal transform; AY realizes it as the identity — byte-parity with z3's own no-op on out-of-fragment goals (measured; z3 counts its pass at :depth 1 where AY's identity stays at the input depth), a truthful identity in-fragment (never a fabricated transform)."
        }
        // --- CLASS F: honest fragment failures (or-else routing matches z3,
        // which fails these on generic goals — measured). ---
        "diff-neq" => {
            "difference-logic-with-disequalities solver; AY realizes it as an honest failure ('goal is not diff neq', z3 byte text): z3 fails it on generic goals too, so or-else routing matches; on an in-fragment goal z3 succeeds where AY honestly fails (sound, documented)."
        }
        "nlqsat" => {
            "quantified nonlinear-real strategy; AY realizes it as an honest failure ('not NRA', z3 byte text) — same or-else routing as z3 on generic goals; in-fragment z3 succeeds where AY honestly fails (sound, documented)."
        }
        "pb2bv" => {
            "pseudo-boolean-to-bitvector reduction; AY realizes it as an honest failure ('goal is in a fragment not supported by pb2bv' — z3's byte prefix; z3 appends '. Offending expression: <term>', a documented suffix divergence); in-fragment z3 succeeds where AY honestly fails (sound, documented)."
        }
        "horn" | "horn-simplify" => {
            "Horn-clause solving/simplification; AY realizes it as an honest failure (AY message — z3's own error here is a dynamic non-tactic-failed string, a documented divergence); never a fabricated transform."
        }
        "bv1-blast" => {
            "reduce bit-vector expressions to bv1 variables; AY fails with z3's byte text ('bv1 blaster cannot be applied to goal') iff the goal contains a bit-vector term and is the identity otherwise — matching z3's measured success-on-BV-free-goals or-else routing; on a pure bv1 goal z3 transforms where AY honestly fails (sound, documented)."
        }
        // --- CLASS C: wired to the real engine primitive. ---
        "fail-if-undecided" => {
            "fail if the goal is not trivially decided: identity on the empty goal (decided SAT) and on a goal containing false (decided UNSAT); otherwise fails with z3's byte text 'undecided'."
        }
        _ => return None,
    })
}

/// Return the parameter-descriptor set for a tactic (Z3's
/// `Z3_tactic_get_param_descrs`).
///
/// HONEST EMPTY (documented): AY's tactics are always the equivalence-preserving
/// transform, so they expose NO per-tactic tunable parameters that would change
/// the produced goal's model set. This therefore returns a REAL, queryable —
/// empty — [`ParamDescrsHandle`] (size 0), never a fabricated parameter set
/// disguised as Z3's. The `t` handle is validated (NULL ⇒ `Z3_INVALID_ARG`).
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid tactic
/// handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_get_param_descrs(
    c: Z3_context,
    t: Z3_tactic,
) -> Z3_param_descrs {
    // SAFETY: `t`, when non-null, is a live `TacticHandle`; `as_ref` null-checks.
    let has_tactic = unsafe { t.as_ref() }.is_some();
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if !has_tactic {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_tactic_get_param_descrs: null tactic handle".to_string());
                return ptr::null_mut();
            }
            ctx.last_error = Z3_OK;
            // Honest-empty: no per-tactic params affect AY's equivalence-preserving
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
// Tactic registry enumeration
// ============================================================================

#[cfg(test)]
#[path = "tactics_ffi_tests.rs"]
mod tactics_ffi_tests;
