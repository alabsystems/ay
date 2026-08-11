// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible solver lifecycle and check-sat functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint};
use std::ptr;

use ay_dpll::api::{
    ConsumerAcceptanceError, ModelValue, RecExpandError, SolveResult, SolverError, Sort, Term,
    TermKind, VerifiedSolveResult,
};
use ay_frontend::Command;

use super::{
    apply_supported_params, bounded_array_ext_consequences, cache_ast_vector, cache_string,
    ensure_cross_context_translation_semantics, ffi_count_within_limit, ffi_guard_ast,
    ffi_guard_const_ptr, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void,
    ffi_read_bounded_parser_file, ffi_read_bounded_parser_text, ffi_read_bounded_text,
    finite_set_decision_gate, reachable_finite_set_axioms, require_term_ast, require_term_asts,
    term_to_ast, transfer_cross_context_ffi_metadata, DecisionOwnerFamily, FiniteSetDecisionGate,
    ModelHandle, SolverCheckOutcome, Z3Context, Z3SolverHandle, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_func_decl, Z3_model, Z3_params, Z3_solver, Z3_sort, Z3_string, Z3_symbol, Z3_EXCEPTION,
    Z3_INVALID_ARG, Z3_INVALID_USAGE, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF, Z3_OK,
};

/// Translate a `VerifiedSolveResult` into the Z3 C API lbool return value,
/// routing through the consumer acceptance boundary (#8725).
///
/// SAT results that did not go through model validation (e.g., `skip_model_eval`
/// paths in the executor) are rejected with `Z3_L_UNDEF` and the context's
/// `last_error` is set to `Z3_EXCEPTION`. This prevents unvalidated SAT from
/// escaping the FFI boundary to downstream consumers (model-checker-consumer, z3-compat shim).
///
/// UNSAT and Unknown results pass through unchanged — the validation boundary
/// only gates SAT.
pub(super) fn solve_lbool_with_acceptance(
    ctx: &mut Z3Context,
    result: VerifiedSolveResult,
) -> c_int {
    solve_lbool_from_consumer_acceptance(ctx, result.accept_for_consumer())
}

/// Fail closed when an auxiliary decision query cannot run every acceptance
/// gate that protects the ordinary solver-check surface.
///
/// Consequence and implied-equality probes currently have no user-propagator
/// final-check loop and no transitive-closure model verifier. A raw backend SAT
/// result is therefore not enough to establish that their baseline is
/// satisfiable under the full public semantics.
pub(super) fn auxiliary_query_acceptance_is_supported(
    ctx: &mut Z3Context,
    has_user_propagator: bool,
    operation: &str,
) -> bool {
    let reason = if has_user_propagator {
        Some("a user propagator is active, but this auxiliary query has no final-check loop")
    } else if !ctx.transitive_closure_regs.is_empty() {
        Some(
            "transitive-closure semantics are active, but this auxiliary query has no model verifier",
        )
    } else {
        None
    };
    let Some(reason) = reason else {
        return true;
    };
    ctx.last_error = Z3_INVALID_USAGE;
    ctx.error_msg = Some(format!(
        "{operation}: {reason}; returning unknown fail-closed"
    ));
    false
}

/// Map the result of AY's consumer boundary to the Z3 lbool/error surface.
///
/// Keeping this mapper private is load-bearing: normal callers must supply a
/// `VerifiedSolveResult` to `solve_lbool_with_acceptance` and therefore cannot
/// inject a caller-chosen SAT-validation outcome.
fn solve_lbool_from_consumer_acceptance(
    ctx: &mut Z3Context,
    accepted: Result<&SolveResult, ConsumerAcceptanceError>,
) -> c_int {
    match accepted {
        Ok(SolveResult::Sat) => Z3_L_TRUE,
        Ok(SolveResult::Unsat(_)) => Z3_L_FALSE,
        // `SolveResult` is `#[non_exhaustive]`; Unknown and any future
        // not-yet-determined variants map to `Z3_L_UNDEF`.
        Ok(SolveResult::Unknown) | Ok(_) => Z3_L_UNDEF,
        Err(err) => {
            // `ConsumerAcceptanceError` is `#[non_exhaustive]`. All current and
            // future rejection reasons must surface as `Z3_L_UNDEF` with an
            // exception on the context — unvalidated SAT must never leak out
            // of the FFI as `Z3_L_TRUE`.
            let msg = match err {
                ConsumerAcceptanceError::SatModelNotValidated => {
                    "sat result rejected at consumer boundary: model validation did not run"
                        .to_string()
                }
                other => format!("sat result rejected at consumer boundary: {other}"),
            };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(msg);
            Z3_L_UNDEF
        }
    }
}

/// Apply finite-set obligations derived from one concrete decision goal.
///
/// A finite-set binder invalidates both polarities of the unrestricted-array
/// relaxation. An arbitrary finite-set value only invalidates SAT; UNSAT is
/// preserved by the over-approximation.
pub(crate) fn apply_finite_set_decision_gate(
    ctx: &mut Z3Context,
    lbool: c_int,
    gate: &FiniteSetDecisionGate,
    operation: &str,
) -> c_int {
    if let Some(reason) = &gate.quantifier_reason {
        ctx.last_error = Z3_OK;
        ctx.error_msg = Some(format!(
            "{operation}: finite-set decision result is not certified: {reason}; \
             returning unknown fail-closed"
        ));
        return Z3_L_UNDEF;
    }
    if lbool == Z3_L_TRUE {
        if let Some(reason) = &gate.arbitrary_reason {
            ctx.last_error = Z3_OK;
            ctx.error_msg = Some(format!(
                "{operation}: finite-set SAT result is not certified: {reason}; \
                 returning unknown fail-closed"
            ));
            return Z3_L_UNDEF;
        }
    }
    lbool
}

/// Exercise the FFI rejection mapping without exporting a constructor that can
/// fabricate `VerifiedSolveResult` in production builds.
#[cfg(test)]
pub(super) fn solve_lbool_from_consumer_rejection_for_testing(
    ctx: &mut Z3Context,
    error: ConsumerAcceptanceError,
) -> c_int {
    solve_lbool_from_consumer_acceptance(ctx, Err(error))
}

// ---- Solver lifecycle ----

/// Record the honest error for a null `Z3_solver` handle.
///
/// Every solver-state function routes through the HANDLE (not the context):
/// each `Z3_solver` owns its own assertion stack and check artefacts, so a
/// null handle cannot be silently mapped to shared context state. Call sites
/// null-check via `s.as_mut()` (the compiler-scoped borrow pattern from
/// #8568) and report through this helper on `None`.
fn note_null_solver_handle(ctx: &mut Z3Context, operation: &str) {
    ctx.last_error = Z3_INVALID_ARG;
    ctx.error_msg = Some(format!("{operation}: null Z3_solver handle"));
}

/// Create a solver.
///
/// The returned handle owns its own assertion stack, independent of every
/// other solver on the same context (Z3 semantics). It shares the context's
/// term arena: ASTs built on the context can be asserted on any of its solvers.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_solver(c: Z3_context) -> Z3_solver {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if !ctx.claim_decision_owner(DecisionOwnerFamily::Solver, "Z3_mk_solver") {
                return ptr::null_mut();
            }
            let handle = Box::into_raw(Box::new(Z3SolverHandle::new(None)));
            ctx.solver_handle_cache.push(handle);
            ctx.last_error = Z3_OK;
            handle
        })
    }
}

/// Create a solver for a specific logic (same as `Z3_mk_solver` in AY).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_solver_for_logic(c: Z3_context, _logic: Z3_symbol) -> Z3_solver {
    // SAFETY: Delegating to `Z3_mk_solver`, which has the same `# Safety` requirements as this
    // function. The caller's guarantees are passed through unchanged.
    unsafe { Z3_mk_solver(c) }
}

/// Increment solver reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_inc_ref(_c: Z3_context, _s: Z3_solver) {}

/// Decrement solver reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_dec_ref(_c: Z3_context, _s: Z3_solver) {}

/// Push a scope on THIS solver handle's assertion stack.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_push(c: Z3_context, s: Z3_solver) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_push") {
                return;
            }
            let Some(handle) = s.as_mut() else {
                note_null_solver_handle(ctx, "Z3_solver_push");
                return;
            };
            handle.scope_markers.push(handle.assertions.len());
            handle.tracked_scope_markers.push(handle.tracked.len());
            handle.clear_check_artifacts();
        });
    }
}

/// Pop `n` scopes from THIS solver handle's assertion stack.
///
/// Popping more scopes than were pushed sets `Z3_EXCEPTION` (scope underflow)
/// and leaves the handle unchanged.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_pop(c: Z3_context, s: Z3_solver, n: c_uint) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_pop") {
                return;
            }
            let Some(handle) = s.as_mut() else {
                note_null_solver_handle(ctx, "Z3_solver_pop");
                return;
            };
            let n = n as usize;
            if n > handle.scope_markers.len() {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!(
                    "Z3_solver_pop: scope underflow (pop {n} with {} scopes pushed)",
                    handle.scope_markers.len()
                ));
                return;
            }
            if n > 0 {
                let target = handle.scope_markers[handle.scope_markers.len() - n];
                // `tracked_scope_markers` is kept exactly parallel to
                // `scope_markers` (both pushed on every `Z3_solver_push`), so it
                // has an entry at the same offset; drop the tracked pairs added
                // in the popped scopes as well.
                let tracked_target =
                    handle.tracked_scope_markers[handle.tracked_scope_markers.len() - n];
                handle
                    .scope_markers
                    .truncate(handle.scope_markers.len() - n);
                handle
                    .tracked_scope_markers
                    .truncate(handle.tracked_scope_markers.len() - n);
                handle.assertions.truncate(target);
                handle.tracked.truncate(tracked_target);
                handle.clear_check_artifacts();
            }
        });
    }
}

/// Remove all assertions from THIS solver handle.
///
/// Matches Z3: only the solver's formulas are removed. Declarations and ASTs
/// are context-owned and remain valid, and other solvers on the same context
/// are untouched.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_reset(c: Z3_context, s: Z3_solver) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_reset") {
                return;
            }
            let Some(handle) = s.as_mut() else {
                note_null_solver_handle(ctx, "Z3_solver_reset");
                return;
            };
            handle.assertions.clear();
            handle.scope_markers.clear();
            handle.tracked.clear();
            handle.tracked_scope_markers.clear();
            handle.clear_check_artifacts();
        });
    }
}

/// Assert a formula on THIS solver handle.
///
/// The formula is recorded on the handle's own assertion stack (independent of
/// every other solver on the context) and evaluated at the next check.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_assert(c: Z3_context, s: Z3_solver, a: Z3_ast) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_assert") {
                return;
            }
            let Some(handle) = s.as_mut() else {
                note_null_solver_handle(ctx, "Z3_solver_assert");
                return;
            };
            let Some(term) = require_term_ast(ctx, a, "Z3_solver_assert", "formula") else {
                return;
            };
            // Same sort validation (and error text) as `Solver::try_assert_term`,
            // performed eagerly at assert time like the Z3 C API.
            let sort = ctx.solver.term_sort(term);
            if sort != Sort::Bool {
                let e = SolverError::SortMismatch {
                    operation: "assert_term",
                    expected: "Bool",
                    got: vec![sort],
                };
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            handle.assertions.push(term);
            handle.clear_check_artifacts();
        });
    }
}

/// Set solver params.
///
/// Only `timeout` is currently honored by AY.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_set_params(c: Z3_context, _s: Z3_solver, p: Z3_params) {
    if c.is_null() || p.is_null() {
        return;
    }
    // SAFETY: `p` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.params` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let params = unsafe { &(*p).params };
    // Clone params to avoid referencing raw pointer inside catch_unwind
    let params_owned: Vec<(String, String)> = params.clone();
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_set_params") {
                return;
            }
            apply_supported_params(&mut ctx.solver, &params_owned);
        });
    }
}

/// Check THIS handle's assertions (optionally under assumptions) against the
/// context's shared solve engine.
///
/// This is the per-handle check primitive: the engine's assertion stack is
/// REPLACED with exactly this handle's assertion list — with its tactic
/// applied first, when it has one — via `reset-assertions` + re-assert, and
/// then checked. Assertions belonging to other handles are never visible to
/// this check (the reset wipes whatever goal the previous check loaded), so
/// handles on one context are fully independent, matching Z3.
///
/// `reset-assertions` preserves the term arena and all declarations, so every
/// AST handle stays valid across checks. Every queryable artefact of this
/// check — model, unsat assumptions, reason-unknown, proof text — is
/// MATERIALIZED into the handle right after the check as an owned SNAPSHOT that
/// no longer references the engine's live check state. `Z3_model` is a genuine
/// snapshot: `Z3_model_eval` and the other model queries read ONLY that
/// captured value (there is no live-state compound fallback), so a LATER check
/// by any handle — which replaces the engine's transient state — leaves each
/// handle's already-materialized artefacts answering from the check that
/// produced them. This snapshot semantics is what keeps handles on one context
/// fully independent.
///
/// # Safety
/// `s`, when non-null, must point to a valid `Z3SolverHandle` owned by `ctx`'s
/// handle arena. The Z3 C API is single-threaded per context, so the mutable
/// borrow of the handle cannot race with another reference.
/// Assert the context-global background axioms (special-relation order axioms +
/// `Char`-sort range invariants) into the shared engine.
///
/// MUST be called AFTER the handle's goal has been loaded (post
/// `try_reset_assertions` + goal re-assert) at every solve site, so these
/// theory-internal constraints reach the check. Returns the engine error text on
/// the first failed assert.
///
/// SOUNDNESS: every axiom is a pure constraint over a FRESH order predicate or a
/// bounded `Char` code point (see [`Z3Context::background_axioms`]), so it can
/// only shrink the model set — never flip a Z3-unsat into an AY-sat — and each is
/// satisfiable in isolation, so it introduces no spurious unsat. They are not
/// part of any handle's `assertions`, so assertion/unsat-core queries stay faithful.
pub(crate) fn assert_background_axioms(
    ctx: &mut Z3Context,
    include_rec_def_axioms: bool,
) -> Result<(), String> {
    if ctx.background_axioms.is_empty()
        && (!include_rec_def_axioms || ctx.global_definition_axioms.is_empty())
    {
        return Ok(());
    }
    // Clone first: `Term` is a Copy id, so this avoids borrowing
    // `ctx.background_axioms` while `ctx.solver` is mutably borrowed.
    let mut axioms = ctx.background_axioms.clone();
    // The quantified recursive-definition axioms are OMITTED when the caller
    // fully expanded every rec-f application into the goal (`include_rec_def_
    // axioms == false`): the expanded goal already carries the definitional
    // content at the used points, and omitting the axioms is what turns
    // `fact(5) == 120` from `unknown` into `sat` (matching z3's on-demand
    // unfolding semantics; z3 likewise does not require a total model of an
    // everywhere-defined recursive function at unused points).
    if include_rec_def_axioms {
        axioms.extend_from_slice(&ctx.global_definition_axioms);
    }
    for term in axioms {
        if let Err(e) = ctx.solver.try_assert_term(term) {
            return Err(format!("{e}"));
        }
    }
    Ok(())
}

/// Install finite-set witness definitions reachable from this decision goal.
///
/// These axioms are context-owned semantic metadata, but unlike the ordinary
/// theory-global axioms they are not relevant to sibling handles or unused AST
/// terms. Call this after loading the current goal, beside
/// [`assert_background_axioms`].
pub(crate) fn assert_reachable_finite_set_axioms(
    ctx: &mut Z3Context,
    roots: &[Term],
) -> Result<(), String> {
    for term in reachable_finite_set_axioms(ctx, roots) {
        if let Err(error) = ctx.solver.try_assert_term(term) {
            return Err(format!("{error}"));
        }
    }
    Ok(())
}

/// How the current decision query relates to the context's recursive
/// definitions (`Z3_add_rec_def`), decided per check by
/// [`ay_dpll::api::Solver::try_expand_rec_defs`].
pub(crate) enum RecDefMode {
    /// No recursive definitions registered: nothing changes.
    None,
    /// Every rec-f application in the goal/assumptions/lemmas was fully
    /// expanded away; solve the expanded goal WITHOUT the defining axioms.
    Expanded,
    /// Expansion failed: solve the ORIGINAL goal and demote a `sat` verdict
    /// to `unknown` — a rec-f application must never reach a released `sat`
    /// as a plain uninterpreted function. Carries the honest reason.
    ///
    /// `keep_axioms` picks the residual solving strategy:
    /// * `true` (cheap SHAPE refusals — capture risk, arity/sort mismatch,
    ///   undefined-reaching definitions): solve WITH the quantified defining
    ///   axioms, keeping the measured axiom-driven `unsat` power.
    /// * `false` (the GRIND class — depth/budget/wall-time exhaustion, i.e.
    ///   symbolic-argument recursion, divergence, un-foldable ADT guards):
    ///   solve WITHOUT them. The quantifier engine's instantiation budgets
    ///   burn ~30s on these axiom shapes regardless of the configured
    ///   timeout (measured; the spin is in quantifier preprocessing), so the
    ///   axioms may not be injected on a path that must stay live. UNSAT
    ///   from the goal alone is still sound (fewer constraints), and it is
    ///   what turns `f(n)==4 ∧ false` from a 30-112s `unknown` into an
    ///   instant `unsat` (z3 parity).
    Residual { reason: String, keep_axioms: bool },
}

/// Nesting-depth limit for check-time expansion, mirroring the SMT-LIB
/// path's `MAX_FUN_EXPANSION_DEPTH = 1000`.
pub(crate) const REC_DEF_MAX_ROUNDS: usize = 1000;
/// Work budget (DAG nodes visited + scan×frontier substitution cost) for one
/// expansion attempt: bounds WORK, so a breadth-exploding definition fails
/// closed in well under a second instead of hanging a decision call.
pub(crate) const REC_DEF_WORK_BUDGET: usize = 5_000_000;
/// Wall-clock budget for one expansion attempt. The work-unit-to-time ratio is
/// shape-dependent (ground ADT constructor guards never fold, so the dag GROWS
/// every round and per-unit cost explodes — the measured multi-minute grind
/// class, skeptic finding 1), so expansion is additionally deadline-bounded:
/// exceeding it is an ordinary expansion failure → residual fail-close.
pub(crate) const REC_DEF_WALL_BUDGET_MS: u64 = 1_000;

/// The wall-clock deadline for one rec-def expansion attempt: the fixed
/// [`REC_DEF_WALL_BUDGET_MS`] cap, tightened to the engine's configured
/// check-sat timeout when that is smaller (expansion runs BEFORE the engine
/// phase, so it must never consume more than the caller's whole budget).
pub(crate) fn rec_def_expansion_deadline(ctx: &Z3Context) -> std::time::Instant {
    let mut budget = std::time::Duration::from_millis(REC_DEF_WALL_BUDGET_MS);
    if let Some(t) = ctx.solver.timeout() {
        if t < budget {
            budget = t;
        }
    }
    std::time::Instant::now() + budget
}

/// The Finding-2 gate: the defined names whose unfolding could SURFACE a
/// rec-DECLARED-but-UNDEFINED function (`Z3_mk_rec_func_decl` with no
/// `Z3_add_rec_def` yet), computed against the context's current registry.
///
/// A goal that USES such a defined name must fail closed: real z3 treats a
/// forced unfold through an undefined recfun as inconsistent (`unsat` even for
/// facts a plain-UF reading satisfies — measured on 4.15.4), while treating it
/// as a plain UF answers `sat`; AY releases neither verdict. DIRECT use of an
/// undefined rec decl (no defined body in between) stays plain-UF — that is
/// the case where z3 agrees with the UF reading.
pub(crate) fn rec_defs_tainted_by_undefined(ctx: &Z3Context) -> std::collections::HashSet<String> {
    if ctx.rec_fun_defs.is_empty() || ctx.rec_declared_names.is_empty() {
        return std::collections::HashSet::new();
    }
    let undefined: std::collections::HashSet<String> = ctx
        .rec_declared_names
        .iter()
        .filter(|n| !ctx.rec_fun_defs.contains_key(n.as_str()))
        .cloned()
        .collect();
    if undefined.is_empty() {
        return std::collections::HashSet::new();
    }
    ctx.solver
        .rec_def_names_reaching(&ctx.rec_fun_defs, &undefined)
}

pub(crate) unsafe fn check_solver_handle(
    ctx: &mut Z3Context,
    s: Z3_solver,
    assumptions: Option<&[Term]>,
    extra_lemmas: &[Term],
) -> c_int {
    if !ctx.decision_engine_is_usable("Z3_solver_check") {
        return Z3_L_UNDEF;
    }
    // SAFETY: `s` is null-checked by `as_mut`; the handle, when non-null, was
    // produced by `Z3_mk_solver`/`Z3_mk_solver_from_tactic` and lives in the
    // context arena (a separate allocation from `*ctx`, so the two &mut do not
    // alias). Single-threaded per context, so no race.
    let Some(handle) = (unsafe { s.as_mut() }) else {
        note_null_solver_handle(ctx, "Z3_solver_check");
        return Z3_L_UNDEF;
    };
    // Stale artefacts from a previous check are dropped up front; the ones for
    // THIS check are re-materialized below.
    handle.clear_check_artifacts();

    /// Publish an honest UNKNOWN for an early or post-backend rejection.
    fn record_unknown(ctx: &mut Z3Context, handle: &mut Z3SolverHandle) {
        if handle.last_reason_unknown.is_none() {
            handle.last_reason_unknown = ctx
                .error_msg
                .clone()
                .or_else(|| ctx.solver.reason_unknown_smtlib());
        }
        handle.record_check_outcome(SolverCheckOutcome::Unknown);
    }

    // The goal is the handle's own assertion list, transformed by its tactic
    // when it has one (equivalence-preserving: identical verdict and models).
    let mut goal = handle.assertions.clone();
    // Snapshot the caller's own top-level assertions BEFORE a tactic can rewrite
    // the observable list: they are the keys the bounded-array extensionality
    // lemmas hang off (see `bounded_arrays`). A tactic is equivalence-preserving,
    // so a pre-transform assertion is still a fact of this check.
    let asserted_keys: Vec<Term> = handle.assertions.clone();
    // Tracking literals from `Z3_solver_assert_and_track`: every `p` is passed
    // as an assumption so the tracked assertion's contribution to an UNSAT is
    // reported by `Z3_solver_get_unsat_core` (a subset of these `p`s plus any
    // explicit check-assumptions — exactly Z3's assert-and-track core rule).
    let tracked_lits: Vec<Term> = handle.tracked.iter().map(|(p, _)| *p).collect();
    if let Some(tactic) = handle.tactic.clone() {
        match ctx.solver.apply_tactic_to_goal(&tactic, &mut goal) {
            Ok(progressed) => {
                // Persist the transformed goal as the handle's assertion list (it
                // is observable via `Z3_solver_get_assertions`, e.g. elim-and
                // yields the individual conjuncts after a check) — but only while
                // no scopes are open, because the scope markers index the
                // untransformed list.
                if progressed && handle.scope_markers.is_empty() {
                    handle.assertions = goal.clone();
                }
            }
            // HONEST FAILURE: the tactic produced NO goal (e.g. `bit-blast` on an
            // out-of-fragment bit-vector goal). Surface it as an error + `unknown`
            // rather than silently solving the untransformed goal — never a
            // fabricated verdict for a goal the tactic did not actually produce.
            Err(e) => {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                record_unknown(ctx, handle);
                return Z3_L_UNDEF;
            }
        }
    }

    // Effective assumptions = explicit check-assumptions ++ tracking literals.
    // When both are empty this is a plain `check_sat` (no assumption machinery),
    // preserving the original behavior for untracked solvers.
    let mut effective: Vec<Term> = Vec::new();
    if let Some(terms) = assumptions {
        effective.extend_from_slice(terms);
    }
    effective.extend(tracked_lits.iter().copied());

    // Check-time bounded expansion of recursive definitions (P1.1). Operates
    // on the LOCAL goal/assumption/lemma copies only — `handle.assertions`
    // and `Z3_solver_get_assertions` stay faithful to what the user asserted.
    // Fully expanded => solve the expanded problem WITHOUT the quantified
    // defining axioms; ANY failure => residual mode: original problem + the
    // axioms, and a SAT verdict is demoted to UNKNOWN below (fail-closed).
    let mut lemmas: Vec<Term> = extra_lemmas.to_vec();
    let mut finite_set_roots = goal.clone();
    finite_set_roots.extend(effective.iter().copied());
    finite_set_roots.extend(lemmas.iter().copied());
    let finite_set_gate = finite_set_decision_gate(ctx, &finite_set_roots);
    let mut rec_mode = RecDefMode::None;
    // `(expanded, original)` pairs for translating an engine unsat core over
    // EXPANDED assumptions back to the caller's original assumption terms.
    let mut rec_core_map: Vec<(Term, Term)> = Vec::new();
    if !ctx.rec_fun_defs.is_empty() {
        let mut batch: Vec<Term> = Vec::with_capacity(goal.len() + effective.len() + lemmas.len());
        batch.extend_from_slice(&goal);
        batch.extend_from_slice(&effective);
        batch.extend_from_slice(&lemmas);
        // Finding-2 gate FIRST: expansion of a defined body must never surface
        // a rec-declared-but-undefined function as a plain UF (z3 4.15.4
        // answers `unsat` in that window where the UF reading says `sat`; AY
        // releases neither — residual mode demotes SAT below).
        let tainted = rec_defs_tainted_by_undefined(ctx);
        if !tainted.is_empty() && ctx.solver.terms_mention_names(&batch, &tainted) {
            rec_mode = RecDefMode::Residual {
                reason: "a used definition depends on a recursive declaration with no \
                         definition"
                    .to_string(),
                keep_axioms: true,
            };
        } else {
            match ctx.solver.try_expand_rec_defs(
                &batch,
                &ctx.rec_fun_defs,
                REC_DEF_MAX_ROUNDS,
                REC_DEF_WORK_BUDGET,
                Some(rec_def_expansion_deadline(ctx)),
            ) {
                Ok(expanded) => {
                    let (new_goal, rest) = expanded.split_at(goal.len());
                    let (new_effective, new_lemmas) = rest.split_at(effective.len());
                    rec_core_map = new_effective
                        .iter()
                        .copied()
                        .zip(effective.iter().copied())
                        .collect();
                    goal = new_goal.to_vec();
                    effective = new_effective.to_vec();
                    lemmas = new_lemmas.to_vec();
                    rec_mode = RecDefMode::Expanded;
                }
                Err(e) => {
                    rec_mode = RecDefMode::Residual {
                        reason: e.to_string(),
                        // Depth/budget/wall-time exhaustion marks the GRIND
                        // class: injecting the quantified axioms on those
                        // shapes costs ~30s of instantiation-budget spin
                        // regardless of the configured timeout (measured).
                        // Shape refusals stay on the axiom path (cheap, and
                        // it keeps the verified axiom-driven unsat power).
                        keep_axioms: matches!(e, RecExpandError::UnsupportedShape(_)),
                    };
                }
            }
        }
    }

    // Public array extensionality over a BOUNDED carrier (see `bounded_arrays`).
    // Each equality is a consequence of a top-level assertion of THIS check, and
    // is released only after the whole term set this check will hand the engine
    // is re-verified to admit the canonical extension the proof needs — never
    // context-globally, and never for a goal holding an interpreted array term.
    // It stays out of `handle.assertions`, so `Z3_solver_get_assertions` and
    // unsat cores keep reporting only what the caller asserted.
    {
        let mut canonicity_roots: Vec<Term> = Vec::new();
        canonicity_roots.extend(asserted_keys.iter().copied());
        canonicity_roots.extend(goal.iter().copied());
        canonicity_roots.extend(effective.iter().copied());
        canonicity_roots.extend(lemmas.iter().copied());
        canonicity_roots.extend(ctx.background_axioms.iter().copied());
        canonicity_roots.extend(ctx.global_definition_axioms.iter().copied());
        canonicity_roots.extend(ctx.finite_set_reachable_axioms.values().flatten().copied());
        let mut keys: Vec<Term> = asserted_keys.clone();
        keys.extend(goal.iter().copied());
        goal.extend(bounded_array_ext_consequences(
            ctx,
            &keys,
            &canonicity_roots,
        ));
    }

    // Load THIS handle's goal into the shared engine, replacing the goal the
    // previous check (possibly another handle's) left behind.
    if let Err(e) = ctx.solver.try_reset_assertions() {
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(format!("{e}"));
        record_unknown(ctx, handle);
        return Z3_L_UNDEF;
    }
    for &term in &goal {
        if let Err(e) = ctx.solver.try_assert_term(term) {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{e}"));
            record_unknown(ctx, handle);
            return Z3_L_UNDEF;
        }
    }
    // Inject the theory-internal background axioms (special-relation orders,
    // Char range invariants) so they constrain THIS check. The quantified
    // recursive-definition axioms are omitted when the goal was fully
    // expanded AND for grind-class residuals (see `RecDefMode::Residual`).
    let include_rec_axioms = match &rec_mode {
        RecDefMode::None => true,
        RecDefMode::Expanded => false,
        RecDefMode::Residual { keep_axioms, .. } => *keep_axioms,
    };
    if let Err(e) = assert_background_axioms(ctx, include_rec_axioms) {
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(e);
        record_unknown(ctx, handle);
        return Z3_L_UNDEF;
    }
    if let Err(e) = assert_reachable_finite_set_axioms(ctx, &finite_set_roots) {
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(e);
        record_unknown(ctx, handle);
        return Z3_L_UNDEF;
    }
    // User-propagator consequence lemmas (see `propagate::user_propagator_check`):
    // each is the consumer's theory axiom `(∧ justification) ⇒ conseq`, trusted
    // exactly as Z3 trusts propagator lemmas. NOT part of the handle's
    // `assertions`, so `Z3_solver_get_assertions` / unsat-core stay faithful.
    for &lemma in &lemmas {
        if let Err(e) = ctx.solver.try_assert_term(lemma) {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{e}"));
            record_unknown(ctx, handle);
            return Z3_L_UNDEF;
        }
    }
    let verified = if effective.is_empty() {
        ctx.solver.check_sat()
    } else {
        ctx.solver.check_sat_assuming(&effective)
    };
    // Materialize the check artefacts into the handle (a later check by any
    // handle replaces the engine-side state). Each is the engine's own
    // artefact for exactly this goal — nothing is fabricated, and a
    // non-SAT/non-UNSAT check simply leaves the matching field `None`.
    handle.last_model = ctx.solver.model().map(|m| m.into_inner());
    // Raw model text captured alongside: it carries the arity > 0 function
    // tables the parsed constants-only `Model` drops, so `Z3_model` handles
    // can resolve UF applications from the snapshot.
    handle.last_model_text = ctx.solver.model_str();
    // The engine saw EXPANDED assumptions in `RecDefMode::Expanded`; translate
    // its core back to the caller's original assumption terms. When several
    // originals share one expansion, ALL of them are included (a superset of a
    // core is still a sound core); an unmapped entry passes through unchanged.
    handle.last_unsat_core = ctx.solver.unsat_assumptions().map(|core| {
        if rec_core_map.is_empty() {
            core
        } else {
            let mut originals: Vec<Term> = Vec::new();
            for entry in core {
                let mut mapped = false;
                for &(expanded, original) in &rec_core_map {
                    if expanded == entry {
                        mapped = true;
                        if !originals.contains(&original) {
                            originals.push(original);
                        }
                    }
                }
                if !mapped && !originals.contains(&entry) {
                    originals.push(entry);
                }
            }
            originals
        }
    });
    handle.last_reason_unknown = ctx.solver.reason_unknown_smtlib();
    if ctx.solver.is_producing_proofs() {
        handle.last_proof_alethe = ctx.solver.export_last_proof_alethe();
    }
    // Snapshot the executor's REAL statistics for exactly this check, so
    // `Z3_solver_get_statistics` on this handle reports this goal's counters
    // even after another handle's later check overwrites the engine state.
    handle.last_statistics = Some(ctx.solver.statistics().clone());
    let mut lbool = solve_lbool_with_acceptance(ctx, verified);
    lbool = apply_finite_set_decision_gate(ctx, lbool, &finite_set_gate, "Z3_solver_check");
    // Transitive-closure SAT gate: the background axioms for a
    // `Z3_mk_transitive_closure` predicate are only PARTIAL (a least fixed
    // point is not finitely FO-axiomatizable), so an engine SAT could rest on
    // an over-approximated TC. Release SAT only after the model's TC tables
    // are verified to BE the reflexive-transitive closures of the model's R
    // tables; otherwise report an honest unknown and revoke the rejected
    // candidate model through `SolverCheckOutcome`.
    if lbool == Z3_L_TRUE && !ctx.transitive_closure_regs.is_empty() {
        if let Err(reason) = verify_transitive_closure_model(ctx, handle) {
            handle.last_reason_unknown =
                Some(format!("transitive-closure model not verified: {reason}"));
            lbool = Z3_L_UNDEF;
        }
    }
    // Recursive-definition SAT trap: in residual mode the engine solved the
    // goal with `f` as a quantified-axiom-constrained plain UF. Its UNSAT is
    // sound (the axiom is definitional), but a SAT could rest on quantifier
    // luck over an unexpanded recursive function — fail closed to UNKNOWN
    // (never a wrong `sat`; `record_check_outcome(Unknown)` below revokes the
    // candidate model's public authority).
    if lbool == Z3_L_TRUE {
        if let RecDefMode::Residual { reason, .. } = &rec_mode {
            handle.last_reason_unknown = Some(format!(
                "recursive definition could not be fully expanded ({reason}); \
                 sat over an unexpanded recursive function is not certified"
            ));
            lbool = Z3_L_UNDEF;
        }
    }
    match lbool {
        Z3_L_TRUE => handle.record_check_outcome(SolverCheckOutcome::Sat),
        Z3_L_FALSE => handle.record_check_outcome(SolverCheckOutcome::Unsat),
        _ => record_unknown(ctx, handle),
    }
    lbool
}

/// Parse through the context solver with a fail-closed transaction boundary.
///
/// Syntax, unsupported state-control commands, and Optimize-only commands are
/// rejected before execution.
/// Once semantic execution starts, all copied handle results are retired and a
/// poison latch is installed before the first command, so a panic cannot leave
/// a partially changed engine reusable. The engine does not currently expose a
/// complete snapshot/rollback for unscoped declarations and options; therefore
/// any execution error permanently poisons the context rather than allowing a
/// later check over ambiguous state.
pub(crate) fn parse_solver_transaction(
    ctx: &mut Z3Context,
    input: &str,
    operation: &str,
) -> Option<Vec<Term>> {
    if !ctx.decision_engine_is_usable(operation) {
        return None;
    }

    // Fail-close reserved `map[...]` symbol capture: this text is handed to
    // the core parser/elaborator, where a quoted symbol `|map[f]|` declares a
    // function whose applications the array theory rewrites as the internal
    // array-map operator (measured wrong verdict). See
    // `smtlib2_reserved_error` in `mod.rs`.
    if let Some(msg) = super::smtlib2_reserved_error(input) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!("{operation}: {msg}"));
        return None;
    }

    let commands = match ay_frontend::parse(input) {
        Ok(commands) => commands,
        Err(e) => {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{operation}: {e}"));
            return None;
        }
    };
    if commands.iter().any(|command| {
        matches!(
            command,
            Command::Push(_) | Command::Pop(_) | Command::Reset | Command::ResetAssertions
        )
    }) {
        ctx.last_error = Z3_INVALID_USAGE;
        ctx.error_msg = Some(format!(
            "{operation}: push/pop/reset commands are not supported by the assertion-returning parse bridge"
        ));
        return None;
    }
    if commands.iter().any(|command| {
        matches!(
            command,
            Command::AssertSoft { .. } | Command::Maximize(_) | Command::Minimize(_)
        )
    }) {
        ctx.last_error = Z3_INVALID_USAGE;
        ctx.error_msg = Some(format!(
            "{operation}: assert-soft/maximize/minimize commands are not supported by the Solver-family assertion-returning parse bridge; use Z3_optimize_from_string"
        ));
        return None;
    }
    // Claim only after non-mutating preflight succeeds. A malformed or
    // unsupported script must not reserve this otherwise-pristine context for
    // the Solver family and thereby prevent a later Optimize constructor.
    if !ctx.claim_decision_owner(DecisionOwnerFamily::Solver, operation) {
        return None;
    }

    ctx.clear_decision_check_artifacts();
    ctx.decision_engine_poisoned = Some(format!(
        "{operation}: parse transaction was interrupted before completion"
    ));
    match ctx.solver.parse_smtlib2_z3_5(input) {
        Ok(batch) => match super::retain_parsed_finite_set_batch(ctx, batch) {
            Ok(retained) => {
                ctx.decision_engine_poisoned = None;
                ctx.last_error = Z3_OK;
                ctx.error_msg = None;
                Some(retained.assertions)
            }
            Err(error) => {
                ctx.poison_decision_engine(format!(
                    "{operation}: parsed public FiniteSet metadata could not be retained: {error}"
                ));
                None
            }
        },
        Err(e) => {
            ctx.poison_decision_engine(format!(
                "{operation}: parse execution failed after semantic mutation may have begun: {e}"
            ));
            None
        }
    }
}

/// Verify, from the materialized model snapshot, that EVERY transitive-closure
/// predicate registered on this context is interpreted as exactly the
/// reflexive-transitive closure of its underlying relation's interpretation.
///
/// Procedure (all fail-closed — any unreadable piece returns `Err`, which the
/// caller converts to an honest `unknown`, never a wrong verdict):
///   1. the domain sort must be an uninterpreted sort (the only kind whose
///      model universe AY can enumerate soundly);
///   2. the enumerable universe `U` = the model's named-constant elements of
///      that sort (`model_sort_universes`) ∪ every element of that sort
///      appearing in ANY parsed function table (argument, row value, or else
///      value) — i.e. every element the model can denote. A parsed-table
///      count mismatch (a table `parse_func_interps` skipped) aborts, so no
///      denotable element can hide in an unparsed table;
///   3. compute `RTC(R)` over `U` by Warshall (reflexive + transitive), with
///      `R` read from its table under first-matching-row-else semantics;
///   4. require `TC(u, v) == RTC(R)(u, v)` for every `(u, v) ∈ U × U`.
///
/// SOUNDNESS of an `Ok`: the engine's validated model already satisfies the
/// background axioms, so `RTC(R_model) ⊆ TC_model` holds semantically. An
/// absent/under-read `R` table only SHRINKS the computed closure `W`, and
/// `W ⊆ RTC(R_model) ⊆ TC_model`; blessing requires `TC_model == W` on
/// `U × U`, which then forces the whole chain equal — so even with an absent
/// `R` table an `Ok` is only reachable when `TC_model` genuinely IS the
/// closure. Errors only ever refuse a SAT (incompleteness, never unsoundness).
fn verify_transitive_closure_model(
    ctx: &mut Z3Context,
    handle: &Z3SolverHandle,
) -> Result<(), String> {
    /// Enumerable-universe cap: Warshall is cubic, so refuse (→ unknown)
    /// beyond this rather than stall the check.
    const MAX_UNIVERSE: usize = 512;

    let Some(model_text) = handle.last_model_text.clone() else {
        return Err("no model text was materialized for this check".to_string());
    };
    let Some(model) = handle.last_model.as_ref() else {
        return Err("no model was materialized for this check".to_string());
    };
    let interps = super::model_params::parse_func_interps(&model_text);
    match super::model_params::count_nonconst_define_funs(&model_text) {
        Some(n) if n == interps.len() => {}
        _ => {
            return Err(
                "a function table in the model is outside the parseable fragment".to_string(),
            );
        }
    }
    let universes = super::model_params::model_sort_universes(&ctx.solver, model);
    let regs: Vec<(String, String, Sort)> = ctx
        .transitive_closure_regs
        .iter()
        .map(|r| (r.tc_name.clone(), r.rel_name.clone(), r.domain.clone()))
        .collect();

    /// Push an element token if unseen (token identity = element identity).
    fn add_element(universe: &mut Vec<String>, e: &str) {
        if !universe.iter().any(|x| x == e) {
            universe.push(e.to_string());
        }
    }
    /// Read a table at `(a, b)` under first-matching-row-else semantics.
    /// An ABSENT table reads all-false (sound: it can only shrink the
    /// computed closure / fail the comparison — see the soundness note).
    fn table_lookup(
        fi: Option<&super::model_params::FuncInterp>,
        a: &str,
        b: &str,
    ) -> Result<bool, String> {
        let Some(fi) = fi else { return Ok(false) };
        for (args, value) in &fi.rows {
            let [arg_a, arg_b] = args.as_slice() else {
                return Err(format!("table {} has a non-binary row", fi.name));
            };
            let (ModelValue::Uninterpreted(ea), ModelValue::Uninterpreted(eb)) = (arg_a, arg_b)
            else {
                return Err(format!("table {} has a non-element argument", fi.name));
            };
            if ea == a && eb == b {
                return value
                    .as_bool()
                    .ok_or_else(|| format!("table {} has a non-Bool row value", fi.name));
            }
        }
        fi.else_value
            .as_bool()
            .ok_or_else(|| format!("table {} has a non-Bool else value", fi.name))
    }

    for (tc_name, rel_name, domain) in regs {
        if !matches!(domain, Sort::Uninterpreted(_)) {
            return Err(format!(
                "the transitive-closure domain sort is not an enumerable uninterpreted \
                 sort (got {domain:?})"
            ));
        }
        // Universe: named-constant elements ∪ every element of this sort in
        // any table (arguments, row values, else values).
        let mut universe: Vec<String> = universes
            .iter()
            .find(|(s, _)| *s == domain)
            .map(|(_, u)| u.clone())
            .unwrap_or_default();
        for fi in &interps {
            for (args, value) in &fi.rows {
                for (i, arg) in args.iter().enumerate() {
                    if fi.param_sorts.get(i) == Some(&domain) {
                        match arg {
                            ModelValue::Uninterpreted(e) => add_element(&mut universe, e),
                            other => {
                                return Err(format!(
                                    "table {} has a non-element value ({}) at a {domain:?} \
                                     argument position",
                                    fi.name,
                                    other.variant_name()
                                ));
                            }
                        }
                    }
                }
                if fi.result_sort == domain {
                    match value {
                        ModelValue::Uninterpreted(e) => add_element(&mut universe, e),
                        other => {
                            return Err(format!(
                                "table {} has a non-element row value ({}) at result sort \
                                 {domain:?}",
                                fi.name,
                                other.variant_name()
                            ));
                        }
                    }
                }
            }
            if fi.result_sort == domain {
                match &fi.else_value {
                    ModelValue::Uninterpreted(e) => add_element(&mut universe, e),
                    other => {
                        return Err(format!(
                            "table {} has a non-element else value ({}) at result sort {domain:?}",
                            fi.name,
                            other.variant_name()
                        ));
                    }
                }
            }
        }
        let n = universe.len();
        if n > MAX_UNIVERSE {
            return Err(format!(
                "the model universe has {n} elements (verification cap {MAX_UNIVERSE})"
            ));
        }
        let r_interp = interps
            .iter()
            .find(|fi| fi.name == rel_name && fi.param_sorts.len() == 2);
        let tc_interp = interps
            .iter()
            .find(|fi| fi.name == tc_name && fi.param_sorts.len() == 2);
        // RTC(R) over U by Warshall: reflexive base + R edges, then closure.
        let mut rtc = vec![vec![false; n]; n];
        for (i, u) in universe.iter().enumerate() {
            for (j, v) in universe.iter().enumerate() {
                rtc[i][j] = i == j || table_lookup(r_interp, u, v)?;
            }
        }
        for k in 0..n {
            for i in 0..n {
                if rtc[i][k] {
                    for j in 0..n {
                        rtc[i][j] = rtc[i][j] || rtc[k][j];
                    }
                }
            }
        }
        // The model's TC must agree with the computed closure EVERYWHERE.
        for (i, u) in universe.iter().enumerate() {
            for (j, v) in universe.iter().enumerate() {
                let modeled = table_lookup(tc_interp, u, v)?;
                if modeled != rtc[i][j] {
                    return Err(format!(
                        "the model interprets {tc_name}({u}, {v}) as {modeled}, but the \
                         reflexive-transitive closure of {rel_name} makes it {}",
                        rtc[i][j]
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Check satisfiability of THIS solver handle's assertions.
///
/// If this solver was produced by `Z3_mk_solver_from_tactic`, its tactic is
/// applied to the goal first (equivalence-preserving, so the verdict and model
/// are identical to solving the untransformed goal).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_check(c: Z3_context, s: Z3_solver) -> c_int {
    // A handle with a registered user propagator runs the SOUND FINAL-CHECK
    // LOOP instead (SAT only after the user's final check raises no objection).
    // SAFETY: `s` is null-checked by `as_ref`; read-only scoped peek.
    if unsafe { s.as_ref() }.is_some_and(|h| h.propagator.is_some()) {
        // SAFETY: `c` valid-or-null per this function's contract; no context
        // borrow is outstanding (the loop takes its own scoped borrows).
        return unsafe { super::propagate::user_propagator_check(c, s, None) };
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is forwarded to `check_solver_handle`, which
    // null-checks it.
    unsafe { ffi_guard_int(c, Z3_L_UNDEF, |ctx| check_solver_handle(ctx, s, None, &[])) }
}

/// Check satisfiability of THIS solver handle's assertions under assumptions.
///
/// # Safety
/// All pointers must be valid. `assumptions` must point to `num_assumptions` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_check_assumptions(
    c: Z3_context,
    s: Z3_solver,
    num_assumptions: c_uint,
    assumptions: *const Z3_ast,
) -> c_int {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_solver_check_assumptions", num_assumptions) } {
        return Z3_L_UNDEF;
    }
    // A non-empty raw array may never be represented by a null pointer.  In
    // addition to rejecting the malformed call, retire the preceding decision
    // artifacts so they cannot be mistaken for this query's result.
    if num_assumptions > 0 && assumptions.is_null() {
        // SAFETY: `ffi_guard_int` validates/guards `c`; `s` is null-checked.
        return unsafe {
            ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
                let Some(handle) = s.as_mut() else {
                    note_null_solver_handle(ctx, "Z3_solver_check_assumptions");
                    return Z3_L_UNDEF;
                };
                let reason =
                    "Z3_solver_check_assumptions: null assumptions array for non-zero count"
                        .to_string();
                handle.clear_check_artifacts();
                handle.last_reason_unknown = Some(reason.clone());
                handle.record_check_outcome(SolverCheckOutcome::Unknown);
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(reason);
                Z3_L_UNDEF
            })
        };
    }

    // Pre-extract raw handles before entering the guard, since raw pointer
    // dereferences need to happen in the unsafe extern "C" context. Decode
    // only while holding the owning context so the salt and arena membership
    // are authenticated before either solver path can consume an assumption.
    let assumption_asts: Vec<_> = if num_assumptions == 0 {
        Vec::new()
    } else {
        (0..num_assumptions as usize)
            // SAFETY: The caller's `# Safety` contract guarantees `assumptions` points to at
            // least the declared number of elements. The count was range-checked above, and
            // null-checked before entering this block, so `assumptions.add(i)` stays within
            // the caller's allocation.
            .map(|i| unsafe { *assumptions.add(i) })
            .collect()
    };
    let has_assumptions = num_assumptions > 0;
    let mut terms = None;
    // SAFETY: `c` is valid-or-null by contract. The guard releases its borrow
    // before the user-propagator path below is allowed to re-enter the API.
    let decoded = unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some(decoded) =
                require_term_asts(ctx, &assumption_asts, "Z3_solver_check_assumptions")
            else {
                if let Some(handle) = s.as_mut() {
                    let reason = ctx.error_msg.clone().unwrap_or_else(|| {
                        "Z3_solver_check_assumptions: invalid assumption AST".to_string()
                    });
                    handle.clear_check_artifacts();
                    handle.last_reason_unknown = Some(reason);
                    handle.record_check_outcome(SolverCheckOutcome::Unknown);
                }
                return 0;
            };
            terms = Some(decoded);
            1
        })
    };
    if decoded == 0 {
        return Z3_L_UNDEF;
    }
    let terms = terms.unwrap_or_default();

    // A handle with a registered user propagator runs the SOUND FINAL-CHECK
    // LOOP instead (SAT only after the user's final check raises no objection).
    // SAFETY: `s` is null-checked by `as_ref`; read-only scoped peek.
    if unsafe { s.as_ref() }.is_some_and(|h| h.propagator.is_some()) {
        let assumptions = has_assumptions.then_some(terms.as_slice());
        // SAFETY: `c` valid-or-null per this function's contract; no context
        // borrow is outstanding (the loop takes its own scoped borrows).
        return unsafe { super::propagate::user_propagator_check(c, s, assumptions) };
    }

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is forwarded to `check_solver_handle`, which
    // null-checks it.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            let assumptions = has_assumptions.then_some(terms.as_slice());
            check_solver_handle(ctx, s, assumptions, &[])
        })
    }
}

/// Get the model from THIS solver handle's last SAT check.
///
/// The model was materialized into the handle at check time, so it reflects
/// exactly this handle's assertions — never another solver's.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_model(c: Z3_context, s: Z3_solver) -> Z3_model {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(solver_handle) = s.as_ref() else {
                note_null_solver_handle(ctx, "Z3_solver_get_model");
                return ptr::null_mut();
            };
            if solver_handle.last_check_outcome != Some(SolverCheckOutcome::Sat) {
                return ptr::null_mut();
            }
            match solver_handle.last_model.clone() {
                Some(model) => {
                    // Function interpretations are part of the snapshot: parse
                    // them out of the raw model text captured at check time.
                    let func_interps = solver_handle
                        .last_model_text
                        .as_deref()
                        .map(super::model_params::parse_func_interps)
                        .unwrap_or_default();
                    let handle = Box::into_raw(Box::new(ModelHandle {
                        model,
                        func_interps,
                        user_const_interps: Vec::new(),
                        user_func_interps: Vec::new(),
                        rec_def_count: ctx.rec_fun_defs.len(),
                        _ctx: c,
                    }));
                    ctx.model_cache.push(handle);
                    handle
                }
                None => ptr::null_mut(),
            }
        })
    }
}

/// Convert solver state to a string.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_to_string(c: Z3_context, s: Z3_solver) -> *const c_char {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary. `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            // Dump THIS handle's real assertions in z3's `Z3_solver_to_string`
            // shape (`(declare-fun ...)` + `(assert ...)`), never a placeholder.
            // The live assertions live on the solver handle, not the executor's
            // internal stack (which is only populated transiently at check time).
            let sexpr = match s.as_ref() {
                Some(handle) => ctx.solver.assertions_sexpr(&handle.assertions),
                None => ctx.solver.assertions_sexpr(&[]),
            };
            let sexpr = super::ffi_surface_text(ctx, &sexpr);
            cache_string(ctx, sexpr)
        })
    }
}

/// Get the reason for THIS solver handle's last Unknown result.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_reason_unknown(
    c: Z3_context,
    s: Z3_solver,
) -> *const c_char {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary. `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_solver_handle(ctx, "Z3_solver_get_reason_unknown");
                return ptr::null();
            };
            let reason = if handle.last_check_outcome == Some(SolverCheckOutcome::Unknown) {
                handle.last_reason_unknown.clone().unwrap_or_default()
            } else {
                String::new()
            };
            cache_string(ctx, reason)
        })
    }
}

/// Get the number of scopes pushed on THIS solver handle.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_num_scopes(c: Z3_context, s: Z3_solver) -> c_uint {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_solver_handle(ctx, "Z3_solver_get_num_scopes");
                return 0;
            };
            handle.scope_markers.len() as c_uint
        })
    }
}

/// Interrupt the solver from another thread.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_interrupt(c: Z3_context, _s: Z3_solver) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(c, |ctx| {
            ctx.solver.interrupt();
        });
    }
}

/// Get the assertions currently on THIS solver handle as an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_assertions(c: Z3_context, s: Z3_solver) -> Z3_ast_vector {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_solver_handle(ctx, "Z3_solver_get_assertions");
                return ptr::null_mut();
            };
            let asts = handle
                .assertions
                .iter()
                .copied()
                .map(|term| term_to_ast(ctx, term))
                .collect();
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Get the unsat core from THIS solver handle's last UNSAT check-sat-assuming
/// result.
///
/// Returns an AST vector containing the subset of assumptions that
/// contributed to unsatisfiability. Returns an empty vector if the last
/// result was not UNSAT or was not produced by check-sat-assuming.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_unsat_core(c: Z3_context, s: Z3_solver) -> Z3_ast_vector {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_solver_handle(ctx, "Z3_solver_get_unsat_core");
                return ptr::null_mut();
            };
            let asts = match (handle.last_check_outcome, &handle.last_unsat_core) {
                (Some(SolverCheckOutcome::Unsat), Some(terms)) => terms
                    .iter()
                    .copied()
                    .map(|term| term_to_ast(ctx, term))
                    .collect(),
                _ => Vec::new(),
            };
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Parse an SMT-LIB2 string and return assertions as an AST vector.
///
/// Parses declarations and assertions from the input string.
/// Query commands (check-sat, get-model, etc.) are ignored.
/// The `sort_names`/`sorts` and `decl_names`/`decls` parameters allow
/// pre-declaring sorts and functions (currently ignored — all declarations
/// must be in the string itself).
///
/// # Safety
/// All pointers must be valid. `str` must be a null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_parse_smtlib2_string(
    c: Z3_context,
    str: *const c_char,
    _num_sorts: c_uint,
    _sort_names: *const Z3_symbol,
    _sorts: *const Z3_sort,
    _num_decls: c_uint,
    _decl_names: *const Z3_symbol,
    _decls: *const Z3_func_decl,
) -> Z3_ast_vector {
    // Pre-validate and extract the input string outside the guard,
    // since raw pointer dereferences happen in the unsafe extern "C" context.
    let input_string = if str.is_null() {
        None
    } else {
        // SAFETY: `str` is non-null and a valid NUL-terminated string per the
        // caller contract; the helper bounds the scan and clone.
        match unsafe { ffi_read_bounded_parser_text(str) } {
            Ok(s) => Some(s),
            Err(error) => {
                // SAFETY: `c` was validated non-null by the outer FFI
                // contract. This borrow is scoped to this block and does
                // not overlap with any other &mut Z3Context. Using
                // `c.as_mut()` directly instead of the removed `ctx_ref`
                // (see #8568) so the compiler constrains the lifetime.
                // SAFETY: `c` is the Z3_context pointer validated by the enclosing extern "C"
                // function's `# Safety` contract. `as_mut()` returns `None` when `c` is null,
                // so dereferencing the resulting reference is sound. The borrow is scoped to
                // this block and does not alias any other reference into `Z3Context`.
                if let Some(ctx) = unsafe { c.as_mut() } {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_parse_smtlib2_string: {error}"));
                    return cache_ast_vector(ctx, Vec::new());
                }
                return ptr::null_mut();
            }
        }
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(ref input) = input_string else {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some("null input string".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            let terms =
                parse_solver_transaction(ctx, input, "Z3_parse_smtlib2_string").unwrap_or_default();
            let asts = terms
                .into_iter()
                .map(|term| term_to_ast(ctx, term))
                .collect();
            cache_ast_vector(ctx, asts)
        })
    }
}

// ============================================================================
// Wave 2: assert-and-track cores, consequences, from-string/file, translate,
// trail/units, help, congruence, DIMACS.
// ============================================================================

/// Assert `a` on THIS solver handle, tracked for unsat-core extraction by the
/// Boolean literal `p` (Z3's `Z3_solver_assert_and_track`).
///
/// Mechanism (exactly Z3's): the IMPLICATION `(=> p a)` is asserted on the
/// handle, and `p` is recorded as a tracking literal. At the next
/// `Z3_solver_check`/`Z3_solver_check_assumptions`, every tracking literal is
/// passed as an assumption, so `Z3_solver_get_unsat_core` returns the subset of
/// tracking literals (combined with any explicit check-assumptions) that
/// contributed to UNSAT. Both `a` and `p` must be Boolean (Z3 additionally
/// requires `p` to be an atomic Boolean constant; AY accepts any Boolean `p`,
/// documented in `ay_z3_compat.h` — the `(=> p a)` encoding is sound for any
/// Boolean `p`).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_assert_and_track(
    c: Z3_context,
    s: Z3_solver,
    a: Z3_ast,
    p: Z3_ast,
) {
    // SAFETY: `c` is validated/guarded by `ffi_guard_void`; `s` is null-checked
    // via `as_mut`. The handle lives in the context arena (separate allocation
    // from `*ctx`), so the two mutable borrows do not alias.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if s.is_null() {
                note_null_solver_handle(ctx, "Z3_solver_assert_and_track");
                return;
            }
            if !ctx.decision_engine_is_usable("Z3_solver_assert_and_track") {
                return;
            }
            // SAFETY: null-checked above; arena-owned and single-threaded.
            let handle = &mut *s;
            let Some(a_term) = require_term_ast(ctx, a, "Z3_solver_assert_and_track", "formula")
            else {
                return;
            };
            let Some(p_term) =
                require_term_ast(ctx, p, "Z3_solver_assert_and_track", "tracking literal")
            else {
                return;
            };
            // Precondition: `a` must be Boolean (same error text as assert).
            let a_sort = ctx.solver.term_sort(a_term);
            if a_sort != Sort::Bool {
                let e = SolverError::SortMismatch {
                    operation: "assert_and_track",
                    expected: "Bool",
                    got: vec![a_sort],
                };
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            // Precondition: `p` must be Boolean (the tracking literal).
            let p_sort = ctx.solver.term_sort(p_term);
            if p_sort != Sort::Bool {
                let e = SolverError::SortMismatch {
                    operation: "assert_and_track (tracking literal)",
                    expected: "Bool",
                    got: vec![p_sort],
                };
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            // The assertion actually added is `(=> p a)`; `p` is the tracker.
            let implication = ctx.solver.implies(p_term, a_term);
            handle.assertions.push(implication);
            handle.tracked.push((p_term, a_term));
            handle.clear_check_artifacts();
        });
    }
}

/// Load SMT-LIB2 assertions from a string into THIS solver handle (Z3's
/// `Z3_solver_from_string`).
///
/// The declarations and assertions in `str` are parsed through AY's real
/// SMT-LIB2 front-end and APPENDED to the handle's assertion stack (query
/// commands such as `check-sat`/`get-model` are ignored). A subsequent
/// `Z3_solver_check` therefore solves the parsed formulas.
///
/// `push`/`pop`/`reset` controls are rejected before execution. After semantic
/// execution starts, any error permanently poisons the context because unscoped
/// declarations/options cannot be completely rolled back; copied check artifacts
/// are retired and existing decision entrypoints fail closed.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver
/// handle; `str`, when non-null, a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_from_string(c: Z3_context, s: Z3_solver, str: Z3_string) {
    // Extract the input string outside the guard (raw-pointer deref).
    let input = if str.is_null() {
        None
    } else {
        // SAFETY: caller contract: `str` is a valid NUL-terminated C string;
        // the helper bounds the scan and clone.
        Some(unsafe { ffi_read_bounded_parser_text(str) })
    };
    // SAFETY: `ffi_guard_void` validates/guards `c`; `s` is null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if s.is_null() {
                note_null_solver_handle(ctx, "Z3_solver_from_string");
                return;
            }
            let text = match input.as_ref() {
                None => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some("Z3_solver_from_string: null input string".to_string());
                    return;
                }
                Some(Ok(text)) => text,
                Some(Err(error)) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_solver_from_string: {error}"));
                    return;
                }
            };
            if let Some(terms) = parse_solver_transaction(ctx, text, "Z3_solver_from_string") {
                // SAFETY: null-checked before the transaction; the handle is
                // arena-owned and no reference to it was held while all handle
                // artifacts were retired.
                (&mut *s).assertions.extend(terms);
            }
        });
    }
}

/// Load SMT-LIB2 assertions from a file into THIS solver handle (Z3's
/// `Z3_solver_from_file`). Reads the file and routes it through
/// `Z3_solver_from_string`'s parsing path.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver
/// handle; `file_name`, when non-null, a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_from_file(c: Z3_context, s: Z3_solver, file_name: Z3_string) {
    // Extract path + read file outside the guard.
    let path: Option<String> = if file_name.is_null() {
        None
    } else {
        // SAFETY: caller contract: `file_name` is a valid NUL-terminated C
        // string; the helper bounds the scan and clone.
        unsafe { ffi_read_bounded_text(file_name) }.ok()
    };
    let contents: Option<Result<String, String>> =
        path.as_deref().map(ffi_read_bounded_parser_file);
    // SAFETY: `ffi_guard_void` validates/guards `c`; `s` is null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if s.is_null() {
                note_null_solver_handle(ctx, "Z3_solver_from_file");
                return;
            }
            let text = match contents {
                Some(Ok(t)) => t,
                Some(Err(e)) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_solver_from_file: {e}"));
                    return;
                }
                None => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some("Z3_solver_from_file: null file name".to_string());
                    return;
                }
            };
            if let Some(terms) = parse_solver_transaction(ctx, &text, "Z3_solver_from_file") {
                // SAFETY: see the string variant above.
                (&mut *s).assertions.extend(terms);
            }
        });
    }
}

/// Copy solver `s` from context `source` into context `target` (Z3's
/// `Z3_solver_translate`).
///
/// Returns a NEW solver handle on `target` carrying a faithful copy of `s`'s
/// assertion stack (including its push/pop scope markers, its
/// assert-and-track pairs, and its tactic, when any). When the contexts
/// differ, the whole assertion/tracking term DAG is re-interned into
/// `target`'s term store via the engine's `translate_terms_from` graft — never
/// a fabricated goal. Cross-context translation is refused when source
/// context-resident semantic metadata cannot be carried by that DAG graft.
/// The source solver is left untouched.
///
/// # Safety
/// `source`/`target` must be valid context pointers; `s`, when non-null, a valid
/// solver handle owned by `source`.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_translate(
    source: Z3_context,
    s: Z3_solver,
    target: Z3_context,
) -> Z3_solver {
    // Pre-extract the source handle's state (raw deref; it lives in `source`).
    // SAFETY: `s`, when non-null, is a live `Z3SolverHandle`.
    let handle_data = unsafe { s.as_ref() }.map(|h| {
        (
            h.assertions.clone(),
            h.scope_markers.clone(),
            h.tracked.clone(),
            h.tracked_scope_markers.clone(),
            h.tactic.clone(),
        )
    });
    // SAFETY: `ffi_guard_ptr` validates/guards `target`.
    unsafe {
        ffi_guard_ptr(target, |tgt| {
            let Some((assertions, scope_markers, tracked, tracked_scope_markers, tactic)) =
                handle_data
            else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_solver_translate: null solver handle".to_string());
                return ptr::null_mut();
            };
            // Validate source semantic portability before claiming or mutating
            // the target. A rejected translation leaves a fresh target usable
            // by either decision family.
            if source != target {
                let Some(src) = source.as_ref() else {
                    tgt.last_error = Z3_INVALID_ARG;
                    tgt.error_msg = Some("Z3_solver_translate: null source context".to_string());
                    return ptr::null_mut();
                };
                if !ensure_cross_context_translation_semantics(src, tgt, "Z3_solver_translate") {
                    return ptr::null_mut();
                }
            }
            let previous_owner = tgt.decision_owner;
            if !tgt.claim_decision_owner(DecisionOwnerFamily::Solver, "Z3_solver_translate") {
                return ptr::null_mut();
            }
            let (new_assertions, new_tracked) = if source == target {
                // Same context: the handles are already valid here.
                (assertions, tracked)
            } else {
                // Cross-context: re-intern into `target`'s term store.
                // SAFETY: `source != target`, so this shared borrow does not
                // alias `tgt`.
                let Some(src) = source.as_ref() else {
                    tgt.last_error = Z3_INVALID_ARG;
                    tgt.error_msg = Some("Z3_solver_translate: null source context".to_string());
                    return ptr::null_mut();
                };
                let new_a = tgt.solver.translate_terms_from(&src.solver, &assertions);
                // Flatten tracked (p, a) pairs, graft, and re-pair.
                let mut flat: Vec<Term> = Vec::with_capacity(tracked.len() * 2);
                for (p, a) in &tracked {
                    flat.push(*p);
                    flat.push(*a);
                }
                let new_flat = tgt.solver.translate_terms_from(&src.solver, &flat);
                let mut source_roots = assertions.clone();
                source_roots.extend(flat.iter().copied());
                let mut target_roots = new_a.clone();
                target_roots.extend(new_flat.iter().copied());
                if !transfer_cross_context_ffi_metadata(
                    src,
                    tgt,
                    &source_roots,
                    &target_roots,
                    "Z3_solver_translate",
                ) {
                    tgt.decision_owner = previous_owner;
                    return ptr::null_mut();
                }
                let new_t: Vec<(Term, Term)> = new_flat
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|c| (c[0], c[1]))
                    .collect();
                (new_a, new_t)
            };
            let mut new_handle = Z3SolverHandle::new(tactic);
            new_handle.assertions = new_assertions;
            new_handle.scope_markers = scope_markers;
            new_handle.tracked = new_tracked;
            new_handle.tracked_scope_markers = tracked_scope_markers;
            let handle = Box::into_raw(Box::new(new_handle));
            tgt.solver_handle_cache.push(handle);
            tgt.last_error = Z3_OK;
            handle
        })
    }
}

/// Build the consequence implication `(=> (and assumptions) lit)` used by
/// `Z3_solver_get_consequences`. An empty assumption set yields `true` as the
/// antecedent (AY then simplifies `(=> true lit)` to `lit`).
fn build_consequence(ctx: &mut Z3Context, base: &[Term], lit: Term) -> Term {
    let antecedent = if base.is_empty() {
        ctx.solver.bool_const(true)
    } else {
        ctx.solver.and_many(base)
    };
    ctx.solver.implies(antecedent, lit)
}

/// Compute the consequences (forced Boolean-variable values) of THIS solver's
/// assertions under `assumptions` (Z3's `Z3_solver_get_consequences`).
///
/// For each variable `v` in `variables`, the routine checks whether the
/// assertions + assumptions FORCE `v` true (i.e. `assumptions ∧ ¬v` is UNSAT)
/// or false (`assumptions ∧ v` is UNSAT). Every forced literal is appended to
/// the `consequences` vector as the implication `(=> (and assumptions) lit)`.
/// This is a SOUND derivation: a consequence is emitted only when the probe is
/// definitively UNSAT (never on an unknown/sat probe), so only truly-implied
/// values are reported. It may be incomplete under `unknown` (honest partial).
///
/// Returns `Z3_L_FALSE` when the assertions are UNSAT under the assumptions,
/// `Z3_L_UNDEF` when the baseline is not publicly accepted, else `Z3_L_TRUE`.
/// Because this auxiliary query has no user-propagator final-check loop or
/// transitive-closure model verifier, either active feature conservatively
/// yields `Z3_L_UNDEF` before any output is appended.
///
/// # Safety
/// All pointers must be valid; `assumptions`/`variables`/`consequences` are
/// valid `Z3_ast_vector` handles (`consequences` is filled in place).
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_consequences(
    c: Z3_context,
    s: Z3_solver,
    assumptions: Z3_ast_vector,
    variables: Z3_ast_vector,
    consequences: Z3_ast_vector,
) -> c_int {
    // Pre-extract the input vectors (raw derefs) outside the guard.
    // SAFETY: caller contract: these are valid `Z3_ast_vector` handles (or null).
    let (assumption_asts, variable_asts): (Vec<Z3_ast>, Vec<Z3_ast>) = unsafe {
        (
            assumptions
                .as_ref()
                .map(|v| v.asts.clone())
                .unwrap_or_default(),
            variables
                .as_ref()
                .map(|v| v.asts.clone())
                .unwrap_or_default(),
        )
    };
    // SAFETY: `ffi_guard_int` validates/guards `c`; `s`/`consequences` are
    // null-checked before use.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_solver_get_consequences") {
                return Z3_L_UNDEF;
            }
            // Snapshot the handle's goal + tracking literals, then drop the borrow.
            let (goal, tracked, has_user_propagator): (Vec<Term>, Vec<Term>, bool) =
                match s.as_ref() {
                    Some(h) => (
                        h.assertions.clone(),
                        h.tracked.iter().map(|(p, _)| *p).collect(),
                        h.propagator.is_some(),
                    ),
                    None => {
                        note_null_solver_handle(ctx, "Z3_solver_get_consequences");
                        return Z3_L_UNDEF;
                    }
                };
            if !auxiliary_query_acceptance_is_supported(
                ctx,
                has_user_propagator,
                "Z3_solver_get_consequences",
            ) {
                return Z3_L_UNDEF;
            }
            // Base assumption set = explicit assumptions ++ tracking literals.
            // `base_original`/`vars_original` are what consequences are BUILT
            // from (faithful output terms); the `*_probe` twins are what the
            // engine actually solves (rec-def-expanded when definitions exist).
            let Some(mut base_original) = require_term_asts(
                ctx,
                &assumption_asts,
                "Z3_solver_get_consequences assumptions",
            ) else {
                return Z3_L_UNDEF;
            };
            base_original.extend(tracked.iter().copied());
            let Some(vars_original) =
                require_term_asts(ctx, &variable_asts, "Z3_solver_get_consequences variables")
            else {
                return Z3_L_UNDEF;
            };
            let mut finite_set_roots = goal.clone();
            finite_set_roots.extend(base_original.iter().copied());
            finite_set_roots.extend(vars_original.iter().copied());
            let finite_set_gate = finite_set_decision_gate(ctx, &finite_set_roots);
            let mut goal = goal;
            let mut base = base_original.clone();
            let mut vars_probe = vars_original.clone();
            let mut rec_expanded = false;
            if !ctx.rec_fun_defs.is_empty() {
                let mut batch: Vec<Term> =
                    Vec::with_capacity(goal.len() + base.len() + vars_probe.len());
                batch.extend_from_slice(&goal);
                batch.extend_from_slice(&base);
                batch.extend_from_slice(&vars_probe);
                // Finding-2 gate: never probe through a defined body whose
                // unfolding surfaces an UNDEFINED rec declaration (see
                // `rec_defs_tainted_by_undefined`) — strictly fail-closed.
                let tainted = rec_defs_tainted_by_undefined(ctx);
                if !tainted.is_empty() && ctx.solver.terms_mention_names(&batch, &tainted) {
                    ctx.last_error = Z3_INVALID_USAGE;
                    ctx.error_msg = Some(
                        "Z3_solver_get_consequences: a used definition depends on a \
                         recursive declaration with no definition; returning unknown \
                         fail-closed"
                            .to_string(),
                    );
                    return Z3_L_UNDEF;
                }
                match ctx.solver.try_expand_rec_defs(
                    &batch,
                    &ctx.rec_fun_defs,
                    REC_DEF_MAX_ROUNDS,
                    REC_DEF_WORK_BUDGET,
                    Some(rec_def_expansion_deadline(ctx)),
                ) {
                    Ok(expanded) => {
                        let (new_goal, rest) = expanded.split_at(goal.len());
                        let (new_base, new_vars) = rest.split_at(base.len());
                        goal = new_goal.to_vec();
                        base = new_base.to_vec();
                        vars_probe = new_vars.to_vec();
                        rec_expanded = true;
                    }
                    // STRICTLY fail-closed: this auxiliary query has no
                    // residual-mode SAT demotion path, so no verdict-bearing
                    // probe may run over an unexpanded recursive function.
                    Err(e) => {
                        ctx.last_error = Z3_INVALID_USAGE;
                        ctx.error_msg = Some(format!(
                            "Z3_solver_get_consequences: recursive definition could not \
                             be fully expanded ({e}); returning unknown fail-closed"
                        ));
                        return Z3_L_UNDEF;
                    }
                }
            }
            // Load the goal into the shared engine.
            if let Err(e) = ctx.solver.try_reset_assertions() {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return Z3_L_UNDEF;
            }
            for &t in &goal {
                if let Err(e) = ctx.solver.try_assert_term(t) {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    return Z3_L_UNDEF;
                }
            }
            // Theory-internal background axioms (orders / Char bounds) too;
            // the rec-def axioms are omitted for a fully-expanded goal.
            if let Err(e) = assert_background_axioms(ctx, !rec_expanded) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(e);
                return Z3_L_UNDEF;
            }
            if let Err(e) = assert_reachable_finite_set_axioms(ctx, &finite_set_roots) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(e);
                return Z3_L_UNDEF;
            }
            // Baseline satisfiability under the assumptions.
            let baseline = if base.is_empty() {
                ctx.solver.check_sat()
            } else {
                ctx.solver.check_sat_assuming(&base)
            };
            let baseline = solve_lbool_with_acceptance(ctx, baseline);
            let baseline = apply_finite_set_decision_gate(
                ctx,
                baseline,
                &finite_set_gate,
                "Z3_solver_get_consequences",
            );
            match baseline {
                Z3_L_FALSE => {
                    ctx.last_error = Z3_OK;
                    return Z3_L_FALSE;
                }
                Z3_L_TRUE => {}
                // Unknown or consumer-rejected baseline: no consequences may
                // be claimed from a baseline the public surface did not admit.
                _ => return Z3_L_UNDEF,
            }
            // Probe each variable's forced value. Probes run over the
            // (possibly expanded) `vars_probe`/`base`; the emitted consequence
            // implications are built over the ORIGINAL terms — under the
            // definitional semantics an expansion is equal to its original, so
            // a probe verdict transfers, and the output stays faithful to the
            // caller's ASTs.
            let mut out: Vec<Z3_ast> = Vec::new();
            for (idx, &v_orig) in vars_original.iter().enumerate() {
                let v = vars_probe[idx];
                if ctx.solver.term_sort(v_orig) != Sort::Bool {
                    continue; // only Boolean variables can be forced to a literal
                }
                // Forced true? `base ∧ ¬v` is UNSAT.
                let not_v = ctx.solver.not(v);
                let mut probe = base.clone();
                probe.push(not_v);
                if ctx.solver.check_sat_assuming(&probe).is_unsat() {
                    let cons = build_consequence(ctx, &base_original, v_orig);
                    out.push(term_to_ast(ctx, cons));
                    continue;
                }
                // Forced false? `base ∧ v` is UNSAT.
                let mut probe = base.clone();
                probe.push(v);
                if ctx.solver.check_sat_assuming(&probe).is_unsat() {
                    let not_v_orig = ctx.solver.not(v_orig);
                    let cons = build_consequence(ctx, &base_original, not_v_orig);
                    out.push(term_to_ast(ctx, cons));
                }
            }
            // Append to the caller's consequences vector.
            // SAFETY: `consequences`, when non-null, is a valid vector handle.
            if let Some(cv) = consequences.as_mut() {
                cv.asts.extend(out);
            }
            ctx.last_error = Z3_OK;
            Z3_L_TRUE
        })
    }
}

/// Whether `term` is a Boolean ATOM (a leaf of the propositional skeleton): a
/// constant, a variable, an uninterpreted/theory predicate application, or a
/// quantifier — i.e. NOT a Boolean connective / `ite`.
fn is_bool_atom(ctx: &Z3Context, term: Term) -> bool {
    match ctx.solver.term_kind(term) {
        TermKind::Const | TermKind::Var { .. } => true,
        TermKind::Not | TermKind::Ite => false,
        // Quantified formulas are opaque Boolean leaves of the skeleton.
        TermKind::Forall | TermKind::Exists => true,
        TermKind::Let => false,
        TermKind::App { name, .. } => !is_bool_connective(ctx, &name, term),
        // `TermKind` is #[non_exhaustive]; a future variant is treated as an
        // opaque Boolean leaf (atom), the safe default for the skeleton split.
        _ => true,
    }
}

/// Whether the application named `name` (rooted at `term`) is a Boolean
/// connective rather than a theory atom. `=` is a connective only when its
/// operands are Boolean (i.e. an `iff`); over any other sort it is a theory
/// equality atom. Note AY desugars `implies` to `or` at construction, so
/// `"=>"`/`"implies"` never actually appear here (kept for robustness).
fn is_bool_connective(ctx: &Z3Context, name: &str, term: Term) -> bool {
    match name {
        "and" | "or" | "xor" | "not" | "=>" | "implies" | "iff" | "distinct" => true,
        "=" => ctx
            .solver
            .term_children(term)
            .first()
            .map(|&ch| ctx.solver.term_sort(ch) == Sort::Bool)
            .unwrap_or(false),
        _ => false,
    }
}

/// Whether `term` is a top-level LITERAL (an atom or the negation of an atom),
/// as opposed to a Boolean connective / compound. Used to split a solver's
/// assertions into units vs non-units.
pub(crate) fn is_unit_literal(ctx: &Z3Context, term: Term) -> bool {
    match ctx.solver.term_kind(term) {
        TermKind::Not => {
            let children = ctx.solver.term_children(term);
            children.len() == 1 && is_bool_atom(ctx, children[0])
        }
        _ => is_bool_atom(ctx, term),
    }
}

/// Collect the subset of THIS solver handle's assertions that are unit literals
/// (an atom or the negation of an atom), as an AST vector.
unsafe fn collect_literal_assertions(
    ctx: &mut Z3Context,
    s: Z3_solver,
    op: &str,
    keep_units: bool,
) -> Z3_ast_vector {
    // SAFETY: `s`, when non-null, is a live handle; `as_ref` null-checks.
    let assertions = match unsafe { s.as_ref() } {
        Some(h) => h.assertions.clone(),
        None => {
            note_null_solver_handle(ctx, op);
            return cache_ast_vector(ctx, Vec::new());
        }
    };
    let asts: Vec<Z3_ast> = assertions
        .iter()
        .copied()
        .filter(|&t| is_unit_literal(ctx, t) == keep_units)
        .map(|term| term_to_ast(ctx, term))
        .collect();
    cache_ast_vector(ctx, asts)
}

/// Return the current unit literals of THIS solver handle (Z3's
/// `Z3_solver_get_units`).
///
/// AY reports the INPUT-level units: the assertions that are themselves literals
/// (an atom or a negated atom). This is a SOUND subset of "the units modulo
/// model conversion" — AY does not surface learned/derived units through this
/// stable API (documented in `ay_z3_compat.h`).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_units(c: Z3_context, s: Z3_solver) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` guards `c`; `s` handled by the helper.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            collect_literal_assertions(ctx, s, "Z3_solver_get_units", true)
        })
    }
}

/// Return the non-unit formulas of THIS solver handle (Z3's
/// `Z3_solver_get_non_units`): the assertions that are compound (a Boolean
/// connective / `ite`), i.e. not literals.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_non_units(c: Z3_context, s: Z3_solver) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` guards `c`; `s` handled by the helper.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            collect_literal_assertions(ctx, s, "Z3_solver_get_non_units", false)
        })
    }
}

/// Return the level-0 assignment trail of THIS solver handle (Z3's
/// `Z3_solver_get_trail`).
///
/// AY exposes the level-0 portion of the trail: the input unit literals, which
/// are exactly the literals assigned at decision level 0. Every returned literal
/// is genuinely on the trail (a SOUND subset); AY does not surface the deeper
/// decision-level trail entries through this stable API (documented in
/// `ay_z3_compat.h`).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_trail(c: Z3_context, s: Z3_solver) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` guards `c`; `s` handled by the helper.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            collect_literal_assertions(ctx, s, "Z3_solver_get_trail", true)
        })
    }
}

/// Return a human-readable description of the solver's supported parameters
/// (Z3's `Z3_solver_get_help`).
///
/// The listed parameters are exactly the ones AY's solver honors (see
/// `apply_supported_params`): `timeout` and `proof`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_help(c: Z3_context, _s: Z3_solver) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` guards `c`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let help = "\
ay solver parameters:\n\
  timeout (unsigned int)  check-sat timeout in milliseconds (0 = no limit)\n\
  proof   (bool)          enable proof production (default: false)\n";
            cache_string(ctx, help.to_string())
        })
    }
}

/// Return the congruence-closure root of `a` under THIS solver's completed
/// state (Z3's `Z3_solver_congruence_root`).
///
/// AY does not expose its internal e-graph's congruence ring through a stable
/// API. The HONEST, SOUND behavior is to model each term as its own singleton
/// congruence class: a term is therefore its own root. This never claims two
/// distinct terms are congruent when they are not (a sound under-approximation);
/// it may miss congruences the engine internally knows (documented in
/// `ay_z3_compat.h`). Never a fabricated representative.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_congruence_root(
    c: Z3_context,
    _s: Z3_solver,
    a: Z3_ast,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` guards `c`.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if a == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_solver_congruence_root: null AST".to_string());
                return 0;
            }
            a
        })
    }
}

/// Return the next term in `a`'s congruence class (Z3's
/// `Z3_solver_congruence_next`). The class is a cyclic list; repeated calls
/// return to the original term.
///
/// As with `Z3_solver_congruence_root`, AY models each term as its own
/// singleton class, so `next(a) == a` (the one-element cycle). Sound and
/// honest (documented in `ay_z3_compat.h`); never a fabricated sibling.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_congruence_next(
    c: Z3_context,
    _s: Z3_solver,
    a: Z3_ast,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` guards `c`.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if a == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_solver_congruence_next: null AST".to_string());
                return 0;
            }
            a
        })
    }
}

/// Tseitin encoder that turns a solver's Boolean skeleton into DIMACS CNF.
///
/// Every distinct Boolean ATOM (constant, variable, theory predicate, or
/// quantifier) becomes one propositional variable; the Boolean connectives
/// (`and`/`or`/`not`/`ite`/`xor`/`iff`) are encoded with the standard
/// definitional (biconditional) clauses. The result is EQUISATISFIABLE with the
/// skeleton. Theory semantics of the atoms are intentionally dropped — this is
/// the propositional skeleton, not a bit-blasting (documented in
/// `ay_z3_compat.h`).
pub(crate) struct DimacsEncoder<'a> {
    ctx: &'a Z3Context,
    /// (dimacs var, atom term) in allocation order, for `include_names`.
    atoms: Vec<(i32, Term)>,
    /// atom term-id -> dimacs var (dedup so equal atoms share a variable).
    atom_vars: std::collections::HashMap<u32, i32>,
    clauses: Vec<Vec<i32>>,
    next_var: i32,
}

impl<'a> DimacsEncoder<'a> {
    pub(crate) fn new(ctx: &'a Z3Context) -> Self {
        Self {
            ctx,
            atoms: Vec::new(),
            atom_vars: std::collections::HashMap::new(),
            clauses: Vec::new(),
            next_var: 1,
        }
    }

    fn fresh_var(&mut self) -> i32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn atom_var(&mut self, t: Term) -> i32 {
        let id = t.to_raw();
        if let Some(&v) = self.atom_vars.get(&id) {
            return v;
        }
        let v = self.fresh_var();
        self.atom_vars.insert(id, v);
        self.atoms.push((v, t));
        v
    }

    /// Encode formula `t` and return its DIMACS literal (a signed variable).
    fn encode(&mut self, t: Term) -> i32 {
        match self.ctx.solver.term_kind(t) {
            TermKind::Const => {
                if let Some(b) = self.ctx.solver.bool_value(t) {
                    // A constant Boolean: a fresh var forced to that polarity.
                    let v = self.fresh_var();
                    self.clauses.push(vec![if b { v } else { -v }]);
                    v
                } else {
                    self.atom_var(t)
                }
            }
            TermKind::Not => {
                let ch = self.ctx.solver.term_children(t);
                if ch.len() == 1 {
                    -self.encode(ch[0])
                } else {
                    self.atom_var(t)
                }
            }
            TermKind::Ite => {
                let ch = self.ctx.solver.term_children(t);
                // Only a Boolean-result ite is a connective in the skeleton.
                if ch.len() == 3 && self.ctx.solver.term_sort(t) == Sort::Bool {
                    let c = self.encode(ch[0]);
                    let a = self.encode(ch[1]);
                    let b = self.encode(ch[2]);
                    self.tseitin_ite(c, a, b)
                } else {
                    self.atom_var(t)
                }
            }
            TermKind::App { name, .. } => {
                let ch = self.ctx.solver.term_children(t);
                match name.as_str() {
                    "and" if ch.len() >= 2 => {
                        let lits: Vec<i32> = ch.iter().map(|&x| self.encode(x)).collect();
                        self.tseitin_and(&lits)
                    }
                    "or" if ch.len() >= 2 => {
                        let lits: Vec<i32> = ch.iter().map(|&x| self.encode(x)).collect();
                        self.tseitin_or(&lits)
                    }
                    "xor" if ch.len() == 2 => {
                        let a = self.encode(ch[0]);
                        let b = self.encode(ch[1]);
                        self.tseitin_xor(a, b)
                    }
                    // `=` over Boolean operands is `iff`; otherwise a theory atom.
                    "=" | "iff"
                        if ch.len() == 2 && self.ctx.solver.term_sort(ch[0]) == Sort::Bool =>
                    {
                        let a = self.encode(ch[0]);
                        let b = self.encode(ch[1]);
                        self.tseitin_iff(a, b)
                    }
                    _ => self.atom_var(t),
                }
            }
            // Var / Forall / Exists / Let: opaque Boolean leaves.
            _ => self.atom_var(t),
        }
    }

    /// Assert formula `t` as true, flattening a top-level `and` into separate
    /// unit assertions (matching how a solver flattens top-level conjunctions).
    pub(crate) fn assert_formula(&mut self, t: Term) {
        if let TermKind::App { name, .. } = self.ctx.solver.term_kind(t) {
            if name == "and" {
                for child in self.ctx.solver.term_children(t) {
                    self.assert_formula(child);
                }
                return;
            }
        }
        let lit = self.encode(t);
        self.clauses.push(vec![lit]);
    }

    fn tseitin_and(&mut self, lits: &[i32]) -> i32 {
        // t <-> (l1 ∧ … ∧ ln)
        let t = self.fresh_var();
        for &li in lits {
            self.clauses.push(vec![-t, li]);
        }
        let mut big = vec![t];
        for &li in lits {
            big.push(-li);
        }
        self.clauses.push(big);
        t
    }

    fn tseitin_or(&mut self, lits: &[i32]) -> i32 {
        // t <-> (l1 ∨ … ∨ ln)
        let t = self.fresh_var();
        let mut big = vec![-t];
        for &li in lits {
            big.push(li);
        }
        self.clauses.push(big);
        for &li in lits {
            self.clauses.push(vec![t, -li]);
        }
        t
    }

    fn tseitin_xor(&mut self, a: i32, b: i32) -> i32 {
        // t <-> (a ⊕ b)
        let t = self.fresh_var();
        self.clauses.push(vec![-t, a, b]);
        self.clauses.push(vec![-t, -a, -b]);
        self.clauses.push(vec![t, -a, b]);
        self.clauses.push(vec![t, a, -b]);
        t
    }

    fn tseitin_iff(&mut self, a: i32, b: i32) -> i32 {
        // t <-> (a <-> b)
        let t = self.fresh_var();
        self.clauses.push(vec![-t, -a, b]);
        self.clauses.push(vec![-t, a, -b]);
        self.clauses.push(vec![t, a, b]);
        self.clauses.push(vec![t, -a, -b]);
        t
    }

    fn tseitin_ite(&mut self, c: i32, a: i32, b: i32) -> i32 {
        // t <-> (c ? a : b)
        let t = self.fresh_var();
        self.clauses.push(vec![-t, -c, a]);
        self.clauses.push(vec![-t, c, b]);
        self.clauses.push(vec![t, -c, -a]);
        self.clauses.push(vec![t, c, -b]);
        t
    }

    /// The encoded CNF clauses (DIMACS signed literals).
    pub(crate) fn clauses(&self) -> &[Vec<i32>] {
        &self.clauses
    }

    /// The `(dimacs var, atom term)` pairs in allocation order. Variables NOT
    /// listed here are Tseitin auxiliaries / forced constants with no atom
    /// mapping.
    pub(crate) fn atoms(&self) -> &[(i32, Term)] {
        &self.atoms
    }

    /// Number of allocated DIMACS variables.
    pub(crate) fn num_vars(&self) -> usize {
        usize::try_from((self.next_var - 1).max(0)).unwrap_or(0)
    }

    pub(crate) fn render(&self, include_names: bool) -> String {
        let mut out = String::new();
        out.push_str(
            "c DIMACS CNF of the Boolean skeleton (Tseitin), emitted by ay.\n\
             c Theory atoms are propositional variables; equisatisfiable with the skeleton.\n",
        );
        if include_names {
            for (v, t) in &self.atoms {
                let name = self
                    .ctx
                    .solver
                    .format_term_checked(*t)
                    .unwrap_or_else(|| "?".to_string());
                let name = super::ffi_surface_text(self.ctx, &name);
                // Keep the mapping comment single-line.
                let name = name.replace('\n', " ");
                out.push_str(&format!("c {v} {name}\n"));
            }
        }
        let num_vars = (self.next_var - 1).max(0);
        out.push_str(&format!("p cnf {} {}\n", num_vars, self.clauses.len()));
        for clause in &self.clauses {
            for &lit in clause {
                out.push_str(&lit.to_string());
                out.push(' ');
            }
            out.push_str("0\n");
        }
        out
    }
}

/// Emit THIS solver handle's Boolean skeleton as a DIMACS CNF string (Z3's
/// `Z3_solver_to_dimacs_string`).
///
/// AY emits a Tseitin CNF of the propositional skeleton: each distinct Boolean
/// atom (including theory atoms, treated as opaque propositional variables)
/// becomes one DIMACS variable, and the Boolean connectives are encoded with
/// their standard definitional clauses. The CNF is equisatisfiable with the
/// skeleton. AY does NOT bit-blast theory atoms, so — unlike libz3 — the DIMACS
/// captures the propositional structure only (documented in `ay_z3_compat.h`);
/// variable numbering also differs from libz3's. When `include_names` is set,
/// a `c <var> <atom>` mapping comment is emitted per atom.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_to_dimacs_string(
    c: Z3_context,
    s: Z3_solver,
    include_names: bool,
) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` guards `c`; `s` null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let assertions = match s.as_ref() {
                Some(h) => h.assertions.clone(),
                None => {
                    note_null_solver_handle(ctx, "Z3_solver_to_dimacs_string");
                    return ptr::null();
                }
            };
            let mut enc = DimacsEncoder::new(ctx);
            for t in &assertions {
                enc.assert_formula(*t);
            }
            let text = enc.render(include_names);
            let text = super::ffi_surface_text(ctx, &text);
            cache_string(ctx, text)
        })
    }
}
