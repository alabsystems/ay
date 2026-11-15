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

use super::check_obligations::{
    assert_reachable_wf_guards, has_loose_bound_variable, lossy_binder_refusal,
    reachable_wf_obligations, recheck_due, validate_wf_model, WfPhase, WfVerdict,
    UNBOUND_VARIABLES_REASON,
};
use super::handle_params::{begin_handle_query, finish_handle_query, EngineSettings, ParamSet};
use super::parse_binding::{bound_parse, BoundParse, GivenDeclaration, ParseScope, ParsedContent};
use super::{
    bounded_array_ext_consequences, cache_ast_vector, cache_string,
    ensure_cross_context_translation_semantics, ffi_count_within_limit, ffi_guard_ast,
    ffi_guard_const_ptr, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void,
    ffi_read_bounded_parser_file, ffi_read_bounded_parser_text, ffi_read_bounded_text,
    finite_set_decision_gate, reachable_finite_set_axioms, require_term_ast, require_term_asts,
    term_to_ast, transfer_cross_context_ffi_metadata, DecisionOwnerFamily, FiniteSetDecisionGate,
    ModelHandle, SolverCheckOutcome, Z3Context, Z3SolverHandle, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_func_decl, Z3_model, Z3_params, Z3_solver, Z3_sort, Z3_string, Z3_symbol, Z3_EXCEPTION,
    Z3_INVALID_ARG, Z3_INVALID_USAGE, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF, Z3_OK, Z3_PARSER_ERROR,
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
            handle.parse_prior = super::parse_binding::ParsePrior::default();
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
            // A converted goal owns exact auxiliary declaration identities.
            // Adopt those existing terms at this explicit consumer boundary so
            // ordinary model extraction publishes them; never consult unrelated
            // live solver assignments when a caller model lacks a binding.
            let admitted = (|| -> Result<(), SolverError> {
                if ctx.goal_cache.is_empty() {
                    return Ok(());
                }
                let operation = ctx.solver.begin_tactic_operation()?;
                let owner = operation.admission();
                owner.admit(ctx.goal_cache.len(), 0).map_err(|_| {
                    SolverError::TacticFailed("goal consumer admission refused".into())
                })?;
                let mut selected = None;
                for &goal in &ctx.goal_cache {
                    // SAFETY: goal_cache exclusively owns each retained handle
                    // until context destruction; no callback occurs while this
                    // shared handle reference is borrowed.
                    let (count, converter) = {
                        // SAFETY: goal_cache exclusively owns the handle (see above).
                        let goal = unsafe { &*goal };
                        (goal.formulas.len(), goal.model_converter.clone())
                    };
                    if let Some(converter) = converter {
                        owner.admit(count, 0).map_err(|_| {
                            SolverError::TacticFailed("goal consumer admission refused".into())
                        })?;
                        if !operation.validate(&ctx.solver) {
                            return Err(SolverError::TacticFailed(
                                "goal consumer source changed".into(),
                            ));
                        }
                        // SAFETY: the context retains the handle for its lifetime.
                        let current = unsafe { &*goal };
                        if current.formulas.len() != count {
                            return Err(SolverError::TacticFailed("goal consumer changed".into()));
                        }
                        if current.formulas.contains(&a) {
                            selected = Some(converter);
                            break;
                        }
                    }
                }
                ay_core::term::reserve_counted(&mut handle.assertions, 1, owner).map_err(|_| {
                    SolverError::TacticFailed("solver assertion admission refused".into())
                })?;
                if !operation.validate(&ctx.solver) {
                    return Err(SolverError::TacticFailed(
                        "goal consumer source changed".into(),
                    ));
                }
                if let Some(converter) = selected {
                    ctx.solver
                        .adopt_tactic_model_constants_in_operation(operation, &converter)?;
                }
                Ok(())
            })();
            if let Err(error) = admitted {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(error.to_string());
                return;
            }
            handle.assertions.push(term);
            handle.clear_check_artifacts();
        });
    }
}

/// Set the params of the solver handle `s`.
///
/// AY honours `timeout` and proof production; they are stored on the handle
/// and applied for its own checks only.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_set_params(c: Z3_context, s: Z3_solver, p: Z3_params) {
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
            // The parameters belong to THIS handle and govern its checks only
            // (libz3 5.1.0: `s1.set("timeout", 1)` leaves a fresh `s2`'s
            // pigeonhole `unsat`); see `handle_params`.
            let Some(handle) = s.as_mut() else {
                note_null_solver_handle(ctx, "Z3_solver_set_params");
                return;
            };
            handle.params.record(&params_owned);
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

/// `Z3_solver_check` / `Z3_solver_check_assumptions` for the handle `s`
/// ([`check_solver_handle`]), leaving no definition the check adopted
/// installed on the context's shared engine ([`release_adopted_definitions`]).
///
/// # Safety
/// `s` must be null or a live solver handle of `ctx`.
pub(crate) unsafe fn check_solver_handle_isolated(
    ctx: &mut Z3Context,
    s: Z3_solver,
    assumptions: Option<&[Term]>,
    extra_lemmas: &[Term],
) -> c_int {
    // The handle's own parameters, applied in full for this check only, and
    // a cleared interrupt (see `handle_params`).
    // SAFETY: `s` is null or a live solver handle of `ctx`; the shared borrow
    // ends at this statement.
    let params = unsafe { s.as_ref() }.map_or_else(ParamSet::default, |handle| handle.params);
    let settings = EngineSettings::apply(&mut ctx.solver, params.over(ctx.default_params));
    let started = std::time::Instant::now();
    // SAFETY: forwarded verbatim; see `refuse_undecided_goal` and
    // `check_solver_handle`.
    let verdict = match unsafe { refuse_undecided_goal(ctx, s, assumptions) } {
        Some(verdict) => verdict,
        None => {
            let mut phase = WfPhase::default();
            // SAFETY: `s` is null or a live solver handle of `ctx`, forwarded
            // unchanged under this function's contract.
            let first =
                unsafe { check_solver_handle(ctx, s, assumptions, extra_lemmas, &mut phase) };
            if recheck_due(ctx, &phase, started) {
                release_adopted_definitions(ctx, "Z3_solver_check");
                let configured = ctx.solver.timeout();
                // What is left of the check's own timeout.
                ctx.solver.set_timeout(
                    configured.map(|timeout| timeout.saturating_sub(started.elapsed())),
                );
                let mut second = phase.next();
                // SAFETY: as for the first check.
                let second =
                    unsafe { check_solver_handle(ctx, s, assumptions, extra_lemmas, &mut second) };
                ctx.solver.set_timeout(configured);
                second
            } else {
                first
            }
        }
    };
    release_adopted_definitions(ctx, "Z3_solver_check");
    settings.restore(&mut ctx.solver);
    verdict
}

/// Decide a check of `s` as `unknown` without the engine when its goal holds
/// a loose bound variable or a binder of a lossy sort (see
/// `check_obligations`); `None` when the goal goes to the engine.
///
/// libz3 5.1.0 answers an assertion with a loose variable `unknown`, reason
/// "Formulas should not contain unbound variables", and an assumption with
/// one with the same text as an error (`Z3_EXCEPTION`).
///
/// # Safety
/// `s` must be null or a live solver handle of `ctx`.
unsafe fn refuse_undecided_goal(
    ctx: &mut Z3Context,
    s: Z3_solver,
    assumptions: Option<&[Term]>,
) -> Option<c_int> {
    // SAFETY: `s` is null or a live handle in the context arena (a separate
    // allocation from `*ctx`); a null handle is reported by the check itself.
    let handle = unsafe { s.as_mut() }?;
    let mut roots = handle.assertions.clone();
    roots.extend_from_slice(assumptions.unwrap_or(&[]));
    let (reason, error) = if !has_loose_bound_variable(ctx, &roots) {
        (lossy_binder_refusal(ctx, &roots)?, None)
    } else if has_loose_bound_variable(ctx, &handle.assertions) {
        (UNBOUND_VARIABLES_REASON.to_string(), None)
    } else {
        (UNBOUND_VARIABLES_REASON.to_string(), Some(Z3_EXCEPTION))
    };
    handle.clear_check_artifacts();
    if let Some(code) = error {
        ctx.last_error = code;
        ctx.error_msg = Some(reason.clone());
    }
    handle.last_reason_unknown = Some(reason);
    handle.record_check_outcome(SolverCheckOutcome::Unknown);
    Some(Z3_L_UNDEF)
}

/// Remove the definitions the engine adopted from this check's definitional
/// `forall`s (`forall y. f(y) = y + 1`), once every artefact of the check is
/// captured on its handle.
///
/// Every handle of a context shares the context's engine, and while such a
/// definition is installed the engine expands each new application of its
/// head at construction. Left installed after the check, it rewrote terms the
/// caller built for OTHER handles (measured: `f(x) == 0` built after one
/// solver's check arrived in another solver as `0 == x + 1`, which answered
/// unsat where z3 answers sat), and for the same handle after `reset` or `pop`.
/// A reset that fails leaves the definition installed, so the engine is
/// poisoned rather than allowed to build pre-expanded terms.
pub(crate) fn release_adopted_definitions(ctx: &mut Z3Context, operation: &str) {
    if !ctx.solver.has_assertion_derived_definitions() {
        return;
    }
    if let Err(e) = ctx.reset_engine_for_solver_goal() {
        ctx.poison_decision_engine(format!(
            "{operation}: an adopted definition could not be removed after the check: {e}"
        ));
    }
}

/// The check of the handle `s` itself; see [`check_solver_handle_isolated`].
///
/// # Safety
/// `s` must be null or a live solver handle of `ctx`.
unsafe fn check_solver_handle(
    ctx: &mut Z3Context,
    s: Z3_solver,
    assumptions: Option<&[Term]>,
    extra_lemmas: &[Term],
    phase: &mut WfPhase,
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
    fn record_tactic_failure(
        ctx: &mut Z3Context,
        handle: &mut Z3SolverHandle,
        operation: Option<ay_dpll::api::TacticOperation>,
        error: SolverError,
    ) {
        if let Some(operation) = operation {
            operation.publish_failure(&mut ctx.solver, &error);
        }
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(error.to_string());
        handle.last_reason_unknown = ctx.solver.reason_unknown_smtlib();
        record_unknown(ctx, handle);
    }
    fn record_decision_failure(
        ctx: &mut Z3Context,
        handle: &mut Z3SolverHandle,
        decision: &ay_dpll::api::TacticDecision,
        detail: &str,
    ) {
        let error = SolverError::TacticFailed(detail.into());
        decision.publish_failure(&mut ctx.solver, &error);
        record_tactic_failure(ctx, handle, None, error);
    }

    let check_started = std::time::Instant::now();
    let mut request = if handle.tactic.is_some() {
        match ctx.solver.begin_tactic_operation_for_check() {
            Ok(operation) => Some(operation),
            Err(error) => {
                record_tactic_failure(ctx, handle, None, error);
                return Z3_L_UNDEF;
            }
        }
    } else {
        None
    };
    if let Some(operation) = &request {
        let count = handle
            .assertions
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(handle.tracked.len()));
        let accepted = count
            .and_then(|n| {
                n.checked_mul(std::mem::size_of::<Term>())
                    .map(|bytes| (n, bytes))
            })
            .is_some_and(|(work, bytes)| operation.admission().admit(work, bytes).is_ok());
        if !accepted || !operation.validate(&ctx.solver) {
            record_tactic_failure(
                ctx,
                handle,
                request.take(),
                SolverError::TacticFailed("tactic input metadata refused".into()),
            );
            return Z3_L_UNDEF;
        }
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
    // The timeout covers the whole check, the tactic's own work included.
    let mut converted_request = None;
    let mut _formulas_only_request = None;
    if let (Some(tactic), Some(operation)) = (handle.tactic.as_ref(), request.take()) {
        let kind = match tactic.execution_kind_admitted(operation.admission()) {
            Ok(kind) => kind,
            Err(error) => {
                record_tactic_failure(
                    ctx,
                    handle,
                    Some(operation),
                    SolverError::TacticFailed(error.message),
                );
                return Z3_L_UNDEF;
            }
        };
        if kind == ay_dpll::api::TacticExecutionKind::OwnedModelConversion {
            let failure = |message: &str| SolverError::TacticFailed(message.into());
            let outcome = (|| -> Result<_, SolverError> {
                if !handle.tracked.is_empty()
                    || ctx.solver.is_producing_proofs()
                    || handle
                        .params
                        .over(ctx.default_params)
                        .clause_proof_enabled()
                {
                    return Err(failure(
                        "converted tactic proof/core transport is not implemented",
                    ));
                }
                let mut source = Vec::new();
                let count = goal
                    .len()
                    .checked_add(assumptions.map_or(0, <[Term]>::len))
                    .ok_or_else(|| failure("converted tactic source overflow"))?;
                ay_core::term::reserve_counted(&mut source, count, operation.admission())
                    .map_err(|e| failure(&e.to_string()))?;
                if !operation.validate(&ctx.solver) {
                    return Err(failure("converted tactic source changed"));
                }
                source.extend_from_slice(&goal);
                source.extend_from_slice(assumptions.unwrap_or(&[]));
                let mut subgoals = ctx
                    .solver
                    .apply_tactic_subgoals_in_operation(&operation, tactic, &source, 0, None)?;
                if subgoals.len() != 1 {
                    return Err(failure("converted solver requires exactly one subgoal"));
                }
                let subgoal = subgoals
                    .pop()
                    .ok_or_else(|| failure("missing converted subgoal"))?;
                let converter = subgoal
                    .model_converter
                    .ok_or_else(|| failure("missing tactic model converter"))?;
                Ok((subgoal.formulas, converter))
            })();
            match outcome {
                Ok((formulas, converter)) => {
                    goal = formulas;
                    converted_request = Some((operation, converter));
                }
                Err(error) => {
                    record_tactic_failure(ctx, handle, Some(operation), error);
                    return Z3_L_UNDEF;
                }
            }
        } else {
            _formulas_only_request = Some(operation);
            match ctx.solver.apply_tactic_to_goal(tactic, &mut goal) {
                Ok(progressed) => {
                    // Persist the transformed goal as the handle's assertion list (it
                    // is observable via `Z3_solver_get_assertions`, e.g. elim-and
                    // yields the individual conjuncts after a check) — but only while
                    // no scopes are open, because the scope markers index the
                    // untransformed list.
                    //
                    // A goal over other constants than the caller's (bit-blast's
                    // bits and tseitin-cnf's definitions added, solve-eqs'
                    // eliminated variables removed) is only equisatisfiable: its
                    // model does not interpret the caller's constants, so the
                    // published model falsified the caller's assertions (measured:
                    // `bit-blast` on `bvult x y` published no `x`, `y`). Such a goal
                    // is solved TOGETHER with the caller's assertions (the
                    // transformation's models extend theirs, so the verdict is
                    // unchanged) and is not persisted as the handle's assertions.
                    if progressed {
                        let original = free_constant_names(&ctx.solver, &asserted_keys);
                        let transformed = free_constant_names(&ctx.solver, &goal);
                        if transformed != original {
                            for &assertion in &asserted_keys {
                                if !goal.contains(&assertion) {
                                    goal.push(assertion);
                                }
                            }
                        } else if handle.scope_markers.is_empty() {
                            handle.assertions = goal.clone();
                        }
                    }
                }
                // HONEST FAILURE: the tactic produced NO goal (e.g. `bit-blast` on an
                // out-of-fragment bit-vector goal). Surface it as an error + `unknown`
                // rather than silently solving the untransformed goal — never a
                // fabricated verdict for a goal the tactic did not actually produce.
                Err(e) => {
                    record_tactic_failure(ctx, handle, _formulas_only_request.take(), e);
                    return Z3_L_UNDEF;
                }
            }
        }
    }

    // Effective assumptions = explicit check-assumptions ++ tracking literals.
    // When both are empty this is a plain `check_sat` (no assumption machinery),
    // preserving the original behavior for untracked solvers.
    let mut effective: Vec<Term> = Vec::new();
    if let Some(terms) = assumptions {
        if converted_request.is_none() {
            effective.extend_from_slice(terms);
        }
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

    // The well-formedness obligations of the lossily lowered free symbols
    // this check reaches (see `wf_guards` and `WfPhase`); a reached symbol
    // whose guard could not be built leaves the goal undecided.
    let wf = {
        let mut wf_roots = goal.clone();
        wf_roots.extend(effective.iter().copied());
        wf_roots.extend(lemmas.iter().copied());
        wf_roots.extend(ctx.global_definition_axioms.iter().copied());
        match reachable_wf_obligations(ctx, &wf_roots) {
            Ok(obligations) => obligations,
            Err(reason) => {
                handle.last_reason_unknown = Some(reason);
                record_unknown(ctx, handle);
                return Z3_L_UNDEF;
            }
        }
    };
    let wf_guards = phase.guards(&wf);

    // Public array extensionality over a BOUNDED carrier (see `bounded_arrays`).
    // Each equality is a consequence of a top-level assertion of THIS check, and
    // is released only after the whole term set this check will hand the engine
    // is re-verified to admit the canonical extension the proof needs — never
    // context-globally, and never for a goal holding an interpreted array term.
    // It stays out of `handle.assertions`, so `Z3_solver_get_assertions` and
    // unsat cores keep reporting only what the caller asserted.
    {
        // Every guard the goal may be checked with, asserted now or by the
        // guarded re-check.
        let mut canonicity_roots: Vec<Term> = wf.eager.clone();
        canonicity_roots.extend(wf.lazy.iter().copied());
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
    let include_rec_axioms = match &rec_mode {
        RecDefMode::None => true,
        RecDefMode::Expanded => false,
        RecDefMode::Residual { keep_axioms, .. } => *keep_axioms,
    };
    if converted_request.is_none() {
        if let Err(e) = ctx.reset_engine_for_solver_goal() {
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
        for &guard in &wf_guards {
            if let Err(e) = ctx.solver.try_assert_term(guard) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                record_unknown(ctx, handle);
                return Z3_L_UNDEF;
            }
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
    }
    let configured_timeout = ctx.solver.timeout();
    if let (Some(timeout), true) = (configured_timeout, handle.tactic.is_some()) {
        let left = timeout.saturating_sub(check_started.elapsed());
        ctx.solver
            .set_timeout(Some(left.max(std::time::Duration::from_millis(1))));
    }
    if let Some(timeout) = phase.first_check_timeout(&wf, ctx.solver.timeout()) {
        ctx.solver.set_timeout(Some(timeout));
    }
    let mut converted_decision = None;
    let verified = if let Some((operation, converter)) = converted_request.take() {
        let roots = (|| -> Result<Vec<Term>, String> {
            let sets = reachable_finite_set_axioms(ctx, &finite_set_roots);
            let rec: &[Term] = if match &rec_mode {
                RecDefMode::None => true,
                RecDefMode::Expanded => false,
                RecDefMode::Residual { keep_axioms, .. } => *keep_axioms,
            } {
                &ctx.global_definition_axioms
            } else {
                &[]
            };
            let mut roots = Vec::new();
            for slice in [
                &goal[..],
                &ctx.background_axioms[..],
                rec,
                &sets[..],
                &wf_guards[..],
                &lemmas[..],
            ] {
                ay_core::term::reserve_counted(&mut roots, slice.len(), operation.admission())
                    .map_err(|e| e.to_string())?;
                if !operation.validate(&ctx.solver) {
                    return Err("tactic decision source changed".into());
                }
                roots.extend_from_slice(slice);
            }
            Ok(roots)
        })();
        let result = match roots {
            Ok(roots) => {
                if !ctx.optimize_handle_cache.is_empty() {
                    ctx.optimize_engine_displaced = true;
                }
                ctx.solver.check_converted_tactic_goal_in_operation(
                    operation, &converter, &roots, &effective,
                )
            }
            Err(detail) => {
                let error = SolverError::TacticFailed(detail);
                operation.publish_failure(&mut ctx.solver, &error);
                Err(error)
            }
        };
        match result {
            Ok(decision) => {
                let verified = decision.result.clone();
                converted_decision = Some(decision);
                verified
            }
            Err(error) => {
                ctx.solver.set_timeout(configured_timeout);
                record_tactic_failure(ctx, handle, None, error);
                return Z3_L_UNDEF;
            }
        }
    } else if effective.is_empty() {
        ctx.solver.check_sat()
    } else {
        ctx.solver.check_sat_assuming(&effective)
    };
    ctx.solver.set_timeout(configured_timeout);
    // Materialize the check artefacts into the handle (a later check by any
    // handle replaces the engine-side state). Each is the engine's own
    // artefact for exactly this goal — nothing is fabricated, and a
    // non-SAT/non-UNSAT check simply leaves the matching field `None`.
    handle.last_model = ctx.solver.model().map(|m| m.into_inner());
    // Raw model text captured alongside: it carries the arity > 0 function
    // tables the parsed constants-only `Model` drops, so `Z3_model` handles
    // can resolve UF applications from the snapshot. It is the decoder text
    // (`Solver::model_str_for_decoder`, #overloaded-nil-surface), which a
    // converted decision below may replace.
    handle.last_model_text = ctx.solver.model_str_for_decoder();
    if let Some(decision) = converted_decision.as_mut() {
        if let Some(model) = decision.model.take() {
            // Converted models contain supported scalar interpretations only;
            // use the same typed renderer as the public model API below.
            match super::model_params::render_converted_model_text(ctx, model, decision) {
                Some((model, text)) => {
                    handle.last_model = Some(model);
                    handle.last_model_text = Some(text);
                }
                None => {
                    record_decision_failure(
                        ctx,
                        handle,
                        decision,
                        "converted model rendering refused",
                    );
                    return Z3_L_UNDEF;
                }
            }
        }
        if !decision.validate(&ctx.solver) {
            record_decision_failure(ctx, handle, decision, "converted model source changed");
            return Z3_L_UNDEF;
        }
    }
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
    // A SAT model must give every reached Char / finite-domain carrying
    // symbol a value of its public sort; a first check that does not, or
    // that answered `unknown`, is followed by a check in the other mode (see
    // `WfPhase`).
    if lbool == Z3_L_TRUE {
        match validate_wf_model(
            ctx,
            &wf,
            handle.last_model.as_ref(),
            handle.last_model_text.as_deref(),
            phase.asserts_quantified_guards(),
            phase.may_recheck(&wf),
        ) {
            WfVerdict::Accept => {}
            WfVerdict::Retry(reason) => {
                phase.recheck = true;
                handle.last_reason_unknown = Some(reason);
                lbool = Z3_L_UNDEF;
            }
            WfVerdict::Refuse(reason) => {
                handle.last_reason_unknown = Some(reason);
                lbool = Z3_L_UNDEF;
            }
        }
    } else if lbool == Z3_L_UNDEF {
        phase.note_undecided(&wf);
    }
    // Publish the model of THIS handle's goal only, and only when the API can
    // carry every value the engine's validated model assigns (see
    // `scope_published_model`); otherwise SAT is not published.
    if lbool == Z3_L_TRUE {
        let mut scope_roots = asserted_keys.clone();
        scope_roots.extend(goal.iter().copied());
        scope_roots.extend(effective.iter().copied());
        scope_roots.extend(assumptions.unwrap_or(&[]).iter().copied());
        scope_roots.extend(lemmas.iter().copied());
        if let Some(propagator) = &handle.propagator {
            scope_roots.extend(propagator.registered.iter().copied());
        }
        let mut axioms = ctx.background_axioms.clone();
        if include_rec_axioms {
            axioms.extend(ctx.global_definition_axioms.iter().copied());
        }
        axioms.extend(reachable_finite_set_axioms(ctx, &finite_set_roots));
        // The caller's own constraints of this check (before any tactic
        // rewrote them): what the published model must not falsify (see
        // `scope_published_model`).
        let mut obligations = asserted_keys;
        obligations.extend(assumptions.unwrap_or(&[]).iter().copied());
        // The terms the engine received verbatim as assertions or
        // assumptions: its validated model-check pipeline confirmed these.
        let mut engine_roots = goal.clone();
        engine_roots.extend(effective.iter().copied());
        if let Err(reason) = scope_published_model(
            ctx,
            handle,
            &scope_roots,
            &axioms,
            &PublicationObligations {
                obligations: &obligations,
                engine_roots: &engine_roots,
            },
        ) {
            handle.last_reason_unknown = Some(reason);
            lbool = Z3_L_UNDEF;
        }
    }
    if lbool == Z3_L_FALSE && ctx.solver.is_producing_proofs() {
        handle.last_clause_trail_requested = handle
            .params
            .over(ctx.default_params)
            .clause_proof_enabled();
        if handle.last_clause_trail_requested {
            handle.last_clause_trail = ctx.solver.native_clause_trail();
        }
    }
    if lbool == Z3_L_FALSE && handle.last_proof_alethe.is_some() {
        handle.last_proof_dag = ctx.solver.native_proof_dag(
            handle
                .assertions
                .iter()
                .copied()
                .chain(handle.tracked.iter().map(|(tracking, _)| *tracking))
                .chain(assumptions.into_iter().flatten().copied()),
        );
    }
    if lbool == Z3_L_FALSE {
        if let Some(decision) = &converted_decision {
            // The converter was captured from these exact authored
            // assertions AND all check-local assumptions. A strictly
            // accepted reduced UNSAT therefore supports their complete
            // assumption set as a valid, deliberately nonminimal core.
            let source_assumptions = assumptions.unwrap_or(&[]);
            let mut core = Vec::new();
            if ay_core::term::reserve_counted(
                &mut core,
                source_assumptions.len(),
                decision.admission(),
            )
            .is_err()
                || !decision.validate(&ctx.solver)
            {
                record_decision_failure(
                    ctx,
                    handle,
                    decision,
                    "converted source core copy refused",
                );
                return Z3_L_UNDEF;
            }
            core.extend_from_slice(source_assumptions);
            handle.last_unsat_core = Some(core);
        }
    }
    if let Some(decision) = &converted_decision {
        if !decision.validate(&ctx.solver) {
            record_decision_failure(
                ctx,
                handle,
                decision,
                "converted decision publication refused",
            );
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

/// What a published SAT model must satisfy.
pub(crate) struct PublicationObligations<'a> {
    /// The caller's own assertions (before a tactic rewrote them) and
    /// assumptions.
    pub(crate) obligations: &'a [Term],
    /// The terms the engine received verbatim as assertions or assumptions.
    pub(crate) engine_roots: &'a [Term],
}

/// Refuse a scoped SAT model whose API form would differ from the engine's
/// validated one (a caller function the API tables cannot carry whole), or
/// under which any of the caller's assertions or assumptions is not literally
/// true, read as `Z3_model_eval` with model completion reads it — unless the
/// engine's own validated model-check pipeline confirmed that very assertion
/// for that very model (see [`engine_confirmed`]).
fn refuse_untransported_model(
    ctx: &mut Z3Context,
    handle: &Z3SolverHandle,
    publication: &PublicationObligations<'_>,
) -> Result<(), String> {
    let (Some(model), Some(text)) = (handle.last_model.clone(), handle.last_model_text.clone())
    else {
        return Ok(());
    };
    refuse_untransported_model_parts(ctx, model, &text, publication)
}

/// [`refuse_untransported_model`] for a model and its engine text, as an
/// Optimize check publishes them too.
pub(crate) fn refuse_untransported_model_parts(
    ctx: &mut Z3Context,
    model: ay_dpll::api::Model,
    text: &str,
    publication: &PublicationObligations<'_>,
) -> Result<(), String> {
    // Function interpretations travel as the engine's `define-fun` tables;
    // every one the scoped text carries must reach the API whole (every row
    // and the else value), or the published function differs from the one
    // the engine validated (measured: a BV-ranged table vanished, and rows at
    // negative Int points were dropped, publishing tables that violate the
    // assertions).
    let func_interps = super::model_params::model_func_interps(&mut ctx.solver, text);
    if let Some((name, body)) =
        super::model_params::unrepresented_function_tables(&mut ctx.solver, text, &func_interps)
            .into_iter()
            // Only the caller's own uninterpreted functions: a datatype selector's
            // totalization (`(ite ((_ is some) x) (value x) 0)`) and a recursive
            // definition are interpreted by their theory, not by the published table.
            .find(|(name, _)| {
                !ctx.rec_fun_defs.contains_key(name)
                    && ctx.ffi_func_names.values().any(|f| f == name)
            })
    {
        let message = format!(
            "the validated model interprets {name} as {body}, which the API model \
             cannot represent; sat is not published without it"
        );
        return Err(super::ffi_surface_text(ctx, &message));
    }
    // Backstop (fail closed): the published model, read exactly as
    // `Z3_model_eval` with model completion reads it, must make every one of
    // the caller's own assertions and assumptions literally true. A transport
    // loss between the engine's validated model and the API model that the
    // checks above do not name, or an obligation the engine never saw
    // verbatim, is refused here instead of reaching the caller as a wrong
    // witness (measured: a quantified assumption the published table
    // falsified, a function left out of the model, an array without a value).
    let probe = ModelHandle {
        model,
        func_interps,
        user_const_interps: Vec::new(),
        user_func_interps: Vec::new(),
        rec_def_count: ctx.rec_fun_defs.len(),
        complete_functions: true,
        _ctx: ptr::null_mut(),
    };
    for &obligation in publication.obligations {
        let value = super::model_params::eval_term_under_model(ctx, &probe, obligation, true);
        match value.and_then(|value| ctx.solver.bool_value(value)) {
            Some(true) => continue,
            Some(false) => {
                let shown = super::ffi_surface_text(ctx, &ctx.solver.format_term(obligation));
                return Err(format!(
                    "the published model falsifies the assertion {shown}; sat is not \
                     published with a model that violates it"
                ));
            }
            None => {}
        }
        if engine_confirmed(ctx, &probe, obligation, value, publication.engine_roots) {
            continue;
        }
        let shown = super::ffi_surface_text(ctx, &ctx.solver.format_term(obligation));
        let residual = match value {
            Some(value) => format!(
                "it evaluates to {}",
                super::ffi_surface_text(ctx, &ctx.solver.format_term(value))
            ),
            None => "it cannot be evaluated".to_string(),
        };
        return Err(format!(
            "the published model does not confirm the assertion {shown} ({residual}); sat \
             is not published without confirming every assertion"
        ));
    }
    Ok(())
}

/// Whether AY's validated model-check pipeline confirmed `obligation` for the
/// published model although the API evaluator leaves it undecided.
///
/// Only a QUANTIFIED residual qualifies (a quantifier the API evaluator cannot
/// fold): a quantifier-free residual means the API model lacks an
/// interpretation the engine relied on (a selector applied to the wrong
/// constructor, a division by zero), which z3's completion would read
/// differently. The obligation must have reached the engine verbatim (a
/// tactic's or a recursive definition's rewrite was validated, not the
/// caller's term), every SAT the engine reports passed its model gates for
/// exactly the engine's printed model, and every symbol of the obligation
/// must be interpreted by the published model itself, so completion cannot
/// make the API model differ from the one the engine validated.
fn engine_confirmed(
    ctx: &Z3Context,
    probe: &ModelHandle,
    obligation: Term,
    residual: Option<Term>,
    engine_roots: &[Term],
) -> bool {
    if !engine_roots.contains(&obligation) {
        return false;
    }
    let residual = residual.unwrap_or(obligation);
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![residual];
    let mut quantified = false;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(
            ctx.solver.term_kind(term),
            TermKind::Forall | TermKind::Exists
        ) {
            quantified = true;
        }
        stack.extend(ctx.solver.term_children(term));
    }
    if !quantified {
        return false;
    }
    let Some(leaves) = super::model_params::scoped_free_leaves(&ctx.solver, obligation) else {
        return false;
    };
    let constants_interpreted = leaves.iter().all(|&leaf| {
        ctx.solver.var_name(leaf).is_some_and(|name| {
            probe.model.value_by_name(&name).is_some() || ctx.solver.is_nullary_constructor(&name)
        })
    });
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![obligation];
    let mut functions_interpreted = true;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::App { name, num_args } = ctx.solver.term_kind(term) {
            if num_args > 0
                && ctx.ffi_func_names.values().any(|f| *f == name)
                && !probe.func_interps.iter().any(|fi| fi.name == name)
            {
                functions_interpreted = false;
                break;
            }
        }
        stack.extend(ctx.solver.term_children(term));
    }
    constants_interpreted && functions_interpreted
}

/// Names of the constants (`Var` leaves) occurring in `roots`, declared or
/// not (a tactic's fresh bits and definitions are undeclared).
fn free_constant_names(
    solver: &ay_dpll::api::Solver,
    roots: &[Term],
) -> std::collections::HashSet<String> {
    let mut names = std::collections::HashSet::new();
    let mut seen = std::collections::HashSet::new();
    let mut stack: Vec<Term> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::Var { name } = solver.term_kind(term) {
            names.insert(name);
        }
        stack.extend(solver.term_children(term));
    }
    names
}

/// Restrict the SAT model just materialized on `handle` to the symbols of this
/// check's goal, and refuse a model the API cannot represent.
///
/// Every solver handle of a context runs on the context's single engine, whose
/// model lists every symbol declared on that engine — including constants that
/// only OTHER handles assert (measured: a model of `xi = 2^xi` listed `x = 0`
/// from a sibling solver). Z3 publishes exactly the symbols of the solver's own
/// assertions, so the published model keeps the declared symbols occurring in
/// `roots` (the caller's assertions, the transformed goal, assumptions, tracked
/// literals, propagator lemmas and registrations), closed under every axiom in
/// `axioms` that mentions a kept symbol (a context-level theory axiom ties its
/// symbols together, so model completion needs all of them). Restriction never
/// changes a retained value, so the published model still satisfies the goal.
///
/// The constants-only API model is parsed from the engine's model text. A
/// constant whose value it cannot parse (e.g. an irrational algebraic
/// `(root-obj ...)` for `x * x = 2`) would silently vanish from the published
/// model — measured: `sat` with an EMPTY model — so a validated model that
/// cannot be carried whole is refused here and the check reports `unknown`
/// with the reason instead.
fn scope_published_model(
    ctx: &mut Z3Context,
    handle: &mut Z3SolverHandle,
    roots: &[Term],
    axioms: &[Term],
    publication: &PublicationObligations<'_>,
) -> Result<(), String> {
    // A sat without the engine's model would publish an EMPTY model, under
    // which the caller's assertions read as false (z3 completion defaults).
    if handle.last_model.is_none() || handle.last_model_text.is_none() {
        let detail = ctx
            .solver
            .try_get_model_str_for_decoder()
            .err()
            .map_or_else(|| "no model".to_string(), |e| e.to_string());
        return Err(format!(
            "the engine reported sat but its model is unavailable ({detail}); sat is not \
             published without a model"
        ));
    }
    let symbols_of = |terms: &[Term]| {
        ctx.solver
            .declared_symbols_in(terms)
            .map_err(|e| format!("Z3_solver_check: model scope could not be computed: {e}"))
    };
    let mut keep = symbols_of(roots)?;
    let mut pending_axioms = axioms
        .iter()
        .map(|&axiom| symbols_of(&[axiom]))
        .collect::<Result<Vec<_>, _>>()?;
    loop {
        let before = pending_axioms.len();
        pending_axioms.retain(|symbols| {
            if symbols.is_disjoint(&keep) {
                return true;
            }
            keep.extend(symbols.iter().cloned());
            false
        });
        if pending_axioms.len() == before {
            break;
        }
    }
    if let Some(model) = handle.last_model.as_mut() {
        model.retain_names(|name| keep.contains(name));
    }
    if let Some(text) = handle.last_model_text.as_deref() {
        let scoped = super::model_params::retain_model_text_symbols(text, &keep);
        handle.last_model_text = Some(scoped);
    }
    if let (Some(model), Some(text)) = (&handle.last_model, &handle.last_model_text) {
        let missing = super::model_params::unrepresented_model_constants(text, model)
            .into_iter()
            .find(|(name, _)| !ctx.rec_fun_defs.contains_key(name));
        if let Some((name, value)) = missing {
            let name = super::model_params::model_entry_display_name(ctx, &name);
            return Err(format!(
                "the validated model assigns {name} the value {value}, which the API \
                 model cannot represent; sat is not published without it"
            ));
        }
    }
    refuse_untransported_model(ctx, handle, publication)
}

/// The assertions a parse produced, unless they involve strings while z3's
/// `encoding` is not unicode; each is marked as AY's own construction (see
/// `provenance.rs`).
fn accept_parsed_assertions(
    ctx: &mut Z3Context,
    operation: &str,
    assertions: Vec<Term>,
) -> Option<Vec<Term>> {
    if super::zstring::refuse_parsed_under_non_unicode_encoding(ctx, operation, &assertions) {
        return None;
    }
    for &term in &assertions {
        super::provenance::mark_produced_term(ctx, term);
    }
    Some(assertions)
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
///
/// The text's declarations are bound to the context's with `scope` in view
/// (see `parse_binding`).
pub(crate) fn parse_solver_transaction_scoped(
    ctx: &mut Z3Context,
    input: &str,
    operation: &str,
    scope: &ParseScope,
) -> Option<ParsedContent> {
    let commands = parse_preflight(ctx, input, operation)?;
    // Claim only after non-mutating preflight succeeds. A malformed or
    // unsupported script must not reserve this otherwise-pristine context for
    // the Solver family and thereby prevent a later Optimize constructor.
    if !ctx.claim_decision_owner(DecisionOwnerFamily::Solver, operation) {
        return None;
    }
    // The parse runs on the shared engine: an Optimize handle's engine state
    // is displaced and replayed before its next use.
    if !ctx.optimize_handle_cache.is_empty() {
        ctx.optimize_engine_displaced = true;
    }

    ctx.decision_engine_poisoned = Some(format!(
        "{operation}: parse transaction was interrupted before completion"
    ));
    // A scoped parse leaves the engine as it was (its scope is popped), so the
    // other handles' check artefacts stay valid, as they do in z3 (measured:
    // re-reading one solver's model after another solver's `from_string`
    // returned no model, which z3py read as an empty, invalid one). The
    // caller retires the parsing handle's own artefacts.
    if let Some(decided) = bound_solver_parse(ctx, input, operation, scope, &commands) {
        let mut content = decided?;
        content.assertions = accept_parsed_assertions(ctx, operation, content.assertions)?;
        return Some(content);
    }
    ctx.clear_decision_check_artifacts();
    let before: std::collections::HashSet<String> = ctx
        .solver
        .symbol_signatures_core()
        .into_iter()
        .map(|(_, identity, ..)| identity)
        .collect();
    match ctx.solver.parse_smtlib2_z3_5(input) {
        Ok(batch) => match super::retain_parsed_finite_set_batch(ctx, batch) {
            Ok(retained) => {
                ctx.decision_engine_poisoned = None;
                ctx.last_error = Z3_OK;
                ctx.error_msg = None;
                register_global_parse_symbols(ctx, &commands, &before);
                // The parsed assertions belong to the caller's handle, which
                // re-asserts them at its check; a definition the engine
                // adopted from them must not rewrite terms built meanwhile.
                release_adopted_definitions(ctx, operation);
                let assertions = accept_parsed_assertions(ctx, operation, retained.assertions)?;
                Some(ParsedContent {
                    assertions,
                    ..ParsedContent::default()
                })
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

/// The bound parse of a Solver-family text (see `parse_binding`): `Some` with
/// the transaction's result when it decided the text, `None` when the text is
/// outside the rebinding fragment and may take the global parse.
fn bound_solver_parse(
    ctx: &mut Z3Context,
    input: &str,
    operation: &str,
    scope: &ParseScope,
    commands: &[Command],
) -> Option<Option<ParsedContent>> {
    match bound_parse(ctx, input, scope) {
        BoundParse::Ineligible(reason) => {
            // The global parse declares the text's names as engine symbols of
            // their own. A name the context already declares would then be
            // two unrelated symbols (measured: `sat` with the model `[a = 0,
            // a = 3]` where z3 answers `unsat`), so such a text is refused
            // before anything executes.
            if let Some(name) = global_parse_collision(ctx, commands) {
                ctx.decision_engine_poisoned = None;
                ctx.last_error = Z3_PARSER_ERROR;
                ctx.error_msg = Some(format!(
                    "{operation}: the text declares '{name}', which this context already \
                     declares, and AY cannot bind the text's '{name}' to it in a text with \
                     {reason}"
                ));
                return Some(None);
            }
        }
        BoundParse::Parsed(content) => {
            ctx.decision_engine_poisoned = None;
            ctx.last_error = Z3_OK;
            ctx.error_msg = None;
            release_adopted_definitions(ctx, operation);
            return Some(Some(content));
        }
        // The parse ran inside a scope that was popped, and the text
        // sets no option, so the engine is as it was: an error, no
        // poison.
        BoundParse::Failed(reason) => {
            ctx.decision_engine_poisoned = None;
            ctx.last_error = Z3_PARSER_ERROR;
            ctx.error_msg = Some(format!("{operation}: {reason}"));
            return Some(None);
        }
        BoundParse::ScopeLost(reason) => {
            ctx.clear_decision_check_artifacts();
            ctx.poison_decision_engine(format!("{operation}: {reason}"));
            return Some(None);
        }
    }
    None
}

/// The names a text declares (functions, constants, sorts, datatypes and
/// their members).
fn text_declared_names(commands: &[Command]) -> Vec<String> {
    let mut names = Vec::new();
    for command in commands {
        match command {
            Command::DeclareFun(name, ..)
            | Command::DeclareConst(name, _)
            | Command::DefineFun(name, ..)
            | Command::DefineFunRec(name, ..)
            | Command::DeclareSort(name, _)
            | Command::DefineSort(name, ..) => names.push(name.clone()),
            Command::DefineFunsRec(declarations, _) => {
                names.extend(declarations.iter().map(|(name, ..)| name.clone()));
            }
            Command::DeclareDatatype(name, datatype) => {
                names.push(name.clone());
                datatype_member_names(datatype, &mut names);
            }
            Command::DeclareDatatypes(sorts, datatypes) => {
                names.extend(sorts.iter().map(|sort| sort.name.clone()));
                for datatype in datatypes {
                    datatype_member_names(datatype, &mut names);
                }
            }
            _ => {}
        }
    }
    names
}

fn datatype_member_names(datatype: &ay_frontend::command::DatatypeDec, names: &mut Vec<String>) {
    for constructor in &datatype.constructors {
        names.push(constructor.name.clone());
        names.extend(constructor.selectors.iter().map(|s| s.name.clone()));
    }
}

/// The first name a globally parsed text would declare that this context
/// already declares (a constant, function or sort of the API, or of an
/// earlier parse).
pub(crate) fn global_parse_collision(ctx: &Z3Context, commands: &[Command]) -> Option<String> {
    text_declared_names(commands).into_iter().find(|name| {
        ctx.ffi_used_decl_names.contains(name)
            || ctx
                .ffi_sort_symbols
                .values()
                .any(|symbol| symbol.display_name() == *name)
            // An earlier text's `declare-sort` (see `datatype_name_collision`).
            || ctx.uninterpreted_sort_names.contains(name)
    })
}

/// Make the constants and functions a global parse declared the context's
/// declarations of those names: a later `Z3_mk_const` / `Z3_mk_func_decl`
/// with the same name and signature returns them (z3 identifies declarations
/// by name and signature), and a later parse's collision check sees them.
fn register_global_parse_symbols(
    ctx: &mut Z3Context,
    commands: &[Command],
    before: &std::collections::HashSet<String>,
) {
    let declared: std::collections::HashSet<String> =
        text_declared_names(commands).into_iter().collect();
    for (name, identity, domain, range, is_definition) in ctx.solver.symbol_signatures_core() {
        if is_definition || before.contains(&identity) || !declared.contains(&name) {
            continue;
        }
        let symbol = super::SymbolKey::String(name.clone());
        ctx.ffi_used_decl_names.insert(name.clone());
        ctx.ffi_decl_symbols
            .insert(identity.clone(), symbol.clone());
        if domain.is_empty() {
            if let Ok(term) = ctx.solver.try_declare_const(&identity, range.clone()) {
                ctx.ffi_const_cache
                    .entry((symbol.clone(), range))
                    .or_insert(term);
                ctx.ffi_const_metadata
                    .entry(term)
                    .or_insert((identity.clone(), symbol));
                ctx.ffi_const_terms_by_identity
                    .entry(identity)
                    .or_insert(term);
            }
        } else {
            let key = (symbol, domain.clone(), range.clone());
            ctx.ffi_func_names
                .entry(key.clone())
                .or_insert(identity.clone());
            ctx.ffi_func_decls
                .entry(key)
                .or_insert_with(|| ay_dpll::api::FuncDecl::new(identity, domain, range));
        }
    }
}

/// The non-mutating preflight of [`parse_solver_transaction_scoped`]: the
/// text's commands, or `None` with the context error set for a text the
/// assertion-returning parse bridge refuses before execution.
fn parse_preflight(ctx: &mut Z3Context, input: &str, operation: &str) -> Option<Vec<Command>> {
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
    Some(commands)
}

/// The sorts and declarations a `Z3_parse_smtlib2_string` caller names.
///
/// # Safety
/// Each non-null array holds its count of handles of `ctx`.
pub(crate) unsafe fn caller_parse_scope(
    ctx: &Z3Context,
    num_sorts: c_uint,
    sort_names: *const Z3_symbol,
    sorts: *const Z3_sort,
    num_decls: c_uint,
    decl_names: *const Z3_symbol,
    decls: *const Z3_func_decl,
) -> Result<ParseScope, String> {
    let mut scope = ParseScope::default();
    let symbol_name = |symbol: Z3_symbol| -> Result<String, String> {
        if symbol.is_null() {
            return Err("null symbol".to_string());
        }
        // SAFETY: a non-null symbol handle of this context.
        Ok(unsafe { (*symbol).key.display_name() })
    };
    if num_sorts > 0 {
        if sort_names.is_null() || sorts.is_null() {
            return Err("null sort array".to_string());
        }
        for i in 0..num_sorts as usize {
            // SAFETY: `i` is below the caller's count for both arrays.
            let (name, sort) = unsafe { (*sort_names.add(i), *sorts.add(i)) };
            let sort = super::sort_arg_handle(ctx, sort).ok_or("null sort")?;
            // SAFETY: decoded to a live sort handle of this context.
            scope
                .sorts
                .push((symbol_name(name)?, unsafe { (*sort).sort.clone() }));
        }
    }
    if num_decls > 0 {
        if decl_names.is_null() || decls.is_null() {
            return Err("null declaration array".to_string());
        }
        for i in 0..num_decls as usize {
            // SAFETY: `i` is below the caller's count for both arrays.
            let (name, decl) = unsafe { (*decl_names.add(i), *decls.add(i)) };
            let decl = super::func_decl_arg_handle(ctx, decl).ok_or("null declaration")?;
            // SAFETY: decoded to a live declaration handle of this context.
            let decl = unsafe { (*decl).decl.clone() };
            let given = if decl.arity() == 0 {
                let term = ctx
                    .ffi_const_terms_by_identity
                    .get(decl.name())
                    .copied()
                    .ok_or_else(|| format!("{} is not a declared constant", decl.name()))?;
                GivenDeclaration::Constant(term)
            } else {
                GivenDeclaration::Function(decl)
            };
            scope.given.push((symbol_name(name)?, given));
        }
    }
    Ok(scope)
}

/// Parse `text` into the solver handle `s`: its declarations are bound to the
/// context's (`parse_binding`), the solver's earlier parsed declarations stay
/// visible (z3 keeps one command context per solver), and the assertions join
/// the handle's.
///
/// # Safety
/// `s` must be a non-null solver handle of `ctx`.
unsafe fn parse_into_solver_handle(ctx: &mut Z3Context, s: Z3_solver, text: &str, operation: &str) {
    let scope = ParseScope {
        // SAFETY: the caller guarantees `s` is a live handle; the arena
        // allocation is separate from `*ctx`.
        prior: unsafe { (*s).parse_prior.clone() },
        ..ParseScope::default()
    };
    if let Some(content) = parse_solver_transaction_scoped(ctx, text, operation, &scope) {
        // SAFETY: as above; no reference to the handle was held while the
        // transaction retired every handle's check artefacts.
        let handle = unsafe { &mut *s };
        handle.assertions.extend(content.assertions);
        handle.parse_prior.extend(content.prior);
        handle.clear_check_artifacts();
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
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            check_solver_handle_isolated(ctx, s, None, &[])
        })
    }
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
            check_solver_handle_isolated(ctx, s, assumptions, &[])
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
            // Without a current model z3 raises "there is no current model";
            // a null model without an error was read by z3py as an empty
            // model (measured: an invalid re-read model of a sat check). An
            // `unknown` publishes no model either: its candidate was not
            // admitted.
            let no_model = |ctx: &mut Z3Context| {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some("Z3_solver_get_model: there is no current model".to_string());
                ptr::null_mut()
            };
            if solver_handle.last_check_outcome != Some(SolverCheckOutcome::Sat) {
                return no_model(ctx);
            }
            match solver_handle.last_model.clone() {
                Some(model) => {
                    // Function interpretations are part of the snapshot: parse
                    // them out of the raw model text captured at check time.
                    let func_interps = solver_handle
                        .last_model_text
                        .as_deref()
                        .map(|text| super::model_params::model_func_interps(&mut ctx.solver, text))
                        .unwrap_or_default();
                    let handle = Box::into_raw(Box::new(ModelHandle {
                        model,
                        func_interps,
                        user_const_interps: Vec::new(),
                        user_func_interps: Vec::new(),
                        rec_def_count: ctx.rec_fun_defs.len(),
                        complete_functions: true,
                        _ctx: c,
                    }));
                    ctx.model_cache.push(handle);
                    handle
                }
                None => no_model(ctx),
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
            let assertions = s
                .as_ref()
                .map(|handle| handle.assertions.as_slice())
                .unwrap_or(&[]);
            let Some(sexpr) = super::finite_field::format_public_assertions(ctx, assertions) else {
                return ptr::null();
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
    num_sorts: c_uint,
    sort_names: *const Z3_symbol,
    sorts: *const Z3_sort,
    num_decls: c_uint,
    decl_names: *const Z3_symbol,
    decls: *const Z3_func_decl,
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
            // z3 parses with a fresh symbol table holding the caller-named
            // sorts and declarations (`decls={'foo': x}` binds the text's
            // `foo` to `x`).
            // SAFETY: the caller guarantees each array holds its count of
            // handles of this context.
            let scope = caller_parse_scope(
                ctx, num_sorts, sort_names, sorts, num_decls, decl_names, decls,
            );
            let terms = match scope {
                Ok(scope) => {
                    parse_solver_transaction_scoped(ctx, input, "Z3_parse_smtlib2_string", &scope)
                        .map(|content| content.assertions)
                        .unwrap_or_default()
                }
                Err(message) => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_parse_smtlib2_string: {message}"));
                    Vec::new()
                }
            };
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
            // SAFETY: `s` was null-checked above.
            parse_into_solver_handle(ctx, s, text, "Z3_solver_from_string");
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
            // SAFETY: see the string variant.
            parse_into_solver_handle(ctx, s, &text, "Z3_solver_from_file");
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
    // SAFETY: `target` is live by caller contract; `ffi_guard_ptr` handles a
    // null pointer defensively before granting mutable context access.
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
    // The handle's own parameters for this query only, a cleared interrupt,
    // and no definition the query adopted left installed afterwards (it
    // rewrote later terms of every handle: `f(x) == 0` built after
    // `consequences` arrived as `0 == x + 1`; libz3 5.1.0 keeps `f(x) == 0`
    // and answers `sat`).
    // SAFETY: `s` is null or a live solver handle of `c`; `c` is null or a
    // live context, borrowed by each call in turn.
    let settings = unsafe {
        begin_handle_query(
            c,
            s.as_ref()
                .map_or_else(ParamSet::default, |handle| handle.params),
        )
    };
    // SAFETY: `ffi_guard_int` validates/guards `c`; `s`/`consequences` are
    // null-checked before use.
    let verdict = unsafe {
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
            // libz3 5.1.0 answers `unknown` with no consequence for a goal
            // holding a loose bound variable; a lossy binder is undecided too.
            let mut goal_roots = goal.clone();
            goal_roots.extend(base_original.iter().copied());
            if has_loose_bound_variable(ctx, &goal_roots)
                || lossy_binder_refusal(ctx, &goal_roots).is_some()
            {
                return Z3_L_UNDEF;
            }
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
            if let Err(e) = ctx.reset_engine_for_solver_goal() {
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
            let mut wf_roots = finite_set_roots.clone();
            wf_roots.extend(goal.iter().chain(&base).chain(&vars_probe).copied());
            wf_roots.extend(ctx.global_definition_axioms.iter().copied());
            if let Err(e) = assert_reachable_wf_guards(ctx, &wf_roots) {
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
    };
    // SAFETY: the guarded query has returned, so no borrow of `c` remains;
    // `c` is null or the caller's live context.
    unsafe { finish_handle_query(c, settings, "Z3_solver_get_consequences") };
    verdict
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
    // SAFETY: `c` is live by caller contract; `ffi_guard_const_ptr` checks for
    // null before the closure accesses context-owned string storage.
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
    // SAFETY: `c` is live by caller contract; `ffi_guard_ast` handles a null
    // pointer defensively before resetting context state. `a` is an opaque
    // integer handle and is not dereferenced by this singleton operation.
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
    // SAFETY: `c` is live by caller contract; `ffi_guard_ast` handles a null
    // pointer defensively before resetting context state. `a` is an opaque
    // integer handle and is not dereferenced by this singleton operation.
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
                let name = super::finite_field::format_public_term_in_context(self.ctx, *t)
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
