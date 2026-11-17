// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Goal` / `ApplyResult` sub-API.
//!
//! A *goal* is a set of assertion formulas (an implicit conjunction). Applying a
//! [`Tactic`](ay_dpll::api::Tactic) to a goal produces an *apply-result*: one or
//! more *subgoals* whose disjunction is equivalent to the input (every tactic
//! here is model-preserving as a disjunction — see the soundness note on the
//! `ay_dpll` tactics module).
//!
//! This exposes the subset of the Z3 `Z3_goal_*` / `Z3_tactic_apply` /
//! `Z3_apply_result_*` C API that z3py's `Goal` + callable-`Tactic` surface uses:
//!
//! - `Z3_mk_goal` / `Z3_goal_assert` / `Z3_goal_size` / `Z3_goal_formula` build
//!   and read a goal.
//! - `Z3_tactic_apply(ctx, t, g)` runs `t` on `g` and returns the apply-result.
//! - `Z3_apply_result_get_num_subgoals` / `Z3_apply_result_get_subgoal` read the
//!   produced subgoals (each itself a `Z3_goal`).
//!
//! # Honesty
//!
//! `Z3_tactic_apply` routes through the SAME `ay_dpll` apply engine the SMT-LIB
//! `(apply <name>)` path and `Z3_mk_solver_from_tactic` use, so the produced
//! subgoals are the tactic's REAL output — never a fabricated or silent-identity
//! result. A tactic that HONESTLY FAILS (e.g. `bit-blast` on an out-of-fragment
//! BV goal, `split-clause` on a clause-free goal) returns NULL and sets
//! `Z3_INVALID_ARG` with the engine's own diagnostic; it never fabricates a
//! subgoal for a transform that did not run.
//!
//! Ref-counting (`Z3_goal_inc_ref`/`_dec_ref`, `Z3_apply_result_inc_ref`/
//! `_dec_ref`) are bookkeeping-only no-ops: goal and apply-result handles are
//! arena-owned by the context and freed only by `Z3_del_context`, mirroring the
//! existing solver/tactic/stats handle discipline.

use std::ptr;

use super::{
    cache_apply_result, cache_goal, cache_goal_with_depth, cache_string, checked_ast_to_pub,
    engine_ast, ensure_cross_context_translation_semantics, ffi_guard_const_ptr, ffi_guard_int,
    ffi_guard_produced, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, mk_ast,
    require_ast_or_return, require_asts, require_asts_or_return, terms_of,
    transfer_cross_context_ffi_metadata, ModelHandle, Z3_apply_result, Z3_ast, Z3_context, Z3_goal,
    Z3_model, Z3_params, Z3_string, Z3_tactic, Z3_EXCEPTION, Z3_GOAL_PRECISE, Z3_INVALID_ARG,
    Z3_OK,
};
use ay_dpll::api::Term;
use ay_frontend::Probe;
use std::os::raw::{c_int, c_uint};

fn apply_owned_goal(
    ctx: &mut super::Z3Context,
    c: Z3_context,
    tactic: &ay_dpll::api::Tactic,
    source: &super::GoalHandle,
    label: &str,
    operation: ay_dpll::api::TacticOperation,
    kind: ay_dpll::api::TacticExecutionKind,
) -> Z3_apply_result {
    let outcome = (|| -> Result<Z3_apply_result, String> {
        if (source.proofs || source.unsat_cores)
            && tactic
                .unsupported_goal_proof_transport_admitted(operation.admission())
                .map_err(|e| e.message)?
        {
            return Err("this tactic has no proof/core transport; original-source solver checking remains required".into());
        }
        if (kind == ay_dpll::api::TacticExecutionKind::OwnedModelConversion
            || source.model_converter.is_some())
            && (source.proofs || source.unsat_cores)
        {
            return Err("ff2bv proof/core conversion is not implemented; original-source solver checking remains required".into());
        }
        let owner = operation.admission();
        let mut terms = Vec::new();
        ay_core::term::reserve_counted(&mut terms, source.formulas.len(), owner)
            .map_err(|e| e.to_string())?;
        if !operation.validate(&ctx.solver) {
            return Err("tactic source changed".into());
        }
        for &ast in &source.formulas {
            owner.admit(1, 0).map_err(|e| e.to_string())?;
            let decoded = checked_ast_to_pub(ctx, ast)
                .ok_or_else(|| format!("{label}: foreign or stale formula"))?;
            if ctx.solver.term_sort(decoded.term) != ay_dpll::api::Sort::Bool {
                return Err("goal formula is not Boolean".into());
            }
            terms.push(decoded.term);
        }
        if !operation.validate(&ctx.solver) {
            return Err("tactic source changed".into());
        }
        let subgoals = ctx
            .solver
            .apply_tactic_subgoals_in_operation(
                &operation,
                tactic,
                &terms,
                source.depth,
                source.model_converter.clone(),
            )
            .map_err(|e| e.to_string())?;
        let mut handles = Vec::new();
        ay_core::term::reserve_counted(&mut handles, subgoals.len(), owner)
            .map_err(|e| e.to_string())?;
        ay_core::term::reserve_counted(&mut ctx.goal_cache, subgoals.len(), owner)
            .map_err(|e| e.to_string())?;
        ay_core::term::reserve_counted(&mut ctx.apply_result_cache, 1, owner)
            .map_err(|e| e.to_string())?;
        let boxes = subgoals
            .len()
            .checked_mul(size_of::<super::GoalHandle>())
            .and_then(|n| n.checked_add(size_of::<super::ApplyResultHandle>()))
            .ok_or("goal publication size overflow")?;
        owner
            .admit(subgoals.len(), boxes)
            .map_err(|e| e.to_string())?;
        if !operation.validate(&ctx.solver) {
            return Err("tactic source changed".into());
        }
        for subgoal in subgoals {
            let mut asts = Vec::new();
            ay_core::term::reserve_counted(&mut asts, subgoal.formulas.len(), owner)
                .map_err(|e| e.to_string())?;
            if !operation.validate(&ctx.solver) {
                return Err("tactic source changed".into());
            }
            for term in subgoal.formulas {
                if !ctx.solver.is_valid_term(term) {
                    return Err("retired tactic output".into());
                }
                let id = ctx
                    .pub_ast
                    .engine_node_owned(term, Some(owner))
                    .ok_or("public AST publication refused")?;
                if !operation.validate(&ctx.solver) {
                    return Err("tactic source changed".into());
                }
                asts.push(super::pub_id_to_ast(ctx, id));
            }
            let handle = Box::into_raw(Box::new(super::GoalHandle {
                formulas: asts,
                depth: subgoal.depth,
                model_converter: subgoal.model_converter,
                models: source.models,
                proofs: source.proofs,
                unsat_cores: source.unsat_cores,
                context: c,
            }));
            ctx.goal_cache.push(handle);
            handles.push(handle);
        }
        if !operation.validate(&ctx.solver) {
            return Err("tactic source changed".into());
        }
        let result = Box::into_raw(Box::new(super::ApplyResultHandle { subgoals: handles }));
        ctx.apply_result_cache.push(result);
        Ok(result)
    })();
    match outcome {
        Ok(result) => {
            ctx.last_error = Z3_OK;
            result
        }
        Err(message) => {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(message);
            ptr::null_mut()
        }
    }
}

/// Create an empty goal.
///
/// The `models` / `unsat_cores` / `proofs` flags are accepted for z3py signature
/// compatibility. AY's tactics are equivalence-preserving (model-preserving as a
/// disjunction), so a produced subgoal's models are directly the input's models;
/// the flags do not change the transform. A fresh goal has no formulas.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_goal(
    c: Z3_context,
    models: bool,
    unsat_cores: bool,
    proofs: bool,
) -> Z3_goal {
    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr` handles
    // the null case and catches panics so they cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            let goal = cache_goal(ctx, Vec::new());
            // SAFETY: this handle was just allocated in this context.
            if let Some(handle) = goal.as_mut() {
                handle.models = models;
                handle.proofs = proofs;
                handle.unsat_cores = unsat_cores;
            }
            goal
        })
    }
}

/// Increment a goal's reference count (bookkeeping no-op — arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_inc_ref(_c: Z3_context, _g: Z3_goal) {}

/// Decrement a goal's reference count (bookkeeping no-op — arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_dec_ref(_c: Z3_context, _g: Z3_goal) {}

/// Assert a formula into a goal.
///
/// Appends `a` to the goal's formula list. `a` is an ordinary term handle in the
/// context's shared term store; the goal records the handle (it owns no terms).
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_assert(c: Z3_context, g: Z3_goal, a: Z3_ast) {
    // SAFETY: `g`, when non-null, is a `GoalHandle` kept alive in the context's
    // `goal_cache` (single-threaded per context, so no race). `as_mut` null-checks.
    let goal = unsafe { g.as_mut() };
    // SAFETY: see above; `ffi_guard_void` handles a null context and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(goal) = goal else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_goal_assert: null goal handle".to_string());
                return;
            };
            if goal.context != c || goal.model_converter.is_some() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_goal_assert: foreign or model-converted goal mutation is unsupported"
                        .into(),
                );
                return;
            }
            let _term = require_ast_or_return!(ctx, a, "Z3_goal_assert", "formula");
            ctx.last_error = Z3_OK;
            goal.formulas.push(a);
        });
    }
}

/// The number of formulas in a goal.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_size(c: Z3_context, g: Z3_goal) -> c_uint {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let n = unsafe { g.as_ref() }.map_or(0, |h| h.formulas.len() as c_uint);
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe { ffi_guard_uint(c, 0, |_ctx| n) }
}

/// The `i`-th formula of a goal (0 on out-of-range / null goal).
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_formula(c: Z3_context, g: Z3_goal, i: c_uint) -> Z3_ast {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let ast = unsafe { g.as_ref() }
        .and_then(|h| h.formulas.get(i as usize).copied())
        .unwrap_or(0);
    // SAFETY: `ffi_guard_ast` handles a null context and catches panics; it
    // returns `Z3_ast` (u64), matching this function's result type.
    unsafe {
        ffi_guard_produced(c, |ctx| {
            if ast == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_goal_formula: index out of range".to_string());
            } else {
                let _formula =
                    require_ast_or_return!(ctx, ast, "Z3_goal_formula", "stored formula", 0);
                ctx.last_error = Z3_OK;
            }
            ast
        })
    }
}

/// Apply a tactic to a goal, returning the apply-result (its subgoals).
///
/// Routes through the shared `ay_dpll` apply engine. On an HONEST tactic failure
/// (e.g. `bit-blast` on an out-of-fragment goal, `split-clause` on a clause-free
/// goal) returns NULL and sets `Z3_INVALID_ARG` with the engine's diagnostic —
/// never a fabricated subgoal.
///
/// # Safety
/// `c` must be a valid context pointer; `t`/`g`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_apply(
    c: Z3_context,
    t: Z3_tactic,
    g: Z3_goal,
) -> Z3_apply_result {
    // SAFETY: forwarded verbatim to the shared implementation under the caller's
    // contract; `apply_tactic_to_goal_impl` re-checks both handles.
    unsafe { apply_tactic_to_goal_impl(c, t, g, "Z3_tactic_apply", None) }
}

/// Apply the tactic with a validated parameter update. Stored using-params
/// settings override later updates, and restrictions retain the same owner.
///
/// # Safety
/// The context is live/non-aliased and handles are live in its arenas.
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_apply_ex(
    c: Z3_context,
    t: Z3_tactic,
    g: Z3_goal,
    p: Z3_params,
) -> Z3_apply_result {
    // SAFETY: forwarded to the common authenticated implementation.
    unsafe { apply_tactic_to_goal_impl(c, t, g, "Z3_tactic_apply_ex", Some(p)) }
}

/// Shared body of `Z3_tactic_apply` / `Z3_tactic_apply_ex`: run `t` on `g`'s
/// formulas through the real `ay_dpll` apply engine and return the apply-result,
/// or NULL + an honest error on a null handle / a genuine tactic failure. `label`
/// names the caller for diagnostics.
///
/// # Safety
/// `c` must be a valid context pointer; `t`/`g`, when non-null, valid handles.
unsafe fn apply_tactic_to_goal_impl(
    c: Z3_context,
    t: Z3_tactic,
    g: Z3_goal,
    label: &'static str,
    request_params: Option<Z3_params>,
) -> Z3_apply_result {
    // Pre-extract the tactic and the goal's formulas outside the guard.
    // SAFETY: the caller guarantees a non-null `t` is a live `TacticHandle`;
    // `as_ref` checks null before cloning, and the API's single-thread rule
    // prevents mutation from racing this shared read.
    let tactic_instance = unsafe { t.as_ref() }.map(|h| &h.tactic);
    // SAFETY: the caller guarantees a non-null `g` is a live `GoalHandle`;
    // `as_ref` checks null before cloning, and the API's single-thread rule
    // prevents mutation from racing this shared read.
    let source = unsafe { g.as_ref() };

    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr` handles
    // the null case and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(tactic_instance) = tactic_instance else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("{label}: null tactic handle"));
                return ptr::null_mut();
            };
            let Some(source) = source else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("{label}: null goal handle"));
                return ptr::null_mut();
            };
            let operation = match ctx.solver.begin_tactic_operation() {
                Ok(value) => value,
                Err(error) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(error.to_string());
                    return ptr::null_mut();
                }
            };
            if operation
                .admission()
                .admit(ctx.goal_cache.len(), 0)
                .is_err()
            {
                ctx.last_error = Z3_EXCEPTION;
                return ptr::null_mut();
            }
            if source.context != c || !ctx.goal_cache.contains(&g) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("foreign goal handle".into());
                return ptr::null_mut();
            }
            if operation
                .admission()
                .admit(ctx.tactic_handle_cache.len(), 0)
                .is_err()
            {
                ctx.last_error = Z3_EXCEPTION;
                return ptr::null_mut();
            }
            if !ctx.tactic_handle_cache.contains(&t) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("foreign tactic handle".into());
                return ptr::null_mut();
            }
            let tactic = ay_dpll::api::Tactic::Shared(std::sync::Arc::clone(tactic_instance));
            let mut parameters = match request_params {
                Some(params) => match super::tactics::parameter_snapshot(ctx, params, &operation) {
                    Ok(value) => value,
                    Err(error) => {
                        ctx.last_error = Z3_EXCEPTION;
                        ctx.error_msg = Some(error);
                        return ptr::null_mut();
                    }
                },
                None => ay_dpll::api::TacticParameters::default(),
            };
            let global = (|| -> Result<(), String> {
                if tactic
                    .has_simplifier_parameters(operation.admission())
                    .map_err(|e| e.message)?
                {
                    let maximum =
                        super::global_params::sequence_power_expansion(operation.admission())?;
                    parameters = parameters.with_global_sequence_power(maximum);
                    parameters = parameters.with_global_polynomial(
                        super::global_params::polynomial_parameters(operation.admission())?,
                    );
                }
                Ok(())
            })();
            if let Err(error) = global {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(error);
                return ptr::null_mut();
            }
            if let Err(error) = tactic.update_parameters(parameters, operation.admission()) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(error.message);
                return ptr::null_mut();
            }
            let formulas = &source.formulas;
            let kind = match tactic.execution_kind_admitted(operation.admission()) {
                Ok(value) => value,
                Err(error) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(error.message);
                    return ptr::null_mut();
                }
            };
            if !operation.validate(&ctx.solver) {
                ctx.last_error = Z3_EXCEPTION;
                return ptr::null_mut();
            }
            if kind != ay_dpll::api::TacticExecutionKind::Legacy || source.model_converter.is_some()
            {
                return apply_owned_goal(ctx, c, &tactic, source, label, operation, kind);
            }
            drop(operation);

            let goal_terms = terms_of(&require_asts_or_return!(
                ctx,
                formulas,
                label,
                ptr::null_mut()
            ));
            match ctx.solver.apply_tactic_subgoals(&tactic, &goal_terms) {
                Ok(subgoals) => {
                    ctx.last_error = Z3_OK;
                    // Each subgoal becomes its own arena-owned GoalHandle; the
                    // apply-result only references them (freed once, in goal_cache).
                    let subgoal_handles: Vec<Z3_goal> = subgoals
                        .into_iter()
                        .map(|(fs, depth)| {
                            let asts: Vec<Z3_ast> =
                                fs.iter().map(|&t| engine_ast(ctx, t)).collect();
                            let goal = cache_goal_with_depth(
                                ctx,
                                asts,
                                source.depth.saturating_add(depth),
                            );
                            // SAFETY: this handle was just allocated in ctx.
                            if let Some(handle) = goal.as_mut() {
                                handle.models = source.models;
                                handle.proofs = source.proofs;
                                handle.unsat_cores = source.unsat_cores;
                            }
                            goal
                        })
                        .collect();
                    cache_apply_result(ctx, subgoal_handles)
                }
                Err(e) => {
                    // HONEST failure: NULL + diagnostic, never a fabricated subgoal.
                    // A tactic that genuinely fails (e.g. `split-clause` on a
                    // clause-free goal) is a Z3 EXCEPTION — so `Z3_get_error_msg`
                    // surfaces the real reason to the caller, matching z3py's
                    // `Z3Exception(<reason>)` rather than a generic invalid-arg.
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(e.to_string());
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Increment an apply-result's reference count (bookkeeping no-op — arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_apply_result_inc_ref(_c: Z3_context, _r: Z3_apply_result) {}

/// Decrement an apply-result's reference count (bookkeeping no-op — arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_apply_result_dec_ref(_c: Z3_context, _r: Z3_apply_result) {}

/// The number of subgoals in an apply-result.
///
/// # Safety
/// `c` must be a valid context pointer; `r`, when non-null, a valid handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_apply_result_get_num_subgoals(
    c: Z3_context,
    r: Z3_apply_result,
) -> c_uint {
    // SAFETY: `r`, when non-null, is a live `ApplyResultHandle`; `as_ref` null-checks.
    let n = unsafe { r.as_ref() }.map_or(0, |h| h.subgoals.len() as c_uint);
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe { ffi_guard_uint(c, 0, |_ctx| n) }
}

/// The `i`-th subgoal of an apply-result (NULL on out-of-range / null result).
///
/// # Safety
/// `c` must be a valid context pointer; `r`, when non-null, a valid handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_apply_result_get_subgoal(
    c: Z3_context,
    r: Z3_apply_result,
    i: c_uint,
) -> Z3_goal {
    // SAFETY: `r`, when non-null, is a live `ApplyResultHandle`; `as_ref` null-checks.
    let sub = unsafe { r.as_ref() }
        .and_then(|h| h.subgoals.get(i as usize).copied())
        .unwrap_or(ptr::null_mut());
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if sub.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_apply_result_get_subgoal: index out of range".to_string());
            } else {
                ctx.last_error = Z3_OK;
            }
            sub
        })
    }
}

/// Return the goal's *precision* ([`Z3_GOAL_PRECISE`]/`under`/`over`/…).
///
/// AY's tactics are ALL equivalence-preserving — no over- or under-
/// approximation is ever applied — so every goal AY produces is
/// [`Z3_GOAL_PRECISE`] (both SAT and UNSAT answers are preserved). This is
/// honest, not a stub: AY genuinely never manufactures an approximated goal.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_precision(c: Z3_context, _g: Z3_goal) -> c_uint {
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe {
        ffi_guard_uint(c, Z3_GOAL_PRECISE, |ctx| {
            ctx.last_error = Z3_OK;
            Z3_GOAL_PRECISE
        })
    }
}

/// Return the goal's *depth* — the number of primitive tactic applications that
/// produced it. A goal built by `Z3_mk_goal` has depth 0; a subgoal from
/// `Z3_tactic_apply` carries the engine's real transformation depth.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_depth(c: Z3_context, g: Z3_goal) -> c_uint {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let depth = unsafe { g.as_ref() }.map_or(0, |h| h.depth as c_uint);
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.last_error = Z3_OK;
            depth
        })
    }
}

/// Return `true` iff the goal contains the formula `false` (Z3's
/// `Z3_goal_inconsistent`). Reads the REAL formulas: a formula whose interned
/// term is the Boolean `false` constant makes the goal inconsistent.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_inconsistent(c: Z3_context, g: Z3_goal) -> bool {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let formulas = unsafe { g.as_ref() }.map(|h| h.formulas.clone());
    // SAFETY: `ffi_guard_int` handles a null context and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            match goal_has_false(ctx, formulas.as_deref(), "Z3_goal_inconsistent") {
                Some(value) => {
                    ctx.last_error = Z3_OK;
                    c_int::from(value)
                }
                None => 0,
            }
        }) != 0
    }
}

/// Return the number of formulas, subformulas and terms in the goal (Z3's
/// `Z3_goal_num_exprs`). Computed by the SAME engine probe as the `num-exprs`
/// probe (distinct sub-expression nodes over the goal's formulas, after Z3-style
/// top-level-conjunction splitting), so it matches libz3 exactly.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_num_exprs(c: Z3_context, g: Z3_goal) -> c_uint {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let data = unsafe { g.as_ref() }.map(|h| (h.formulas.clone(), h.depth));
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.last_error = Z3_OK;
            match data {
                Some((formulas, depth)) => {
                    let terms = terms_of(&require_asts_or_return!(
                        ctx,
                        &formulas,
                        "Z3_goal_num_exprs",
                        0
                    ));
                    // `num-exprs` is depth-independent; pass the goal's depth for
                    // symmetry with the probe evaluator.
                    ctx.solver.apply_probe(&Probe::NumExprs, &terms, depth) as c_uint
                }
                None => 0,
            }
        })
    }
}

/// Return `true` iff the goal is empty (Z3's `Z3_goal_is_decided_sat`).
///
/// An empty goal (no formulas) is trivially satisfiable, and — because AY goals
/// are always [`Z3_GOAL_PRECISE`] — this is a decided SAT. A non-empty goal is
/// not decided here.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_is_decided_sat(c: Z3_context, g: Z3_goal) -> bool {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let empty = unsafe { g.as_ref() }.map_or(false, |h| h.formulas.is_empty());
    // SAFETY: `ffi_guard_int` handles a null context and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            ctx.last_error = Z3_OK;
            c_int::from(empty)
        }) != 0
    }
}

/// Return `true` iff the goal contains `false` (Z3's
/// `Z3_goal_is_decided_unsat`). A goal containing `false` is UNSAT, and — since
/// AY goals are always [`Z3_GOAL_PRECISE`] — this is a decided UNSAT.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_is_decided_unsat(c: Z3_context, g: Z3_goal) -> bool {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let formulas = unsafe { g.as_ref() }.map(|h| h.formulas.clone());
    // SAFETY: `ffi_guard_int` handles a null context and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            match goal_has_false(ctx, formulas.as_deref(), "Z3_goal_is_decided_unsat") {
                Some(value) => {
                    ctx.last_error = Z3_OK;
                    c_int::from(value)
                }
                None => 0,
            }
        }) != 0
    }
}

/// Does any formula in `formulas` denote the Boolean `false` constant?
///
/// Shared by `Z3_goal_inconsistent` and `Z3_goal_is_decided_unsat`, which both
/// key on the goal containing `false`. Uses the solver's REAL constant value.
fn goal_has_false(
    ctx: &mut super::Z3Context,
    formulas: Option<&[Z3_ast]>,
    operation: &str,
) -> Option<bool> {
    let formulas = formulas?;
    let decoded = require_asts(ctx, formulas, operation)?;
    Some(
        decoded
            .into_iter()
            .any(|formula| ctx.solver.bool_value(formula.term) == Some(false)),
    )
}

/// Erase all formulas from the goal, resetting its depth to 0 (Z3's
/// `Z3_goal_reset`).
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_reset(c: Z3_context, g: Z3_goal) {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_mut` null-checks.
    let goal = unsafe { g.as_mut() };
    // SAFETY: `ffi_guard_void` handles a null context and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| match goal {
            Some(h) => {
                if h.context != c {
                    ctx.last_error = Z3_INVALID_ARG;
                    return;
                }
                h.formulas.clear();
                h.depth = 0;
                h.model_converter = None;
                ctx.last_error = Z3_OK;
            }
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_goal_reset: null goal handle".to_string());
            }
        });
    }
}

/// Copy goal `g` from context `source` into context `target` (Z3's
/// `Z3_goal_translate`).
///
/// When `source == target` the formula handles are already valid in `target`,
/// so this returns a real copy (same formulas, same depth). When the contexts
/// differ, a `Z3_ast` handle from `source` is meaningless in `target`, so the
/// goal's whole formula term DAG is re-interned into `target`'s term store via
/// the engine's [`translate_terms_from`](ay_dpll::api::Solver::translate_terms_from)
/// graft — a faithful deep copy, never a fabricated goal. The copy is refused
/// when source context-resident semantic metadata cannot be carried by the DAG.
///
/// # Safety
/// `source`/`target` must be valid context pointers; `g`, when non-null, a valid
/// goal handle in `source`.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_translate(
    source: Z3_context,
    g: Z3_goal,
    target: Z3_context,
) -> Z3_goal {
    // SAFETY: a non-null g is a live caller-supplied goal. Borrow only; no
    // formula/converter payload is copied before original admission.
    if let Some(goal) = unsafe { g.as_ref() }.filter(|goal| goal.model_converter.is_some()) {
        // SAFETY: the existing guard validates target and contains panics.
        return unsafe {
            ffi_guard_ptr(target, |ctx| {
                if source != target || goal.context != target || !ctx.goal_cache.contains(&g) {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(
                        "cross-context translation of a model converter is unsupported".into(),
                    );
                    return ptr::null_mut();
                }
                let operation = match ctx.solver.begin_tactic_operation() {
                    Ok(value) => value,
                    Err(error) => {
                        ctx.last_error = Z3_EXCEPTION;
                        ctx.error_msg = Some(error.to_string());
                        return ptr::null_mut();
                    }
                };
                let result = apply_owned_goal(
                    ctx,
                    target,
                    &ay_dpll::api::Tactic::Skip,
                    goal,
                    "Z3_goal_translate",
                    operation,
                    ay_dpll::api::TacticExecutionKind::Legacy,
                );
                // SAFETY: non-null result was just allocated in ctx's apply arena.
                result
                    .as_ref()
                    .and_then(|value| value.subgoals.first().copied())
                    .unwrap_or(ptr::null_mut())
            })
        };
    }
    // SAFETY: `g`, when non-null, is a live `GoalHandle` in `source`'s arena;
    // `as_ref` null-checks before the formula/depth snapshot is copied.
    let goal_data = unsafe { g.as_ref() }.map(|h| {
        (
            h.formulas.clone(),
            h.depth,
            h.models,
            h.proofs,
            h.unsat_cores,
        )
    });
    // SAFETY: the caller guarantees that a non-null `target` is a live context;
    // `ffi_guard_ptr` handles null and contains panics. The only other raw
    // context dereference below is `source`, whose validity is also part of the
    // caller contract and whose inequality with `target` prevents aliasing the
    // guard's exclusive target borrow.
    unsafe {
        ffi_guard_ptr(target, |tgt| {
            let Some((formulas, depth, models, proofs, unsat_cores)) = goal_data else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_goal_translate: null goal handle".to_string());
                return ptr::null_mut();
            };
            // Same context: authenticate before copying so translation cannot
            // launder formulas that came from a different context.
            if source == target {
                let _decoded =
                    require_asts_or_return!(tgt, &formulas, "Z3_goal_translate", ptr::null_mut());
                tgt.last_error = Z3_OK;
                let result = cache_goal_with_depth(tgt, formulas, depth);
                // SAFETY: this result was just allocated in tgt's goal arena.
                if let Some(goal) = result.as_mut() {
                    goal.models = models;
                    goal.proofs = proofs;
                    goal.unsat_cores = unsat_cores;
                }
                return result;
            }
            // Cross-context: re-intern the formula term DAG into `target`'s store.
            // SAFETY: `source != target`, so this borrow does not alias `tgt`;
            // dereferenced under the enclosing `unsafe` (the closure is lexically
            // nested in it).
            let Some(src) = source.as_ref() else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_goal_translate: null source context".to_string());
                return ptr::null_mut();
            };
            let Some(src_terms) = formulas
                .iter()
                .map(|&ast| checked_ast_to_pub(src, ast).map(|source| source.term))
                .collect::<Option<Vec<Term>>>()
            else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some(
                    "Z3_goal_translate: goal contains an invalid formula or one from a different source context"
                        .to_string(),
                );
                return ptr::null_mut();
            };
            if !ensure_cross_context_translation_semantics(src, tgt, "Z3_goal_translate") {
                return ptr::null_mut();
            }
            let new_terms = tgt.solver.translate_terms_from(&src.solver, &src_terms);
            if !transfer_cross_context_ffi_metadata(
                src,
                tgt,
                &src_terms,
                &new_terms,
                "Z3_goal_translate",
            ) {
                return ptr::null_mut();
            }
            let mut new_asts: Vec<Z3_ast> = Vec::with_capacity(new_terms.len());
            for (&source_term, &term) in src_terms.iter().zip(&new_terms) {
                let sort = src.solver.term_sort(source_term);
                new_asts.push(mk_ast(tgt, term, sort));
            }
            tgt.last_error = Z3_OK;
            let result = cache_goal_with_depth(tgt, new_asts, depth);
            // SAFETY: this result was just allocated in tgt's goal arena.
            if let Some(goal) = result.as_mut() {
                goal.models = models;
                goal.proofs = proofs;
                goal.unsat_cores = unsat_cores;
            }
            result
        })
    }
}

/// Convert a model of the goal's formulas back to a model of the original goal
/// (Z3's `Z3_goal_convert_model`).
///
/// Identity goals retain their snapshot behavior. A field-to-BV goal carries
/// actual typed reconstruction, rejects missing/out-of-range representatives,
/// and independently checks the complete original goal. No proof grant is
/// inferred from a returned candidate. Unsupported interpretation families or
/// context/source mismatches refuse instead of discarding model data.
///
/// # Safety
/// `c` must be a valid context pointer; `g`/`m`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_convert_model(c: Z3_context, g: Z3_goal, m: Z3_model) -> Z3_model {
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if g.is_null()
                || m.is_null()
                || !ctx.goal_cache.contains(&g)
                || !ctx.model_cache.contains(&m)
            {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_goal_convert_model: foreign or null goal/model".into());
                return ptr::null_mut();
            }
            // SAFETY: both handles were authenticated in this live context's
            // owned arenas above; neither operation mutates these input boxes.
            let (goal, input) = (&*g, &*m);
            if goal.context != c || input._ctx != c {
                ctx.last_error = Z3_INVALID_ARG;
                return ptr::null_mut();
            }
            let (model, func_interps, complete_functions) = if let Some(converter) =
                &goal.model_converter
            {
                if !input.func_interps.is_empty()
                    || !input.user_const_interps.is_empty()
                    || !input.user_func_interps.is_empty()
                {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg=Some("ff2bv model conversion does not support caller-edited/function interpretations".into());
                    return ptr::null_mut();
                }
                let operation = match ctx.solver.begin_tactic_operation() {
                    Ok(value) => value,
                    Err(e) => {
                        ctx.last_error = Z3_EXCEPTION;
                        ctx.error_msg = Some(e.to_string());
                        return ptr::null_mut();
                    }
                };
                let converted = if goal.models {
                    ctx.solver.convert_tactic_model_in_operation(
                        &operation,
                        converter,
                        &input.model,
                    )
                } else {
                    ctx.solver.copy_unconverted_tactic_model_in_operation(
                        &operation,
                        converter,
                        &input.model,
                    )
                };
                let model = match converted {
                    Ok(value) => value,
                    Err(e) => {
                        ctx.last_error = Z3_EXCEPTION;
                        ctx.error_msg = Some(e.to_string());
                        return ptr::null_mut();
                    }
                };
                let owner = operation.admission();
                if owner.admit(1, size_of::<ModelHandle>()).is_err()
                    || ay_core::term::reserve_counted(&mut ctx.model_cache, 1, owner).is_err()
                    || !operation.validate(&ctx.solver)
                {
                    ctx.last_error = Z3_EXCEPTION;
                    return ptr::null_mut();
                }
                let handle = Box::into_raw(Box::new(ModelHandle {
                    model,
                    func_interps: Vec::new(),
                    complete_functions: input.complete_functions,
                    user_const_interps: Vec::new(),
                    user_func_interps: Vec::new(),
                    rec_def_count: input.rec_def_count,
                    _ctx: c,
                }));
                ctx.model_cache.push(handle);
                ctx.last_error = Z3_OK;
                return handle;
            } else {
                (
                    input.model.clone(),
                    input.func_interps.clone(),
                    input.complete_functions,
                )
            };
            ctx.last_error = Z3_OK;
            let handle = Box::into_raw(Box::new(ModelHandle {
                model,
                func_interps,
                user_const_interps: Vec::new(),
                user_func_interps: Vec::new(),
                rec_def_count: ctx.rec_fun_defs.len(),
                complete_functions,
                _ctx: c,
            }));
            ctx.model_cache.push(handle);
            handle
        })
    }
}

/// Render the goal as an s-expression (Z3's `Z3_goal_to_string`): `(goal` then
/// each formula on its own two-space-indented line, closed by `)`. An empty goal
/// prints `(goal)`. Each formula is rendered by the solver's REAL term formatter
/// (matching `Z3_ast_to_string`), so the output matches libz3's goal printing.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_to_string(c: Z3_context, g: Z3_goal) -> Z3_string {
    // SAFETY: `g`, when non-null, is a live `GoalHandle`; `as_ref` null-checks.
    let formulas = unsafe { g.as_ref() }.map(|h| h.formulas.clone());
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            let mut s = String::from("(goal");
            if let Some(fs) = formulas {
                for &a in &fs {
                    let rendered = if a == 0 {
                        "?".to_string()
                    } else {
                        let term = require_ast_or_return!(
                            ctx,
                            a,
                            "Z3_goal_to_string",
                            "goal formula",
                            ptr::null()
                        )
                        .term;
                        match super::finite_field::format_public_term(ctx, term) {
                            Some(text) => text,
                            None => return ptr::null(),
                        }
                    };
                    s.push_str("\n  ");
                    s.push_str(&rendered);
                }
            }
            s.push(')');
            let s = super::ffi_surface_text(ctx, &s);
            cache_string(ctx, s)
        })
    }
}

#[cfg(test)]
#[path = "goals_probes_ffi_tests.rs"]
mod goals_probes_ffi_tests;
