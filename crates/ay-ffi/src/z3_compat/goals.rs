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
    ast_to_term, cache_apply_result, cache_goal, cache_goal_with_depth, cache_string,
    ensure_cross_context_translation_semantics, ffi_guard_ast, ffi_guard_const_ptr, ffi_guard_int,
    ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, record_ast_sort, term_to_ast, ModelHandle,
    Z3_apply_result, Z3_ast, Z3_context, Z3_goal, Z3_model, Z3_params, Z3_string, Z3_tactic,
    Z3_EXCEPTION, Z3_GOAL_PRECISE, Z3_INVALID_ARG, Z3_OK,
};
use ay_dpll::api::Term;
use ay_frontend::Probe;
use std::os::raw::{c_int, c_uint};

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
    _models: bool,
    _unsat_cores: bool,
    _proofs: bool,
) -> Z3_goal {
    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr` handles
    // the null case and catches panics so they cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            cache_goal(ctx, Vec::new())
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
            if a == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_goal_assert: null formula".to_string());
                return;
            }
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
        ffi_guard_ast(c, |ctx| {
            if ast == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_goal_formula: index out of range".to_string());
            } else {
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
    unsafe { apply_tactic_to_goal_impl(c, t, g, "Z3_tactic_apply") }
}

/// Apply tactic `t` to goal `g` using the parameter set `p` (Z3's
/// `Z3_tactic_apply_ex`).
///
/// HONEST DIVERGENCE (documented): AY always applies the equivalence-preserving
/// transform, so the parameter set — which in Z3 only tunes the produced goal's
/// SHAPE, never its verdict/model set — does not change the transform. `p` is
/// therefore accepted for API compatibility and ignored; the produced subgoals
/// are the tactic's REAL output, identical to [`Z3_tactic_apply`] on the same
/// goal. It never fabricates a subgoal, and never substitutes a different,
/// possibly-unsound transform. On an HONEST tactic failure it returns NULL and
/// sets a Z3 EXCEPTION error, exactly like `Z3_tactic_apply`.
///
/// # Safety
/// `c` must be a valid context pointer; `t`/`g`, when non-null, valid handles;
/// `p`, when non-null, a valid params handle (unused).
#[no_mangle]
pub unsafe extern "C" fn Z3_tactic_apply_ex(
    c: Z3_context,
    t: Z3_tactic,
    g: Z3_goal,
    _p: Z3_params,
) -> Z3_apply_result {
    // SAFETY: forwarded to the shared implementation; `p` is honestly ignored
    // (see the doc note above).
    unsafe { apply_tactic_to_goal_impl(c, t, g, "Z3_tactic_apply_ex") }
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
) -> Z3_apply_result {
    // Pre-extract the tactic and the goal's formulas outside the guard
    // (raw-pointer derefs). SAFETY: both handles, when non-null, are arena-owned
    // by the context and single-threaded per context; `as_ref` null-checks.
    let tactic = unsafe { t.as_ref() }.map(|h| h.tactic.clone());
    let formulas: Option<Vec<Z3_ast>> = unsafe { g.as_ref() }.map(|h| h.formulas.clone());

    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr` handles
    // the null case and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(tactic) = tactic else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("{label}: null tactic handle"));
                return ptr::null_mut();
            };
            let Some(formulas) = formulas else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("{label}: null goal handle"));
                return ptr::null_mut();
            };

            let goal_terms: Vec<Term> = formulas.iter().map(|&a| ast_to_term(a)).collect();
            match ctx.solver.apply_tactic_subgoals(&tactic, &goal_terms) {
                Ok(subgoals) => {
                    ctx.last_error = Z3_OK;
                    // Each subgoal becomes its own arena-owned GoalHandle; the
                    // apply-result only references them (freed once, in goal_cache).
                    let subgoal_handles: Vec<Z3_goal> = subgoals
                        .into_iter()
                        .map(|(fs, depth)| {
                            let asts: Vec<Z3_ast> = fs.iter().map(|&t| term_to_ast(t)).collect();
                            cache_goal_with_depth(ctx, asts, depth)
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
            ctx.last_error = Z3_OK;
            c_int::from(goal_has_false(ctx, formulas.as_deref()))
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
                    let terms: Vec<Term> = formulas.iter().map(|&a| ast_to_term(a)).collect();
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
            ctx.last_error = Z3_OK;
            c_int::from(goal_has_false(ctx, formulas.as_deref()))
        }) != 0
    }
}

/// Does any formula in `formulas` denote the Boolean `false` constant?
///
/// Shared by `Z3_goal_inconsistent` and `Z3_goal_is_decided_unsat`, which both
/// key on the goal containing `false`. Uses the solver's REAL constant value.
fn goal_has_false(ctx: &super::Z3Context, formulas: Option<&[Z3_ast]>) -> bool {
    formulas.is_some_and(|fs| {
        fs.iter()
            .any(|&a| a != 0 && ctx.solver.bool_value(ast_to_term(a)) == Some(false))
    })
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
                h.formulas.clear();
                h.depth = 0;
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
    // Pre-extract the source goal's formulas + depth (raw deref; the goal lives
    // in `source`'s arena). SAFETY: `g`, when non-null, is a live `GoalHandle`.
    let goal_data = unsafe { g.as_ref() }.map(|h| (h.formulas.clone(), h.depth));
    // SAFETY: `target` is the destination context; `ffi_guard_ptr` handles a null
    // context and catches panics.
    unsafe {
        ffi_guard_ptr(target, |tgt| {
            let Some((formulas, depth)) = goal_data else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_goal_translate: null goal handle".to_string());
                return ptr::null_mut();
            };
            // Same context: the handles are already valid here — copy directly.
            if source == target {
                tgt.last_error = Z3_OK;
                return cache_goal_with_depth(tgt, formulas, depth);
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
            if !ensure_cross_context_translation_semantics(src, tgt, "Z3_goal_translate") {
                return ptr::null_mut();
            }
            let src_terms: Vec<Term> = formulas.iter().map(|&a| ast_to_term(a)).collect();
            let new_terms = tgt.solver.translate_terms_from(&src.solver, &src_terms);
            let new_asts: Vec<Z3_ast> = new_terms.iter().map(|&t| term_to_ast(t)).collect();
            for (&term, &ast) in new_terms.iter().zip(&new_asts) {
                let sort = tgt.solver.term_sort(term);
                record_ast_sort(tgt, ast, sort);
            }
            tgt.last_error = Z3_OK;
            cache_goal_with_depth(tgt, new_asts, depth)
        })
    }
}

/// Convert a model of the goal's formulas back to a model of the original goal
/// (Z3's `Z3_goal_convert_model`).
///
/// A goal built by `Z3_mk_goal`/`Z3_goal_assert` (and any AY-transformed goal,
/// since AY's tactics are equivalence-preserving) carries the IDENTITY model
/// converter: a model of its formulas is already a model of the goal. This
/// therefore returns a real snapshot copy of `m` — never a fabricated model. A
/// null `m` has nothing to convert and yields null (honest: AY does not
/// manufacture a witness the caller never supplied).
///
/// # Safety
/// `c` must be a valid context pointer; `g`/`m`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_convert_model(
    c: Z3_context,
    _g: Z3_goal,
    m: Z3_model,
) -> Z3_model {
    // Pre-extract a snapshot of the input model (raw deref). SAFETY: `m`, when
    // non-null, is a live `ModelHandle`; `as_ref` null-checks.
    let snapshot = unsafe { m.as_ref() }.map(|h| (h.model.clone(), h.func_interps.clone()));
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            let Some((model, func_interps)) = snapshot else {
                return ptr::null_mut();
            };
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
                        ctx.solver
                            .format_term_checked(ast_to_term(a))
                            .unwrap_or_else(|| "?".to_string())
                    };
                    s.push_str("\n  ");
                    s.push_str(&rendered);
                }
            }
            s.push(')');
            cache_string(ctx, s)
        })
    }
}

#[cfg(test)]
#[path = "goals_probes_ffi_tests.rs"]
mod goals_probes_ffi_tests;
