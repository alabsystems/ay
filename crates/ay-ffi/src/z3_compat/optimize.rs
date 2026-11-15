// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Optimize` sub-API for MaxSMT and arithmetic objectives.
//!
//! Implements the subset of the Z3 `Z3_optimize_*` C API that z3py's
//! `Optimize()` exercises:
//!
//! - **MaxSAT / weighted partial MaxSMT**: hard constraints plus weighted soft
//!   constraints (`Z3_optimize_assert_soft`), solved by AY's weight-exact engine
//!   ([`Solver::check_sat_max`](ay_dpll::api::Solver::check_sat_max)).
//! - **Arithmetic objectives** (`Z3_optimize_maximize` / `Z3_optimize_minimize`):
//!   Int / Real / BitVec objective terms driven to their extremum by AY's
//!   executor optimizer ([`Solver::optimize_check`](ay_dpll::api::Solver::optimize_check)),
//!   with the optimum read back via `Z3_optimize_get_lower` / `Z3_optimize_get_upper`.
//!
//! # Objectives vs soft constraints (mixed-use behavior — honest)
//!
//! `Z3_optimize_check` routes as follows:
//!
//! - objectives and/or soft constraints under ONE registration style → the
//!   executor's joint engine (declaration-order lex; `box` via
//!   `opt.priority`), exactly as for parsed scripts.
//! - MIXING parsed (`from_string`) softs with `Z3_optimize_assert_soft`
//!   softs → honest `Z3_L_UNDEF`/`Z3_INVALID_ARG` (no single joint
//!   representation yet); use one registration style.
//! - flat (ungrouped) API softs only → MaxSMT (`check_sat_max`).
//! - neither → plain `check_sat`.
//!
//! The remaining restriction is documented rather than faked: a wrong joint
//! optimum is never reported.
//!
//! # Handle model
//!
//! A `Z3_optimize` is a context-arena-owned handle. UNLIKE `Z3_solver` — whose
//! handles each own an independent replayable assertion stack (see
//! [`super::Z3SolverHandle`]) — an optimize handle installs its state on the
//! context's single `ay_dpll::api::Solver` ENGINE. Several Optimize handles and
//! any number of Solver handles may share a context, as in z3: another
//! handle's engine use displaces an Optimize handle's state, and the handle
//! replays its recorded hard constraints, soft constraints, objectives and
//! scopes before its next engine use (`restore_optimize_engine`); objective
//! optima are snapshotted at check time. `Z3_optimize_from_string` binds the
//! text's names to the context's declarations (`parse_binding`) and records
//! its formulas on the handle like the API calls do. Only a text outside the
//! rebinding fragment is parsed globally; such content is not recorded, so
//! that handle stays alone in its context (`Z3_INVALID_USAGE`); silent
//! union/wipe behavior is never allowed. Fixedpoint handles may coexist
//! because they only read the shared term arena and solve in an independent
//! CHC engine. `inc_ref`/`dec_ref` are bookkeeping-only no-ops; the handle
//! lives until `Z3_del_context` frees the arena.
//!
//! Objectives are numbered as z3 numbers them: each `maximize` / `minimize`
//! is one objective, and so is each soft-constraint group (one per id), whose
//! value is the total weight of its violated soft constraints.
//!
//! # Model capture
//!
//! `Solver::check_sat_max` transactionally restores the user's hard formula and
//! then revalidates the selected optimal model. `Z3_optimize_check` captures
//! exactly that consumer-accepted witness. It never re-solves a weaker set of
//! satisfied softs, which could select a different model and sever the model from
//! the certified optimum/accounting.
//!
use std::ffi::{c_int, c_uint, c_void};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::ptr;

use ay_dpll::api::{MaxSmtStatus, ObjectiveValue, Sort, Term};
use ay_frontend::Command;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::check_obligations::{
    assert_optimize_obligations, has_loose_bound_variable, lossy_binder_refusal, recheck_due,
    validate_wf_model, WfObligations, WfPhase, WfVerdict, UNBOUND_VARIABLES_REASON,
};
use super::handle_params::{EngineSettings, ParamSet};
use super::{
    apply_finite_set_decision_gate, cache_ast_vector, cache_string, cache_symbol,
    ffi_guard_const_ptr, ffi_guard_int, ffi_guard_produced, ffi_guard_ptr, ffi_guard_uint,
    ffi_guard_void, ffi_read_bounded_parser_file, ffi_read_bounded_parser_text,
    ffi_read_bounded_text, finite_set_decision_gate, flatten_statistics, public_ast_sort,
    record_ast_sort, require_term_ast_or_return, term_to_ast, DecisionOwnerFamily,
    FiniteSetDecisionGate, ModelHandle, ObjectiveSense, ObjectiveSlot, OptimizeCheckOutcome,
    OptimizeHandle, OptimizeScopeMarker, ParamDescr, ParamDescrsHandle, SoftRecord, StatsHandle,
    Z3Context, Z3_ast, Z3_ast_vector, Z3_context, Z3_model, Z3_optimize, Z3_param_descrs,
    Z3_params, Z3_stats, Z3_string, Z3_symbol, Z3_EXCEPTION, Z3_FILE_ACCESS_ERROR, Z3_INVALID_ARG,
    Z3_INVALID_USAGE, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF, Z3_OK, Z3_PK_BOOL, Z3_PK_INVALID,
    Z3_PK_STRING, Z3_PK_UINT,
};

// ---- Optimize lifecycle ----

/// Create an optimization context (MaxSMT handle).
///
/// The returned handle aliases the context's single AY `Solver`; it is owned by
/// the context arena and lives until `Z3_del_context`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_optimize(c: Z3_context) -> Z3_optimize {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. The handle is registered in `optimize_handle_cache`
    // and freed once, on context drop.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            // Several Optimize handles share a context's engine the way
            // Solver and Optimize handles do: each replays its recorded
            // state before its next engine use. Content parsed through the
            // legacy global path is not recorded and keeps its handle alone.
            if let Some(reason) = ctx.optimize_replay_blocker() {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(format!(
                    "Z3_mk_optimize: this context's Optimize handle cannot share the engine \
                     ({reason}); use a separate Z3_context"
                ));
                return ptr::null_mut();
            }
            let other_optimize = !ctx.optimize_handle_cache.is_empty();
            // The engine may hold a Solver-family goal (a check or parse that
            // ran before this handle existed): start displaced so the first
            // engine use installs only this handle's (empty) state.
            let solver_family_used = ctx.decision_owner == Some(DecisionOwnerFamily::Solver);
            if !ctx.claim_decision_owner(DecisionOwnerFamily::Optimize, "Z3_mk_optimize") {
                return ptr::null_mut();
            }
            if solver_family_used || other_optimize {
                ctx.optimize_engine_displaced = true;
            }
            let handle = Box::into_raw(Box::new(OptimizeHandle {
                _ctx: c,
                hard: Vec::new(),
                softs: Vec::new(),
                parsed_soft_public_terms: Vec::new(),
                public_objectives: Vec::new(),
                objective_senses: Vec::new(),
                objective_slots: Vec::new(),
                replay_blocker: None,
                last_objective_values: Vec::new(),
                last_objective_epsilons: Vec::new(),
                last_model: None,
                last_model_text: None,
                last_check_outcome: None,
                tracked: Vec::new(),
                scope_markers: Vec::new(),
                last_unsat_core: None,
                last_reason_unknown: None,
                last_statistics: None,
                terminal_error: None,
                params: ParamSet::default(),
            }));
            ctx.optimize_handle_cache.push(handle);
            ctx.last_error = Z3_OK;
            handle
        })
    }
}

/// Increment optimize reference count (bookkeeping no-op).
///
/// Mirrors `Z3_solver_inc_ref`: the handle is arena-owned and freed only by
/// `Z3_del_context`, so this never frees anything.
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_inc_ref(_c: Z3_context, _o: Z3_optimize) {}

/// Decrement optimize reference count (bookkeeping no-op).
///
/// Mirrors `Z3_solver_dec_ref`: the handle is arena-owned and freed only by
/// `Z3_del_context`, so this never frees anything (no early-free of an
/// arena-owned handle).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_dec_ref(_c: Z3_context, _o: Z3_optimize) {}

/// Reject semantic use of an Optimize handle that was permanently failed
/// closed after an incomplete parse transaction.
fn optimize_handle_is_usable(ctx: &mut Z3Context, opt: &OptimizeHandle, operation: &str) -> bool {
    if !ctx.decision_engine_is_usable(operation) {
        return false;
    }
    if let Some(reason) = &opt.terminal_error {
        ctx.last_error = Z3_INVALID_USAGE;
        ctx.error_msg = Some(format!(
            "{operation}: optimize handle is unavailable: {reason}"
        ));
        return false;
    }
    if let Err(reason) = restore_optimize_engine(ctx, opt) {
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(format!("{operation}: {reason}"));
        return false;
    }
    true
}

/// Re-install `opt`'s state on the shared engine after a Solver-family use of
/// the same context reset it (`Z3Context::reset_engine_for_solver_goal`).
///
/// Z3 runs Solver and Optimize objects side by side in one context; AY runs
/// both on the context's single engine, and a Solver check replaces the
/// engine's assertions with its own goal. The Optimize handle records every
/// hard constraint, soft constraint, objective and scope marker it installed,
/// so it replays them, scope by scope, before its next engine use. Content
/// parsed from SMT-LIB text is not recorded; such a handle never shares its
/// context with Solver handles (`Z3Context::claim_decision_owner`), so the
/// error below is defence in depth.
fn restore_optimize_engine(ctx: &mut Z3Context, opt: &OptimizeHandle) -> Result<(), String> {
    let owner = ptr::from_ref(opt);
    if ctx.optimize_engine_owner.is_null() && !ctx.optimize_engine_displaced {
        // The first Optimize engine use of a context that never displaced:
        // the engine holds exactly this handle's (initially empty) state.
        ctx.optimize_engine_owner = owner;
    }
    if !ctx.optimize_engine_displaced && ctx.optimize_engine_owner == owner {
        return Ok(());
    }
    if let Some(reason) = &opt.replay_blocker {
        return Err(format!(
            "the Optimize state was displaced by a Solver check and cannot be replayed ({reason})"
        ));
    }
    ctx.solver
        .try_reset_assertions()
        .map_err(|e| format!("cannot reset the engine for Optimize replay: {e}"))?;
    let (mut hard, mut soft, mut tracked, mut objective) = (0, 0, 0, 0);
    let end = OptimizeScopeMarker {
        hard_len: opt.hard.len(),
        soft_len: opt.softs.len(),
        tracked_len: opt.tracked.len(),
        public_objective_len: opt.public_objectives.len(),
        objective_slot_len: opt.objective_slots.len(),
        parsed_soft_public_len: opt.parsed_soft_public_terms.len(),
    };
    let scopes = opt.scope_markers.len();
    for (level, marker) in opt
        .scope_markers
        .iter()
        .chain(std::iter::once(&end))
        .enumerate()
    {
        for &term in &opt.hard[hard..marker.hard_len] {
            ctx.solver
                .try_assert_term(term)
                .map_err(|e| format!("Optimize replay: {e}"))?;
        }
        // A tracking literal is an assumption of every check (z3 asserts
        // `t => a` and assumes `t`); see `Z3_optimize_assert_and_track`.
        for &(literal, _) in &opt.tracked[tracked..marker.tracked_len] {
            ctx.solver
                .try_assert_term(literal)
                .map_err(|e| format!("Optimize replay: {e}"))?;
        }
        for record in &opt.softs[soft..marker.soft_len] {
            ctx.solver
                .assert_soft(record.term, record.weight, None)
                .map_err(|e| format!("Optimize replay: {e}"))?;
        }
        for (index, &term) in opt.public_objectives[objective..marker.public_objective_len]
            .iter()
            .enumerate()
        {
            let registered = match opt
                .objective_senses
                .get(objective + index)
                .copied()
                .flatten()
            {
                Some(ObjectiveSense::Maximize) => ctx.solver.try_maximize(term),
                Some(ObjectiveSense::Minimize) => ctx.solver.try_minimize(term),
                None => return Err("an objective has no recorded direction".to_string()),
            };
            registered.map_err(|e| format!("Optimize replay: {e}"))?;
        }
        (hard, soft, tracked, objective) = (
            marker.hard_len,
            marker.soft_len,
            marker.tracked_len,
            marker.public_objective_len,
        );
        if level < scopes {
            ctx.solver
                .try_push()
                .map_err(|e| format!("Optimize replay: {e}"))?;
        }
    }
    ctx.optimize_engine_displaced = false;
    ctx.optimize_engine_owner = owner;
    Ok(())
}

// ---- Asserting constraints ----

/// Assert a HARD constraint into the optimization context.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_assert(c: Z3_context, o: Z3_optimize, a: Z3_ast) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary. `a` is a u64 AST handle (Copy), authenticated below.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in assert".to_string());
                return;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_assert") {
                return;
            }
            let term = require_term_ast_or_return!(ctx, a, "Z3_optimize_assert", "formula");
            if let Err(e) = ctx.solver.try_assert_term(term) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            // Mirror onto the handle's clean assertion set (for get_assertions).
            opt.hard.push(term);
            opt.clear_check_artifacts();
            release_optimize_adopted_definitions(ctx, opt);
            ctx.last_error = Z3_OK;
        });
        // SAFETY: the guard has returned; see `finish_optimize_operation`.
        finish_optimize_operation(c, o);
    }
}

/// Assert a SOFT constraint with the given weight and (optional) group id.
///
/// `weight` is a C string. Z3 permits rationals here; AY's MaxSMT engine takes
/// integer weights, so we parse `weight` as a non-negative integer. A
/// non-integer, negative, or unparseable weight is rejected with
/// `Z3_INVALID_ARG` on the context and the soft is NOT registered; the function
/// returns the index it *would* have had (the current soft count) so callers
/// observe no insertion — they should check `Z3_get_error_code`.
///
/// `id` is an optional group symbol (may be null); it is threaded through to the
/// engine as the soft's group label.
///
/// Returns the index of the objective of the soft constraint's group (z3's
/// numbering: one objective per group id, shared by its soft constraints).
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle;
/// `weight` must be a null-terminated C string (or null); `id` may be null.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_assert_soft(
    c: Z3_context,
    o: Z3_optimize,
    a: Z3_ast,
    weight: Z3_string,
    id: Z3_symbol,
) -> c_uint {
    // Pre-extract the weight string and group label outside the guard, since raw
    // pointer dereferences need to happen in the unsafe extern "C" context.
    let weight_str: Option<String> = if weight.is_null() {
        None
    } else {
        // SAFETY: the caller's `# Safety` contract guarantees `weight`, when non-null, points to
        // a valid null-terminated C string owned by the caller for the duration of this call.
        Some(unsafe { ffi_read_bounded_text(weight) }.unwrap_or_default())
    };
    // SAFETY: `id`, when non-null, is a live symbol handle of the context.
    let group = unsafe { soft_group(id) };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    let index = unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            // Resolve `o` -> &mut OptimizeHandle. Null handle is invalid.
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in assert_soft".to_string());
                return 0;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_assert_soft") {
                return 0;
            }

            // Parse the weight as a non-negative integer. Reject anything else
            // with a clear error rather than silently mis-weighting the problem.
            let parsed_weight: Option<u64> = match weight_str.as_deref() {
                // Z3 default weight when the string is absent is "1".
                None => Some(1),
                Some(s) => {
                    let t = s.trim();
                    if t.is_empty() {
                        None
                    } else {
                        t.parse::<u64>().ok()
                    }
                }
            };
            let Some(w) = parsed_weight else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_optimize_assert_soft: weight must be a non-negative integer, got {:?} \
                     (rationals not yet supported)",
                    weight_str.unwrap_or_default()
                ));
                // No insertion; report the index it would have taken.
                return opt.softs.len() as c_uint;
            };

            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_optimize_assert_soft",
                "formula",
                opt.softs.len() as c_uint
            );
            // The engine optimizes one group; the group stays on the handle.
            match ctx.solver.assert_soft(term, w, None) {
                Ok(_) => {
                    // Record the soft locally so `to_string` can render the
                    // handle's soft set and the handle can replay it. The
                    // exact witness itself is captured directly from the
                    // solver's admitted MaxSMT result.
                    opt.softs.push(SoftRecord {
                        term,
                        weight: w,
                        group: group.clone(),
                    });
                    opt.clear_check_artifacts();
                    ctx.last_error = Z3_OK;
                    // z3 returns the index of the objective of the soft
                    // constraint's group (one per id).
                    soft_slot(opt, group.clone()) as c_uint
                }
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    opt.softs.len() as c_uint
                }
            }
        })
    };
    // SAFETY: the guard has returned; see `finish_optimize_operation`.
    unsafe { finish_optimize_operation(c, o) };
    index
}

/// The group of a soft constraint: the id symbol's name, with no symbol and
/// the empty symbol (z3py's default) meaning the default group.
///
/// # Safety
/// `id` is null or a `SymbolHandle` the context keeps alive.
unsafe fn soft_group(id: Z3_symbol) -> Option<String> {
    if id.is_null() {
        return None;
    }
    // SAFETY: non-null, and live per the contract; the Z3 C API is
    // single-threaded per context, so this shared read does not race.
    Some(unsafe { &*id }.display_name()).filter(|group| !group.is_empty())
}

// ---- Solving ----

/// Solve the MaxSMT problem.
///
/// Returns `Z3_L_TRUE` if the problem is satisfiable (an optimum was found),
/// `Z3_L_FALSE` if the hard constraints are unsatisfiable, and `Z3_L_UNDEF`
/// otherwise (unknown — e.g. an unbounded Int objective, which AY reports
/// honestly as unknown rather than fabricating a finite optimum).
///
/// Routing (see module docs): arithmetic objectives and soft constraints may
/// each be optimized alone. Their unsupported combination is rejected with
/// `Z3_L_UNDEF`/`Z3_INVALID_ARG`; neither class is ever silently ignored.
///
/// Check-time assumptions hold for this check only: they are asserted in a
/// scope of their own around the optimization, and an unsat core is the
/// tracking literals and the assumptions (sound, not minimal).
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
/// `assumptions` must point to `num_assumptions` elements when `num_assumptions > 0`.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_check(
    c: Z3_context,
    o: Z3_optimize,
    num_assumptions: c_uint,
    assumptions: *const Z3_ast,
) -> c_int {
    // SAFETY: the caller's contract: `assumptions` holds `num_assumptions`
    // handles when the count is positive.
    if !unsafe { super::ffi_count_within_limit(c, "Z3_optimize_check", num_assumptions) } {
        return Z3_L_UNDEF;
    }
    let assumption_asts: Vec<Z3_ast> = if num_assumptions > 0 && !assumptions.is_null() {
        // SAFETY: as above; the count was range-checked.
        (0..num_assumptions as usize)
            .map(|i| unsafe { *assumptions.add(i) })
            .collect()
    } else {
        Vec::new()
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in check".to_string());
                return Z3_L_UNDEF;
            };
            if num_assumptions > 0 && assumptions.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_optimize_check: null assumptions array for a positive count".to_string(),
                );
                return Z3_L_UNDEF;
            }
            let mut assumed = Vec::with_capacity(assumption_asts.len());
            for &ast in &assumption_asts {
                let Some(term) =
                    super::require_term_ast(ctx, ast, "Z3_optimize_check", "assumption")
                else {
                    return Z3_L_UNDEF;
                };
                assumed.push(term);
            }
            // The handle's own parameters, applied in full for this check
            // only, and a cleared interrupt (see `handle_params`).
            let settings =
                EngineSettings::apply(&mut ctx.solver, opt.params.over(ctx.default_params));
            let mut verdict =
                if let Some(refused) = refuse_undecided_optimize_goal(ctx, opt, &assumed) {
                    refused
                } else {
                    optimize_check_phases(ctx, opt, &assumed)
                };
            if verdict == Z3_L_TRUE {
                scope_optimize_model(ctx, opt, &assumed);
                if let Err(reason) = refuse_unconfirmed_optimize_model(ctx, opt, &assumed) {
                    verdict = optimize_unknown(ctx, opt, None, reason);
                }
            }
            release_optimize_adopted_definitions(ctx, opt);
            settings.restore(&mut ctx.solver);
            verdict
        })
    }
}

/// An Optimize check in the two checks of `wf_guards::WfPhase`: one that
/// leaves the quantified well-formedness guards out (validating its optimum)
/// and one of the replayed handle that asserts them, in the order the goal
/// picks. Only a handle the engine can replay with at most one objective
/// takes the relaxed check: the optimum of the relaxed goal is the optimum of
/// the goal exactly when its witness is a model of the guards, and only one
/// objective has one witness.
fn optimize_check_phases(ctx: &mut Z3Context, opt: &mut OptimizeHandle, assumed: &[Term]) -> c_int {
    let started = std::time::Instant::now();
    let mut phase = if opt.replay_blocker.is_none() && opt.public_objectives.len() <= 1 {
        WfPhase::default()
    } else {
        WfPhase::guarded()
    };
    let first = optimize_check_once(ctx, opt, assumed, &mut phase);
    if !recheck_due(ctx, &phase, started) {
        return first;
    }
    // The relaxed check's engine state is discarded: the handle is replayed
    // from its own records (see `restore_optimize_engine`).
    ctx.optimize_engine_displaced = true;
    let configured = ctx.solver.timeout();
    ctx.solver
        .set_timeout(configured.map(|timeout| timeout.saturating_sub(started.elapsed())));
    let second = optimize_check_once(ctx, opt, assumed, &mut phase.next());
    ctx.solver.set_timeout(configured);
    second
}

fn optimize_check_once(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    assumed: &[Term],
    phase: &mut WfPhase,
) -> c_int {
    if assumed.is_empty() {
        optimize_check_handle(ctx, opt, &[], phase)
    } else {
        optimize_check_assuming(ctx, opt, assumed, phase)
    }
}

/// The FFI gates of an optimum ([`gate_optimize_sat`]), then its
/// well-formedness (see [`optimize_check_phases`]): its model must give every
/// reached symbol a value of its public sort, and, when its check left the
/// quantified guards out, every objective must have an attained, finite
/// optimum (an unbounded or unattained optimum of the relaxed goal says
/// nothing of the goal's).
fn validate_optimum(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    finite_set_gate: &FiniteSetDecisionGate,
    obligations: &WfObligations,
    phase: &mut WfPhase,
) -> c_int {
    if gate_optimize_sat(ctx, opt, finite_set_gate) != Z3_L_TRUE {
        return Z3_L_UNDEF;
    }
    let relaxed = !phase.asserts_quantified_guards() && !obligations.lazy.is_empty();
    if relaxed {
        let attained = opt
            .last_objective_values
            .iter()
            .all(|(_, value)| matches!(value, Some(ObjectiveValue::Finite(_))))
            && opt.last_objective_epsilons.iter().all(Option::is_none);
        if !attained {
            phase.recheck = phase.may_recheck(obligations);
            let reason = "the optimum of the goal without its well-formedness guards is not                           attained by a model"
                .to_string();
            return optimize_unknown(ctx, opt, None, reason);
        }
    }
    let model = opt.last_model.clone();
    let text = opt.last_model_text.clone();
    match validate_wf_model(
        ctx,
        obligations,
        model.as_ref(),
        text.as_deref(),
        phase.asserts_quantified_guards(),
        phase.may_recheck(obligations),
    ) {
        WfVerdict::Accept => Z3_L_TRUE,
        WfVerdict::Retry(reason) => {
            phase.recheck = true;
            optimize_unknown(ctx, opt, None, reason)
        }
        WfVerdict::Refuse(reason) => optimize_unknown(ctx, opt, None, reason),
    }
}

/// Decide an Optimize check as `unknown` without the engine when its goal
/// holds a loose bound variable (libz3 5.1.0: `Z3_EXCEPTION`, "Formulas
/// should not contain unbound variables") or a binder of a lossy sort (see
/// `check_obligations`); `None` when the goal goes to the engine.
fn refuse_undecided_optimize_goal(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    assumed: &[Term],
) -> Option<c_int> {
    let mut roots = opt.hard.clone();
    roots.extend(opt.softs.iter().map(|soft| soft.term));
    roots.extend(opt.parsed_soft_public_terms.iter().copied());
    roots.extend(opt.public_objectives.iter().copied());
    roots.extend(
        opt.tracked
            .iter()
            .flat_map(|&(tracking, assertion)| [tracking, assertion]),
    );
    roots.extend_from_slice(assumed);
    let (code, reason) = if has_loose_bound_variable(ctx, &roots) {
        (Z3_EXCEPTION, UNBOUND_VARIABLES_REASON.to_string())
    } else {
        (Z3_OK, lossy_binder_refusal(ctx, &roots)?)
    };
    opt.clear_check_artifacts();
    Some(optimize_unknown(ctx, opt, Some(code), reason))
}

/// Restrict the model of `opt`'s SAT check to the symbols of its own
/// constraints (hard, soft, tracked, objectives), closed under the context's
/// theory axioms that mention a kept symbol, as `scope_published_model` does
/// for a Solver: the engine's model lists every symbol declared on the shared
/// engine, so the Optimize model listed constants only other handles (or no
/// handle at all) use (measured: `[x = 10, z = 0, y = 0]` for `maximize x`
/// under `x <= 10`; z3: `[x = 10]`). Restriction never changes a kept value.
fn scope_optimize_model(ctx: &mut Z3Context, opt: &mut OptimizeHandle, assumed: &[Term]) {
    let mut roots = opt.hard.clone();
    roots.extend(assumed.iter().copied());
    roots.extend(opt.softs.iter().map(|soft| soft.term));
    roots.extend(opt.parsed_soft_public_terms.iter().copied());
    roots.extend(opt.tracked.iter().map(|&(literal, _)| literal));
    roots.extend(opt.public_objectives.iter().copied());
    let Ok(mut keep) = ctx.solver.declared_symbols_in(&roots) else {
        // The scope could not be computed: keep the whole model (it still
        // satisfies the constraints; only extra symbols are listed).
        return;
    };
    let mut axioms = ctx.background_axioms.clone();
    axioms.extend(ctx.global_definition_axioms.iter().copied());
    let mut pending: Vec<_> = axioms
        .iter()
        .filter_map(|&axiom| ctx.solver.declared_symbols_in(&[axiom]).ok())
        .collect();
    loop {
        let before = pending.len();
        pending.retain(|symbols| {
            if symbols.is_disjoint(&keep) {
                return true;
            }
            keep.extend(symbols.iter().cloned());
            false
        });
        if pending.len() == before {
            break;
        }
    }
    if let Some(model) = opt.last_model.as_mut() {
        model.retain_names(|name| keep.contains(name));
    }
    if let Some(text) = opt.last_model_text.as_deref() {
        let scoped = super::model_params::retain_model_text_symbols(text, &keep);
        opt.last_model_text = Some(scoped);
    }
}

/// The fail-closed backstop of `Z3_solver_check` on an Optimize SAT: the
/// published model, with its function tables and read as `Z3_model_eval`
/// with model completion reads it, must make every hard constraint and
/// tracked literal literally true (measured: a model without the table of
/// the caller's `f`, under which `f(x) == 5` read `0 == 5` with z3's
/// completion, was published as the optimum).
fn refuse_unconfirmed_optimize_model(
    ctx: &mut Z3Context,
    opt: &OptimizeHandle,
    assumed: &[Term],
) -> Result<(), String> {
    let (Some(model), Some(text)) = (opt.last_model.clone(), opt.last_model_text.clone()) else {
        return Err(
            "the optimum's model is unavailable; sat is not published without a model".to_string(),
        );
    };
    let mut obligations = opt.hard.clone();
    obligations.extend(opt.tracked.iter().map(|&(literal, _)| literal));
    obligations.extend(assumed.iter().copied());
    super::solver::refuse_untransported_model_parts(
        ctx,
        model,
        &text,
        &super::solver::PublicationObligations {
            obligations: &obligations,
            engine_roots: &obligations,
        },
    )
}

/// Remove a definition the engine adopted from this handle's definitional
/// `forall` once the operation that installed it is done (see
/// `solver::release_adopted_definitions`): the handle replays its state before
/// its next engine use, so the definition is back for its own checks but never
/// rewrites terms the caller builds for another handle in between.
///
/// Parsed content cannot be replayed. A handle holding some keeps its engine
/// state, unless a definition is adopted: then the definition is released
/// all the same and the handle is retired (libz3 5.1.0 keeps a later
/// `f(x) == 0` of another handle as built; AY's engine would rewrite it).
fn release_optimize_adopted_definitions(ctx: &mut Z3Context, opt: &mut OptimizeHandle) {
    if opt.replay_blocker.is_some() && ctx.solver.has_assertion_derived_definitions() {
        opt.terminal_error = Some(
            "the handle's parsed content installed a definition that AY cannot keep apart \
             from other handles, and the content cannot be replayed after its release"
                .to_string(),
        );
    }
    super::solver::release_adopted_definitions(ctx, "Z3_optimize");
}

/// After an engine-mutating Optimize operation on `o` (whose guard has
/// returned): release any definition it left adopted, including on its error
/// paths after the handle's state was replayed.
///
/// # Safety
/// `c` and `o` must be null or live and not otherwise borrowed.
unsafe fn finish_optimize_operation(c: Z3_context, o: Z3_optimize) {
    // SAFETY: the context pointer is null or live and unborrowed (contract);
    // this borrow ends with the call.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return;
    };
    // SAFETY: the optimize handle is null or live in the context arena, a
    // separate allocation from the context itself (contract).
    let Some(opt) = (unsafe { o.as_mut() }) else {
        return;
    };
    let released = catch_unwind(AssertUnwindSafe(|| {
        release_optimize_adopted_definitions(ctx, opt);
    }));
    if released.is_err() {
        ctx.poison_decision_engine(
            "Z3_optimize: an adopted definition could not be released".to_string(),
        );
    }
}

/// Record an Optimize check that ends `unknown` for `reason`, with the context
/// error set to `code` (`None` keeps the error the caller already set).
fn optimize_unknown(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    code: Option<c_uint>,
    reason: String,
) -> c_int {
    if let Some(code) = code {
        ctx.last_error = code;
        ctx.error_msg = Some(reason.clone());
    }
    opt.last_reason_unknown = Some(reason);
    opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
    Z3_L_UNDEF
}

/// The body of [`Z3_optimize_check`] for a live handle.
fn optimize_check_handle(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    assumed: &[Term],
    phase: &mut WfPhase,
) -> c_int {
    // Retire the previous query before every exit from this decision
    // endpoint. In particular, an unsupported-assumption rejection
    // must not leave an earlier model or optimum queryable.
    opt.clear_check_artifacts();
    ctx.last_error = Z3_OK;
    ctx.error_msg = None;

    if !ctx.decision_engine_is_usable("Z3_optimize_check") {
        let reason = ctx
            .error_msg
            .clone()
            .unwrap_or_else(|| "context decision engine is unavailable".to_string());
        return optimize_unknown(ctx, opt, None, reason);
    }
    if let Some(reason) = opt.terminal_error.clone() {
        return optimize_unknown(ctx, opt, Some(Z3_INVALID_USAGE), reason);
    }
    if let Err(reason) = restore_optimize_engine(ctx, opt) {
        return optimize_unknown(ctx, opt, Some(Z3_EXCEPTION), reason);
    }

    let mut finite_set_roots = opt.hard.clone();
    finite_set_roots.extend(assumed.iter().copied());
    finite_set_roots.extend(opt.softs.iter().map(|soft| soft.term));
    finite_set_roots.extend(opt.parsed_soft_public_terms.iter().copied());
    for &(tracking, assertion) in &opt.tracked {
        finite_set_roots.push(tracking);
        finite_set_roots.push(assertion);
    }
    finite_set_roots.extend(opt.public_objectives.iter().copied());
    let finite_set_gate = finite_set_decision_gate(ctx, &finite_set_roots);
    if finite_set_gate.quantifier_reason.is_some() {
        let _ =
            apply_finite_set_decision_gate(ctx, Z3_L_UNDEF, &finite_set_gate, "Z3_optimize_check");
        let reason = ctx
            .error_msg
            .clone()
            .unwrap_or_else(|| "finite-set optimization result is not certified".to_string());
        return optimize_unknown(ctx, opt, Some(Z3_OK), reason);
    }

    // Inject theory-internal background axioms (special-relation orders,
    // Char range invariants) so they constrain the optimization solve.
    // Unlike the plain-solver path this engine state is not reset per
    // check, so a repeated check may re-assert them — harmless (asserting
    // a Bool constraint twice is idempotent) and always sound (they only
    // add constraints over fresh predicates / bounded Char code points).
    // The Optimize engine state is incremental (asserted at
    // `Z3_optimize_assert` time), so check-time goal expansion is not
    // available here: the rec-def axioms the goal reaches are included
    // (keeps the sound definitional UNSAT power; the unreached ones only
    // stalled the check), and a SAT/optimum over a rec-f mention is demoted.
    let obligations = match assert_optimize_obligations(ctx, &finite_set_roots, phase) {
        Ok(obligations) => obligations,
        Err(e) => return optimize_unknown(ctx, opt, Some(Z3_EXCEPTION), e),
    };

    let has_objectives = ctx.solver.num_objectives() > 0;
    let has_parsed_softs = ctx.solver.num_parsed_soft_constraints() > 0;
    // Joint arithmetic+soft and grouped-soft problems route to the
    // executor's native dispatch (`optimize_check` transplants API
    // softs with the tracked declaration sequence, so joint and
    // lexicographic-group problems take the joint/grouped engines).
    let native = has_objectives || has_parsed_softs || ctx.solver.has_grouped_soft_constraints();
    let Some(verdict) = optimize_solve(ctx, opt, native) else {
        return Z3_L_UNDEF;
    };
    capture_check_diagnostics(ctx, opt, verdict);
    if verdict == Z3_L_TRUE {
        // Snapshot the optima: a later Solver check on this context
        // resets the engine that holds them.
        opt.last_objective_values = (0..opt.public_objectives.len())
            .map(|idx| {
                (
                    ctx.solver.objective_sort(idx),
                    ctx.solver.get_objective_value(idx),
                )
            })
            .collect();
        opt.last_objective_epsilons = (0..opt.public_objectives.len())
            .map(|idx| ctx.solver.get_objective_epsilon(idx))
            .collect();
        return validate_optimum(ctx, opt, &finite_set_gate, &obligations, phase);
    }
    if verdict == Z3_L_UNDEF {
        phase.note_undecided(&obligations);
    }
    verdict
}

/// [`optimize_check_handle`] under check-time assumptions: they hold as hard
/// constraints in a scope of their own, popped after the check (z3 assumes
/// them for this check only), and an unsat core is the tracking literals and
/// the assumptions (sound, not minimal).
fn optimize_check_assuming(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    assumed: &[Term],
    phase: &mut WfPhase,
) -> c_int {
    opt.clear_check_artifacts();
    if let Err(reason) = restore_optimize_engine(ctx, opt) {
        return optimize_unknown(ctx, opt, Some(Z3_EXCEPTION), reason);
    }
    if let Err(e) = ctx.solver.try_push() {
        return optimize_unknown(
            ctx,
            opt,
            Some(Z3_EXCEPTION),
            format!("Z3_optimize_check: {e}"),
        );
    }
    let mut verdict = Z3_L_UNDEF;
    let mut asserted = true;
    for &term in assumed {
        if let Err(e) = ctx.solver.try_assert_term(term) {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("Z3_optimize_check: {e}"));
            asserted = false;
            break;
        }
    }
    if asserted {
        verdict = optimize_check_handle(ctx, opt, assumed, phase);
    }
    if let Err(e) = ctx.solver.try_pop() {
        let reason = format!("Z3_optimize_check: the assumption scope could not be closed: {e}");
        opt.terminal_error = Some(reason.clone());
        return optimize_unknown(ctx, opt, Some(Z3_EXCEPTION), reason);
    }
    if verdict == Z3_L_FALSE {
        let mut core = opt.last_unsat_core.take().unwrap_or_default();
        for &term in assumed {
            if !core.contains(&term) {
                core.push(term);
            }
        }
        opt.last_unsat_core = Some(core);
    }
    if !asserted {
        let reason = ctx
            .error_msg
            .clone()
            .unwrap_or_else(|| "an assumption could not be asserted".to_string());
        return optimize_unknown(ctx, opt, None, reason);
    }
    verdict
}

/// Route the solve. Three paths (see module docs):
///   1. arithmetic objectives registered, soft constraints parsed
///      into the executor via `Z3_optimize_from_string`/`_from_file`,
///      or grouped API softs (`objectives`) → the executor's native
///      `(check-sat)` dispatch (`optimize_check` transplants API
///      softs, so joint soft+arithmetic and grouped problems take
///      the joint/grouped engines).
///   2. else flat API-level softs (from `Z3_optimize_assert_soft`)
///      → the weight-exact MaxSMT engine (`check_sat_max`).
///   3. else a plain check-sat.
///
/// `None` when the engine raised (the diagnostics are already captured).
fn optimize_solve(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    objectives: bool,
) -> Option<c_int> {
    if objectives {
        return Some(optimize_check_objectives(ctx, opt));
    }
    let result = match ctx.solver.check_sat_max() {
        Ok(r) => r,
        Err(e) => {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{e}"));
            capture_check_diagnostics(ctx, opt, Z3_L_UNDEF);
            return None;
        }
    };
    Some(match result.status {
        MaxSmtStatus::Optimal => {
            // Capture the exact model selected, restored, and revalidated by
            // the MaxSMT transaction. An Optimal result without a
            // consumer-admissible witness violates the boundary contract and
            // must fail closed.
            match ctx.solver.model_for_consumer() {
                Some(model) => {
                    opt.last_model = Some(model.into_inner());
                    // The decoder text (#overloaded-nil-surface).
                    opt.last_model_text = ctx.solver.model_str_for_decoder();
                    ctx.last_error = Z3_OK;
                    Z3_L_TRUE
                }
                None => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(
                        "MaxSMT optimum has no consumer-admissible witnessing model".to_string(),
                    );
                    Z3_L_UNDEF
                }
            }
        }
        MaxSmtStatus::HardUnsatisfiable => {
            ctx.last_error = Z3_OK;
            Z3_L_FALSE
        }
        // `MaxSmtStatus` is `#[non_exhaustive]`; Unknown and any future
        // not-yet-determined variant maps to Z3_L_UNDEF.
        MaxSmtStatus::Unknown => Z3_L_UNDEF,
        _ => Z3_L_UNDEF,
    })
}

/// The FFI trust gates on an Optimize SAT whose diagnostics and optima are
/// already captured: `Z3_L_TRUE`, or `Z3_L_UNDEF` with the SAT's public
/// authority revoked and the reason recorded.
fn gate_optimize_sat(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    finite_set_gate: &FiniteSetDecisionGate,
) -> c_int {
    let gated =
        apply_finite_set_decision_gate(ctx, Z3_L_TRUE, finite_set_gate, "Z3_optimize_check");
    if gated != Z3_L_TRUE {
        let reason = ctx
            .error_msg
            .clone()
            .unwrap_or_else(|| "finite-set optimum is not certified".to_string());
        return optimize_unknown(ctx, opt, None, reason);
    }
    // Transitive-closure SAT gate: the background axioms for a
    // `Z3_mk_transitive_closure` predicate are only PARTIAL (see
    // `verify_transitive_closure_model` in solver.rs), so a SAT here
    // could rest on an over-approximated TC. The optimize path has no
    // snapshot verifier wired, so it honestly reports unknown rather
    // than release an unverified SAT (never a fabricated verdict). The
    // backend model and objective values were captured before this FFI
    // trust gate; downgrading SAT to UNKNOWN revokes their public authority
    // while retaining the reason/statistics for this completed query.
    if !ctx.transitive_closure_regs.is_empty() {
        let reason = "transitive-closure model verification is not wired into the \
                      optimization path; refusing an unverified sat"
            .to_string();
        return optimize_unknown(ctx, opt, None, reason);
    }
    // Recursive-definition SAT gate (P1.1): the Optimize path cannot
    // expand its incremental goal at check time, so a rec-defined
    // function reaches the engine as a quantified-axiom-constrained
    // plain UF. UNSAT is sound (the axiom is definitional); a SAT /
    // optimum over ANY mention of a rec-defined name is not certified
    // and is demoted honestly (never a fabricated optimum). The scan
    // covers hard constraints, API softs, tracked pairs, and every
    // registered objective; parsed-in soft constraints are not
    // individually reachable here, so their mere presence demotes.
    if !ctx.rec_fun_defs.is_empty() {
        let mut scan: Vec<Term> = opt.hard.clone();
        scan.extend(opt.softs.iter().map(|s| s.term));
        for &(p, a) in &opt.tracked {
            scan.push(p);
            scan.push(a);
        }
        scan.extend(opt.public_objectives.iter().copied());
        let parsed_softs_present = ctx.solver.num_parsed_soft_constraints() > 0;
        if parsed_softs_present || ctx.solver.contains_rec_fun_apps(&scan, &ctx.rec_fun_defs) {
            let reason = "recursive definitions are not expanded on the Optimize path; \
                          optimum not certified"
                .to_string();
            return optimize_unknown(ctx, opt, None, reason);
        }
    }
    Z3_L_TRUE
}

/// Capture the per-check diagnostics into the optimize handle: the reason-unknown
/// string and the executor statistics snapshot.
///
/// An unsat check's core is the full set of tracking literals (see
/// [`Z3_optimize_get_unsat_core`]): sound, not minimal.
fn capture_check_diagnostics(ctx: &mut Z3Context, opt: &mut OptimizeHandle, verdict: c_int) {
    opt.last_reason_unknown = if verdict == Z3_L_UNDEF {
        if ctx.last_error == Z3_OK {
            ctx.solver.reason_unknown_smtlib()
        } else {
            ctx.error_msg
                .clone()
                .or_else(|| ctx.solver.reason_unknown_smtlib())
        }
    } else {
        None
    };
    opt.last_statistics = Some(ctx.solver.statistics().clone());
    let outcome = match verdict {
        Z3_L_TRUE => OptimizeCheckOutcome::Sat,
        Z3_L_FALSE => OptimizeCheckOutcome::Unsat,
        _ => OptimizeCheckOutcome::Unknown,
    };
    opt.record_check_outcome(outcome);
    if outcome == OptimizeCheckOutcome::Unsat {
        // One entry per distinct literal: a literal tracking several
        // constraints is still one assumption (z3 reports it once).
        let mut core: Vec<Term> = Vec::new();
        for &(tracking, _) in &opt.tracked {
            if !core.contains(&tracking) {
                core.push(tracking);
            }
        }
        opt.last_unsat_core = Some(core);
    }
}

/// Run the executor's NATIVE optimization `(check-sat)` (arithmetic objectives
/// and/or soft constraints parsed into the elaboration context) and capture the
/// witnessing model.
///
/// Maps the verdict to the Z3 tri-state: SAT → `Z3_L_TRUE`, UNSAT → `Z3_L_FALSE`,
/// otherwise `Z3_L_UNDEF`. On SAT the solver's optimized model is captured into
/// the optimize handle so `Z3_optimize_get_model` returns a model realizing the
/// optima.
fn optimize_check_objectives(ctx: &mut Z3Context, opt: &mut OptimizeHandle) -> c_int {
    let result = ctx.solver.optimize_check();
    if result
        .accept_for_consumer()
        .is_ok_and(|accepted| accepted.is_sat())
    {
        // Capture the consumer-admissible model selected by the optimization
        // transaction. Both arithmetic and parsed-MaxSMT lanes leave that exact
        // recertified witness installed after restoring temporary constraints.
        match ctx.solver.model_for_consumer() {
            Some(model) => {
                opt.last_model = Some(model.into_inner());
                // As above (#overloaded-nil-surface).
                opt.last_model_text = ctx.solver.model_str_for_decoder();
                ctx.last_error = Z3_OK;
                Z3_L_TRUE
            }
            None => {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(
                    "optimized SAT result has no consumer-admissible witnessing model".to_string(),
                );
                Z3_L_UNDEF
            }
        }
    } else if result.is_unsat() {
        ctx.last_error = Z3_OK;
        Z3_L_FALSE
    } else {
        // Unknown (e.g. an unbounded Int objective): honest, not faked.
        Z3_L_UNDEF
    }
}

/// Get the model from the last successful `Z3_optimize_check`.
///
/// Returns a context-owned model handle realizing the reported optimum, or null
/// if the last check did not produce a model.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_model(c: Z3_context, o: Z3_optimize) -> Z3_model {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                return ptr::null_mut();
            };
            // Without a current model z3 raises; a null model without an
            // error read in z3py as an empty, invalid one (measured: after
            // another handle's parse retired this handle's model).
            if opt.last_check_outcome != Some(OptimizeCheckOutcome::Sat) || opt.last_model.is_none()
            {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg =
                    Some("Z3_optimize_get_model: there is no current model".to_string());
                return ptr::null_mut();
            }
            match opt.last_model.clone() {
                Some(model) => {
                    // Function interpretations are part of the snapshot, as
                    // for a Solver model: parsed out of the engine's model
                    // text captured at check time.
                    let func_interps = opt
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
                None => ptr::null_mut(),
            }
        })
    }
}

/// Best-effort SMT-LIB-ish rendering of the optimization problem.
///
/// Renders the hard assertions (via the solver) plus the registered soft
/// constraints as `(assert-soft <ast-id> :weight <w>)` lines. Term ASTs are
/// rendered by their internal handle id (AY does not pretty-print arbitrary
/// terms here), so this is a diagnostic shape, not a faithful Z3 reproduction.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_to_string(c: Z3_context, o: Z3_optimize) -> Z3_string {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic so
    // it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let mut out = String::from("(optimize\n");
            // Soft constraints recorded on this optimize handle.
            if let Some(opt) = o.as_mut() {
                // Hard assertions, by internal term id (best-effort).
                for t in &opt.hard {
                    out.push_str(&format!("  (assert t!{})\n", t.to_raw()));
                }
                for soft in &opt.softs {
                    let group = soft
                        .group
                        .as_ref()
                        .map(|id| format!(" :id {id}"))
                        .unwrap_or_default();
                    out.push_str(&format!(
                        "  (assert-soft t!{} :weight {}{})\n",
                        soft.term.to_raw(),
                        soft.weight,
                        group
                    ));
                }
            }
            out.push_str("  (check-sat)\n)");
            cache_string(ctx, out)
        })
    }
}

// ============================================================================
// Arithmetic objectives.
// ============================================================================

/// Register a `maximize` objective on term `t`.
///
/// Returns the objective's index (declaration order), which identifies it for
/// `Z3_optimize_get_lower` / `Z3_optimize_get_upper` after `Z3_optimize_check`.
/// The term should be numeric (Int / Real / BitVec); a non-numeric sort is
/// accepted here and rejected at `Z3_optimize_check` time (matching SMT-LIB).
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle;
/// `t` is a u64 AST handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_maximize(c: Z3_context, o: Z3_optimize, t: Z3_ast) -> c_uint {
    // SAFETY: `c`/`o`/`t` are forwarded under the caller's `# Safety` contract;
    // `ffi_guard_uint` handles null `c` and catches panics; `o` is null-checked.
    unsafe { optimize_register_objective(c, o, t, ObjectiveSense::Maximize) }
}

/// Register a `minimize` objective on term `t`.
///
/// See [`Z3_optimize_maximize`].
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle;
/// `t` is a u64 AST handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_minimize(c: Z3_context, o: Z3_optimize, t: Z3_ast) -> c_uint {
    // SAFETY: the caller supplies live context and optimize handles;
    // `optimize_register_objective` null-checks both before registering `t`.
    unsafe { optimize_register_objective(c, o, t, ObjectiveSense::Minimize) }
}

/// Shared registration path for `maximize`/`minimize`.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
unsafe fn optimize_register_objective(
    c: Z3_context,
    o: Z3_optimize,
    t: Z3_ast,
    sense: ObjectiveSense,
) -> c_uint {
    // SAFETY: forwarded under the caller's contract; `ffi_guard_uint` handles
    // null `c` and catches panics; `o` is null-checked below.
    let index = unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in maximize/minimize".to_string());
                return 0;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_maximize/minimize") {
                return 0;
            }
            let term = require_term_ast_or_return!(
                ctx,
                t,
                "Z3_optimize_maximize/minimize",
                "objective",
                0
            );
            match sense {
                ObjectiveSense::Maximize => ctx.solver.maximize(term),
                ObjectiveSense::Minimize => ctx.solver.minimize(term),
            };
            opt.public_objectives.push(term);
            opt.objective_senses.push(Some(sense));
            opt.objective_slots
                .push(ObjectiveSlot::Arith(opt.public_objectives.len() - 1));
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
            (opt.objective_slots.len() - 1) as c_uint
        })
    };
    // SAFETY: the guard has returned; see `finish_optimize_operation`.
    unsafe { finish_optimize_operation(c, o) };
    index
}

/// Get the lower bound (`>=` side) of objective `idx`'s optimum as an AST.
///
/// After a SAT `Z3_optimize_check`, every available scalar optimum is exact, so
/// `Z3_optimize_get_lower` and `Z3_optimize_get_upper` return the SAME value: the
/// optimum itself, as a Z3 numeral AST in the objective's sort (Int/Real
/// numeral, or a BitVec numeral for BV objectives — the unsigned value). A
/// declaration following an unbounded lexicographic predecessor has an interval
/// outcome in Z3; AY cannot represent that interval and returns null honestly.
///
/// Unbounded objectives (`+oo` for an unbounded `maximize`, `-oo` for an
/// unbounded `minimize`) return the null AST (0). DIVERGENCE FROM Z3: Z3 returns
/// a structured `oo` AST here; AY has no first-class `oo` numeral and there is no
/// finite numeral that represents infinity, so it returns null with an error
/// rather than fabricate one. (Note that an unbounded INT objective already makes
/// `Z3_optimize_check` return `Z3_L_UNDEF`, so `get_lower`/`get_upper` are not
/// usefully reached for it; only an unbounded REAL objective — which AY reports
/// SAT with `oo` — reaches this null return.) A finite optimum is always an exact
/// numeral, never fabricated.
///
/// Returns the null AST (0) and sets `Z3_INVALID_ARG` if `idx` is out of range,
/// `Z3_INVALID_USAGE` if the last check was not SAT, and `Z3_EXCEPTION` if the
/// optimum is unbounded or missing, so a binding raises instead of handing on
/// a null AST.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_lower(
    c: Z3_context,
    o: Z3_optimize,
    idx: c_uint,
) -> Z3_ast {
    // SAFETY: the caller supplies live context and optimize handles;
    // `optimize_get_objective_ast` null-checks them and bounds-checks `idx`.
    unsafe { optimize_get_objective_ast(c, o, idx) }
}

/// Get the upper bound (`<=` side) of objective `idx`'s optimum as an AST.
///
/// Identical to [`Z3_optimize_get_lower`]: AY's optimum is exact, so lower and
/// upper coincide. See [`Z3_optimize_get_lower`] for the unbounded handling
/// (null AST) and the documented Z3 divergence.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_upper(
    c: Z3_context,
    o: Z3_optimize,
    idx: c_uint,
) -> Z3_ast {
    // SAFETY: forwarded under the caller's contract.
    unsafe { optimize_get_objective_ast(c, o, idx) }
}

/// Shared accessor: build the optimum of objective `idx` as a numeral AST.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
unsafe fn optimize_get_objective_ast(c: Z3_context, o: Z3_optimize, idx: c_uint) -> Z3_ast {
    // SAFETY: forwarded; `ffi_guard_ast` handles null `c` and catches panics.
    unsafe {
        ffi_guard_produced(c, |ctx| {
            let Some(opt) = o.as_ref() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in get_lower/get_upper".to_string());
                return 0;
            };
            let slot_index = idx as usize;
            // Validate the index against the registered objectives.
            let Some(slot) = opt.objective_slots.get(slot_index).cloned() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_optimize_get_lower/upper: objective index {slot_index} out of range"
                ));
                return 0;
            };
            if opt.last_check_outcome != Some(OptimizeCheckOutcome::Sat) {
                // No optimum to report: an error, not a null AST that a binding
                // only notices later as "AST is null".
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(format!(
                    "Z3_optimize_get_lower/upper: objective {idx} has no value: the last \
                     check was not sat"
                ));
                return 0;
            }
            let idx = match slot {
                ObjectiveSlot::Arith(idx) => idx,
                ObjectiveSlot::Soft(group) => {
                    ctx.last_error = Z3_OK;
                    return soft_group_cost(ctx, opt, group.as_deref());
                }
            };
            if let (Some((Some(sort), None)), Some(Some((value, eps)))) = (
                opt.last_objective_values.get(idx).cloned(),
                opt.last_objective_epsilons.get(idx).cloned(),
            ) {
                ctx.last_error = Z3_OK;
                return build_epsilon_numeral(ctx, &value, &eps, &sort);
            }
            let Some((Some(sort), Some(value))) = opt.last_objective_values.get(idx).cloned()
            else {
                // SAT, yet no optimum recorded: say so instead of a silent null
                // that a binding reads as "AST is null" much later.
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!(
                    "Z3_optimize_get_lower/upper: no value is available for objective {idx}"
                ));
                return 0;
            };
            ctx.last_error = Z3_OK;
            let ast = build_objective_numeral(ctx, &value, &sort);
            if ast == 0 && ctx.last_error == Z3_OK {
                // Never a silent null: a binding would only notice it later.
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!(
                    "Z3_optimize_get_lower/upper: the optimum of objective {idx} could not be \
                     built as a term"
                ));
            }
            ast
        })
    }
}

/// The cost of the soft-constraint group `group` under the last optimum's
/// model: the sum of the weights of its soft constraints the model falsifies
/// (z3's value of a soft objective). Null when some soft constraint does not
/// evaluate to a Boolean value.
fn soft_group_cost(ctx: &mut Z3Context, opt: &OptimizeHandle, group: Option<&str>) -> Z3_ast {
    let Some(model) = opt.last_model.clone() else {
        return 0;
    };
    let func_interps = opt
        .last_model_text
        .as_deref()
        .map(|text| super::model_params::model_func_interps(&mut ctx.solver, text))
        .unwrap_or_default();
    let probe = ModelHandle {
        model,
        func_interps,
        user_const_interps: Vec::new(),
        user_func_interps: Vec::new(),
        rec_def_count: ctx.rec_fun_defs.len(),
        complete_functions: true,
        _ctx: ptr::null_mut(),
    };
    let mut cost = BigInt::from(0);
    for soft in opt.softs.iter().filter(|s| s.group.as_deref() == group) {
        let value = super::model_params::eval_term_under_model(ctx, &probe, soft.term, true);
        match value.and_then(|v| ctx.solver.bool_value(v)) {
            Some(true) => {}
            Some(false) => cost += BigInt::from(soft.weight),
            None => return 0,
        }
    }
    let term = ctx.solver.int_const_bigint(&cost);
    let ast = term_to_ast(ctx, term);
    record_ast_sort(ctx, ast, Sort::Int)
}

/// Build a Z3 numeral AST for an objective optimum in the given sort.
///
/// Finite optima: an exact numeral in the objective's sort. Unbounded optima
/// (`+oo` / `-oo`): AY has no first-class infinity term and there is no finite
/// numeral that represents `oo`, so this returns the null AST (0) — honest
/// rather than a fabricated finite value; the accessor then sets
/// `Z3_EXCEPTION` (z3 returns a structured `oo` AST).
fn build_objective_numeral(ctx: &mut Z3Context, value: &ObjectiveValue, sort: &Sort) -> Z3_ast {
    match value {
        ObjectiveValue::Finite(r) => build_finite_numeral(ctx, r, sort),
        // Unbounded: z3 reports the constant `oo` (an uninterpreted
        // constant named `oo`, measured on 5.1), and `-oo` as `-1 * oo`.
        // The constant is INT-sorted even for a Real objective (measured:
        // `Z3_get_sort` of a Real objective's `oo` is the Int sort).
        ObjectiveValue::PosInfinity | ObjectiveValue::NegInfinity => {
            let oo_sort = Sort::Int;
            let Some(oo) = super::terms::ffi_api_constant(
                ctx,
                &super::SymbolKey::String("oo".to_string()),
                &oo_sort,
            ) else {
                return 0;
            };
            let term = if matches!(value, ObjectiveValue::NegInfinity) {
                let minus_one = ctx.solver.int_const_bigint(&BigInt::from(-1));
                match ctx.solver.try_mul(minus_one, oo) {
                    Ok(term) => term,
                    Err(_) => return 0,
                }
            } else {
                oo
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, oo_sort)
        }
    }
}

/// z3's AST of an unattained optimum `value + eps * epsilon` (z3 prints
/// `3 + -1*epsilon` for `maximize x` under `x < 3`): `epsilon` is a constant
/// of that name, as `oo` is.
fn build_epsilon_numeral(
    ctx: &mut Z3Context,
    value: &BigRational,
    eps: &BigRational,
    sort: &Sort,
) -> Z3_ast {
    let Some(epsilon) =
        super::terms::ffi_api_constant(ctx, &super::SymbolKey::String("epsilon".to_string()), sort)
    else {
        return 0;
    };
    let finite = ctx
        .solver
        .rational_const_bigint(value.numer(), value.denom());
    let coeff = ctx.solver.rational_const_bigint(eps.numer(), eps.denom());
    let Ok(scaled) = ctx.solver.try_mul(coeff, epsilon) else {
        return 0;
    };
    let Ok(sum) = ctx.solver.try_add(finite, scaled) else {
        return 0;
    };
    let ast = term_to_ast(ctx, sum);
    record_ast_sort(ctx, ast, sort.clone())
}

/// Build a finite numeral AST in the objective's sort.
fn build_finite_numeral(ctx: &mut Z3Context, r: &BigRational, sort: &Sort) -> Z3_ast {
    let (out_sort, term) = match sort {
        // Int optimum: a whole rational. Build an Int numeral from the integer
        // part (the executor guarantees Int optima are whole).
        Sort::Int => (Sort::Int, ctx.solver.int_const_bigint(&r.to_integer())),
        // Real optimum: build an exact rational numeral (numer/denom).
        Sort::Real => (
            Sort::Real,
            ctx.solver.rational_const_bigint(r.numer(), r.denom()),
        ),
        // BitVec optimum: the unsigned integer value, as a BV numeral of the
        // objective's width (matches Z3's `(x 7)` decimal report).
        Sort::BitVec(bv) => (
            sort.clone(),
            ctx.solver.bv_const_bigint(&r.to_integer(), bv.width),
        ),
        // Any other sort cannot be an objective (rejected at check time); be
        // defensive and emit an Int numeral of the integer part.
        _ => (Sort::Int, ctx.solver.int_const_bigint(&r.to_integer())),
    };
    let ast = term_to_ast(ctx, term);
    record_ast_sort(ctx, ast, out_sort)
}

/// Build an `Int` numeral AST for the exact integer `v` and record its sort.
fn int_numeral_ast(ctx: &mut Z3Context, v: &BigInt) -> Z3_ast {
    let term = ctx.solver.int_const_bigint(v);
    let ast = term_to_ast(ctx, term);
    record_ast_sort(ctx, ast, Sort::Int)
}

// ============================================================================
// Backtracking scopes (push / pop).
// ============================================================================

/// Create a backtracking point on the optimize context.
///
/// Scopes the hard assertions, objectives, and soft constraints: everything
/// added after this call is removed by the matching `Z3_optimize_pop`. The
/// engine's own `(push)` scopes the hard assertions, the arithmetic objectives,
/// and any soft constraints parsed via `Z3_optimize_from_string`; the API-level
/// soft records (from `Z3_optimize_assert_soft`) and tracked-assertion list are
/// restored by `Z3_optimize_pop` from the marker recorded here.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_push(c: Z3_context, o: Z3_optimize) {
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `o` is
    // null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in push".to_string());
                return;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_push") {
                return;
            }
            let marker = OptimizeScopeMarker {
                hard_len: opt.hard.len(),
                soft_len: opt.softs.len(),
                tracked_len: opt.tracked.len(),
                public_objective_len: opt.public_objectives.len(),
                objective_slot_len: opt.objective_slots.len(),
                parsed_soft_public_len: opt.parsed_soft_public_terms.len(),
            };
            if let Err(e) = ctx.solver.try_push() {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            opt.scope_markers.push(marker);
            // A new scope invalidates the prior check's artefacts.
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
        });
        // SAFETY: the guard has returned; see `finish_optimize_operation`.
        finish_optimize_operation(c, o);
    }
}

/// Backtrack one level on the optimize context.
///
/// Restores the hard assertions, objectives, and soft constraints to the state
/// at the matching `Z3_optimize_push`. Popping more than was pushed is rejected
/// with `Z3_EXCEPTION` (scope underflow) and leaves the handle unchanged.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_pop(c: Z3_context, o: Z3_optimize) {
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `o` is
    // null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in pop".to_string());
                return;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_pop") {
                return;
            }
            let Some(marker) = opt.scope_markers.pop() else {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(
                    "Z3_optimize_pop: scope underflow (pop with no matching push)".to_string(),
                );
                return;
            };
            if let Err(e) = ctx.solver.try_pop() {
                // The engine pop failed: keep the marker so the handle stays
                // consistent with the (unchanged) engine scope stack.
                opt.scope_markers.push(marker);
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            // Restore the API-level mirrors the engine scope does not cover.
            opt.hard.truncate(marker.hard_len);
            opt.softs.truncate(marker.soft_len);
            ctx.solver.truncate_soft_constraints(marker.soft_len);
            opt.tracked.truncate(marker.tracked_len);
            opt.public_objectives.truncate(marker.public_objective_len);
            opt.objective_senses.truncate(marker.public_objective_len);
            opt.objective_slots.truncate(marker.objective_slot_len);
            opt.parsed_soft_public_terms
                .truncate(marker.parsed_soft_public_len);
            // The popped scope's model / core no longer apply.
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
        });
        // SAFETY: the guard has returned; see `finish_optimize_operation`.
        finish_optimize_operation(c, o);
    }
}

// ============================================================================
// Tracked assertions + unsat core.
// ============================================================================

/// Assert a tracked hard constraint `a`, associated with the tracking literal
/// `t`.
///
/// Exactly z3's encoding: the hard constraint is `t => a` and `t` is an
/// assumption of every check. AY has no check-time assumptions on its
/// Optimize path, so `t` is asserted as well; `t => a` with `t` is the same
/// problem, so the verdict and optima are z3's (asserting `a` alone, as AY did,
/// answered `sat` when another hard constraint refutes `t`). Every tracking
/// literal is therefore part of each check, and the full set of them is a
/// sound unsat core ([`Z3_optimize_get_unsat_core`]).
///
/// # Safety
/// `c` must be a valid context pointer; `o` a valid optimize handle; `a`/`t`
/// u64 AST handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_assert_and_track(
    c: Z3_context,
    o: Z3_optimize,
    a: Z3_ast,
    t: Z3_ast,
) {
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `o` is
    // null-checked via `as_mut`; `a`/`t` are authenticated below.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in assert_and_track".to_string());
                return;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_assert_and_track") {
                return;
            }
            let a_term =
                require_term_ast_or_return!(ctx, a, "Z3_optimize_assert_and_track", "formula");
            let t_term = require_term_ast_or_return!(
                ctx,
                t,
                "Z3_optimize_assert_and_track",
                "tracking literal",
            );
            // The tracking literal must be Boolean (z3 requires a Boolean atom).
            if ctx.solver.term_sort(t_term) != Sort::Bool {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_optimize_assert_and_track: tracking literal must be Boolean".to_string(),
                );
                return;
            }
            // `t => a` as the hard constraint (validates `a`'s Bool sort), and
            // `t` as the check's assumption.
            let hard = match ctx.solver.try_implies(t_term, a_term) {
                Ok(term) => term,
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    return;
                }
            };
            for term in [hard, t_term] {
                if let Err(e) = ctx.solver.try_assert_term(term) {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    return;
                }
            }
            opt.hard.push(hard);
            opt.tracked.push((t_term, a_term));
            opt.clear_check_artifacts();
            release_optimize_adopted_definitions(ctx, opt);
            ctx.last_error = Z3_OK;
        });
        // SAFETY: the guard has returned; see `finish_optimize_operation`.
        finish_optimize_operation(c, o);
    }
}

/// Retrieve the unsat core of the last `Z3_optimize_check`.
///
/// The core is every tracking literal of that check: each is asserted with its
/// `t => a` (see [`Z3_optimize_assert_and_track`]), so the hard constraints
/// together with all of them are unsatisfiable exactly when the check was
/// unsat. That core is sound, though not minimal. The empty core AY used to
/// return claimed the untracked hard constraints alone were unsatisfiable,
/// which is false whenever a tracked assertion takes part (z3: `[p1, p3]`).
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_unsat_core(
    c: Z3_context,
    o: Z3_optimize,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let asts = match o.as_ref() {
                Some(opt) if opt.last_check_outcome == Some(OptimizeCheckOutcome::Unsat) => {
                    match &opt.last_unsat_core {
                        Some(core) => core
                            .iter()
                            .copied()
                            .map(|term| term_to_ast(ctx, term))
                            .collect(),
                        None => Vec::new(),
                    }
                }
                Some(_) => Vec::new(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null Z3_optimize handle in get_unsat_core".to_string());
                    Vec::new()
                }
            };
            cache_ast_vector(ctx, asts)
        })
    }
}

// ============================================================================
// Objectives / assertions introspection.
// ============================================================================

/// Return the registered objectives as an AST vector (the `(maximize ...)` /
/// `(minimize ...)` argument expressions, in declaration order).
///
/// DIVERGENCE FROM Z3: z3 normalizes every objective to a MINIMIZATION objective
/// (negating a `maximize`) and renders a MaxSAT objective as a pseudo-Boolean
/// sum. AY returns the objective terms EXACTLY as registered (the real objective
/// expressions) — honest, never a fabricated normalized form.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_objectives(
    c: Z3_context,
    o: Z3_optimize,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(opt) = o.as_ref() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in get_objectives".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            let n = ctx.solver.num_objectives();
            if !ctx.optimize_engine_displaced
                && ptr::eq(ctx.optimize_engine_owner, ptr::from_ref(opt))
                && opt.public_objectives.len() != n
            {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(
                    "Z3_optimize_get_objectives: public objective metadata is not aligned"
                        .to_string(),
                );
                return cache_ast_vector(ctx, Vec::new());
            }
            let items = opt.public_objectives.clone();
            let mut asts = Vec::with_capacity(items.len());
            for term in items {
                let ast = term_to_ast(ctx, term);
                let sort = public_ast_sort(ctx, ast, term);
                let ast = record_ast_sort(ctx, ast, sort);
                asts.push(ast);
            }
            ctx.last_error = Z3_OK;
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Return the hard assertions on the optimization context as an AST vector.
///
/// Includes constraints added via `Z3_optimize_assert`, the tracked assertions
/// from `Z3_optimize_assert_and_track`, and anything parsed via
/// `Z3_optimize_from_string`/`_from_file` — the clean user/parsed constraint set
/// (never the engine's internal MaxSMT relaxation clauses). Soft constraints and
/// objectives are NOT included (they are separate; see
/// `Z3_optimize_get_objectives`).
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_assertions(
    c: Z3_context,
    o: Z3_optimize,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let asts = match o.as_ref() {
                Some(opt) => opt
                    .hard
                    .iter()
                    .copied()
                    .map(|term| term_to_ast(ctx, term))
                    .collect(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null Z3_optimize handle in get_assertions".to_string());
                    Vec::new()
                }
            };
            cache_ast_vector(ctx, asts)
        })
    }
}

// ============================================================================
// Bound-as-vector (Z3's [a, b, c] = a*infinity + b + c*epsilon rep).
// ============================================================================

/// Get the lower bound of objective `idx` as a length-3 numeral vector.
///
/// The vector `[a, b, c]` encodes `a*infinity + b + c*epsilon` (z3's rep). AY
/// computes EXACT, ATTAINED optima, so:
/// - finite optimum `v` → `[0, v, 0]` (`v` an exact numeral in the objective's
///   sort);
/// - unbounded `maximize` (`+oo`) → `[1, 0, 0]`; unbounded `minimize` (`-oo`) →
///   `[-1, 0, 0]`.
///
/// The epsilon coefficient `c` is always `0`: AY reports the attained optimum,
/// never a strict `v - epsilon` sup (honest — it does not fabricate an
/// infinitesimal it did not compute). Returns an EMPTY vector (not a fabricated
/// bound) when no optimum is available (last check not SAT) and sets
/// `Z3_INVALID_ARG` for an out-of-range `idx`.
///
/// See [`Z3_optimize_get_lower`] for the scalar form.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_lower_as_vector(
    c: Z3_context,
    o: Z3_optimize,
    idx: c_uint,
) -> Z3_ast_vector {
    // SAFETY: the caller supplies live context and optimize handles;
    // `optimize_get_objective_vector` null-checks them and bounds-checks `idx`.
    unsafe { optimize_get_objective_vector(c, o, idx) }
}

/// Get the upper bound of objective `idx` as a length-3 numeral vector.
///
/// Identical to [`Z3_optimize_get_lower_as_vector`]: AY's optimum is exact, so
/// lower and upper coincide.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_upper_as_vector(
    c: Z3_context,
    o: Z3_optimize,
    idx: c_uint,
) -> Z3_ast_vector {
    // SAFETY: the caller supplies live context and optimize handles;
    // `optimize_get_objective_vector` null-checks them and bounds-checks `idx`.
    unsafe { optimize_get_objective_vector(c, o, idx) }
}

/// Shared implementation of `get_lower_as_vector` / `get_upper_as_vector`.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
unsafe fn optimize_get_objective_vector(
    c: Z3_context,
    o: Z3_optimize,
    idx: c_uint,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(opt) = o.as_ref() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("null Z3_optimize handle in get_lower/upper_as_vector".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            let idx = match opt.objective_slots.get(idx as usize) {
                Some(ObjectiveSlot::Arith(idx)) => *idx,
                _ => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!(
                        "Z3_optimize_get_lower/upper_as_vector: objective index {idx} is not \
                         an arithmetic objective"
                    ));
                    return cache_ast_vector(ctx, Vec::new());
                }
            };
            if opt.last_check_outcome != Some(OptimizeCheckOutcome::Sat) {
                ctx.last_error = Z3_OK;
                return cache_ast_vector(ctx, Vec::new());
            }
            let epsilon = opt.last_objective_epsilons.get(idx).cloned().flatten();
            let (sort, value) = match opt.last_objective_values.get(idx).cloned() {
                Some((Some(sort), Some(value))) => (sort, Some(value)),
                Some((Some(sort), None)) if epsilon.is_some() => (sort, None),
                _ => {
                    // No optimum available (last check not SAT): honest empty vector.
                    ctx.last_error = Z3_OK;
                    return cache_ast_vector(ctx, Vec::new());
                }
            };
            ctx.last_error = Z3_OK;
            // Decompose into (infinity coeff a, finite b, epsilon coeff c).
            let (a, finite, eps) = match (value, epsilon) {
                (Some(ObjectiveValue::Finite(r)), _) => (BigInt::from(0), Some(r), BigInt::from(0)),
                (Some(ObjectiveValue::PosInfinity), _) => (BigInt::from(1), None, BigInt::from(0)),
                (Some(ObjectiveValue::NegInfinity), _) => (BigInt::from(-1), None, BigInt::from(0)),
                (None, Some((value, eps))) if eps.is_integer() => {
                    (BigInt::from(0), Some(value), eps.to_integer())
                }
                _ => return cache_ast_vector(ctx, Vec::new()),
            };
            let a_ast = int_numeral_ast(ctx, &a);
            let b_ast = match &finite {
                Some(r) => build_finite_numeral(ctx, r, &sort),
                None => int_numeral_ast(ctx, &BigInt::from(0)),
            };
            let c_ast = int_numeral_ast(ctx, &eps);
            cache_ast_vector(ctx, vec![a_ast, b_ast, c_ast])
        })
    }
}

// ============================================================================
// Reason-unknown / statistics.
// ============================================================================

/// Retrieve the reason-unknown string from the last `Z3_optimize_check`.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_reason_unknown(
    c: Z3_context,
    o: Z3_optimize,
) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let reason = match o.as_ref() {
                Some(opt) if opt.last_check_outcome == Some(OptimizeCheckOutcome::Unknown) => {
                    opt.last_reason_unknown.clone().unwrap_or_default()
                }
                Some(_) => String::new(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg =
                        Some("null Z3_optimize handle in get_reason_unknown".to_string());
                    String::new()
                }
            };
            cache_string(ctx, reason)
        })
    }
}

/// Retrieve statistics from the last `Z3_optimize_check`.
///
/// Returns a `Z3_stats` handle over a snapshot of the executor's REAL counters
/// for that check (reusing the same machinery as `Z3_solver_get_statistics`). If
/// no check has run, the snapshot is empty (all-zero stats).
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_statistics(c: Z3_context, o: Z3_optimize) -> Z3_stats {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let stats = match o.as_ref() {
                Some(opt) => opt.last_statistics.clone().unwrap_or_default(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null Z3_optimize handle in get_statistics".to_string());
                    return ptr::null_mut();
                }
            };
            let entries = flatten_statistics(&stats);
            let handle = Box::into_raw(Box::new(StatsHandle { entries }));
            ctx.stats_handle_cache.push(handle);
            ctx.last_error = Z3_OK;
            handle
        })
    }
}

// ============================================================================
// SMT-LIB2 parsing into the optimize context.
// ============================================================================

/// Refuse an Optimize parse while Solver handles share the context: parsed
/// content is not recorded on the handle, so it could not be replayed after a
/// Solver check reset the engine (`restore_optimize_engine`).
fn parse_blocked_by_solver_handles(ctx: &mut Z3Context, operation: &str) -> bool {
    if !ctx.has_solver_family_handles() {
        return false;
    }
    ctx.last_error = Z3_INVALID_USAGE;
    ctx.error_msg = Some(format!(
        "{operation}: parsing into an Optimize handle whose context also has Solver \
         handles is unsupported; use a separate Z3_context"
    ));
    true
}

/// The non-mutating preflight of an Optimize parse: the text's commands, or
/// `None` with the context error set.
fn optimize_parse_preflight(
    ctx: &mut Z3Context,
    input: &str,
    operation: &str,
) -> Option<Vec<Command>> {
    // Fail-close reserved `map[...]` symbol capture (measured wrong-verdict
    // channel through the core elaborator) — see `smtlib2_reserved_error`.
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
            "{operation}: push/pop/reset commands are not supported inside an Optimize parse transaction"
        ));
        return None;
    }
    Some(commands)
}

/// The bound parse of an Optimize text (see `parse_binding`): `None` when it
/// decided the text (installed, or refused with the context error set), and
/// `Some(())` when the text is outside the rebinding fragment and may take the
/// legacy global parse.
fn parse_optimize_bound(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    input: &str,
    commands: &[Command],
    operation: &str,
) -> Option<()> {
    // z3 parses each Optimize text in a fresh command context whose names
    // denote the context's declarations of the same name and signature
    // (measured: a parsed `(declare-fun a () Int)` was a second `a`, so the
    // API's `a == 0` never constrained it: `sat [a = 0, a = 3]` where z3
    // answers `unsat`). The bound parse installs the text's formulas through
    // the handle's own records, so the handle stays replayable.
    let scope = super::parse_binding::ParseScope {
        objectives: true,
        ..super::parse_binding::ParseScope::default()
    };
    match super::parse_binding::bound_parse(ctx, input, &scope) {
        super::parse_binding::BoundParse::Parsed(content) => {
            install_parsed_optimize_content(ctx, opt, content, operation);
            return None;
        }
        super::parse_binding::BoundParse::Failed(reason) => {
            ctx.last_error = super::Z3_PARSER_ERROR;
            ctx.error_msg = Some(format!("{operation}: {reason}"));
            return None;
        }
        super::parse_binding::BoundParse::ScopeLost(reason) => {
            opt.terminal_error = Some(format!("{operation}: {reason}"));
            ctx.poison_decision_engine(format!("{operation}: {reason}"));
            return None;
        }
        super::parse_binding::BoundParse::Ineligible(reason) => {
            if let Some(name) = super::solver::global_parse_collision(ctx, commands) {
                ctx.last_error = super::Z3_PARSER_ERROR;
                ctx.error_msg = Some(format!(
                    "{operation}: the text declares '{name}', which this context already \
                     declares, and AY cannot bind the text's '{name}' to it in a text with \
                     {reason}"
                ));
                return None;
            }
        }
    }

    Some(())
}

/// Execute one Optimize parse as an atomic semantic transaction.
///
/// A hidden solver scope commits successful parsed assertions/objectives/softs
/// by remaining below all user-visible scopes. On execution failure it rolls
/// those semantic lists back. Because options can be unscoped, any late
/// execution failure permanently poisons the handle even after a successful
/// scope rollback; no partially changed configuration can later admit a result.
/// Parsing is rejected while a user-visible scope is open, ensuring the hidden
/// scope can never sit above and corrupt a user marker.
fn parse_optimize_transaction(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    input: &str,
    operation: &str,
) {
    if !optimize_handle_is_usable(ctx, opt, operation) {
        return;
    }
    let Some(commands) = optimize_parse_preflight(ctx, input, operation) else {
        return;
    };

    if parse_optimize_bound(ctx, opt, input, &commands, operation).is_none() {
        return;
    }
    // The legacy global parse: its content is not recorded on the handle.
    if parse_blocked_by_solver_handles(ctx, operation) {
        return;
    }
    // Successful parse transactions intentionally retain a hidden engine
    // scope as their commit boundary. Such a scope must remain below every
    // user-visible scope; opening one after a user push would make the next
    // user pop remove the hidden scope while consuming the user's marker,
    // diverging handle and engine state.
    if !opt.scope_markers.is_empty() {
        ctx.last_error = Z3_INVALID_USAGE;
        ctx.error_msg = Some(format!(
            "{operation}: parsing while an Optimize user scope is open is unsupported; pop all user scopes before parsing"
        ));
        return;
    }

    if let Err(e) = ctx.solver.try_push() {
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(format!("{operation}: cannot open parse transaction: {e}"));
        return;
    }
    opt.clear_check_artifacts();
    opt.terminal_error = Some(format!(
        "{operation}: parse transaction was interrupted before completion"
    ));

    let parsed = ctx
        .solver
        .parse_smtlib2_z3_5(input)
        .map_err(|error| error.to_string())
        .and_then(|batch| {
            super::retain_parsed_finite_set_batch(ctx, batch)
                .map_err(|error| format!("public FiniteSet metadata retention failed: {error}"))
        });
    match parsed {
        Ok(retained) => {
            opt.hard.extend(retained.assertions);
            opt.parsed_soft_public_terms
                .extend(retained.soft_constraints);
            opt.objective_senses
                .extend(retained.objectives.iter().map(|_| None));
            opt.public_objectives.extend(retained.objectives);
            opt.replay_blocker = Some(format!(
                "{operation} installed SMT-LIB content the handle cannot replay"
            ));
            opt.terminal_error = None;
            ctx.last_error = Z3_OK;
            ctx.error_msg = None;
        }
        Err(error) => {
            let mut reason = format!("{operation}: parse execution failed: {error}");
            if let Err(rollback) = ctx.solver.try_pop() {
                reason.push_str(&format!("; semantic rollback also failed: {rollback}"));
            }
            // Even when the semantic scope rolled back, options are not scoped.
            // Permanently fail closed instead of later solving a possibly
            // configuration-shifted or otherwise partially executed script.
            opt.terminal_error = Some(reason.clone());
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(reason);
        }
    }
}

/// The objective index of the soft-constraint group `group`, registering it
/// on first use.
fn soft_slot(opt: &mut OptimizeHandle, group: Option<String>) -> usize {
    let slot = ObjectiveSlot::Soft(group);
    if let Some(index) = opt.objective_slots.iter().position(|s| *s == slot) {
        return index;
    }
    opt.objective_slots.push(slot);
    opt.objective_slots.len() - 1
}

/// Install the formulas of a bound Optimize parse exactly as the API calls
/// install them (`Z3_optimize_assert`, `_assert_soft`, `_maximize`,
/// `_minimize`), recorded on the handle so it replays them.
fn install_parsed_optimize_content(
    ctx: &mut Z3Context,
    opt: &mut OptimizeHandle,
    content: super::parse_binding::ParsedContent,
    operation: &str,
) {
    for term in content.assertions {
        if let Err(e) = ctx.solver.try_assert_term(term) {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{operation}: {e}"));
            return;
        }
        opt.hard.push(term);
    }
    for (term, weight, group) in content.softs {
        if let Err(e) = ctx.solver.assert_soft(term, weight, None) {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{operation}: {e}"));
            return;
        }
        soft_slot(opt, group.clone());
        opt.softs.push(SoftRecord {
            term,
            weight,
            group,
        });
    }
    for (term, sense) in content.objectives {
        match sense {
            ObjectiveSense::Maximize => ctx.solver.maximize(term),
            ObjectiveSense::Minimize => ctx.solver.minimize(term),
        };
        opt.public_objectives.push(term);
        opt.objective_senses.push(Some(sense));
        opt.objective_slots
            .push(ObjectiveSlot::Arith(opt.public_objectives.len() - 1));
    }
    opt.clear_check_artifacts();
    release_optimize_adopted_definitions(ctx, opt);
    ctx.last_error = Z3_OK;
    ctx.error_msg = None;
}

/// Parse an SMT-LIB2 string (with `(assert ...)`, `(assert-soft ...)`,
/// `(maximize ...)`, `(minimize ...)`) into the optimization context.
///
/// Declarations, hard assertions, soft constraints, and objectives are added to
/// the engine (query commands like `(check-sat)` are ignored — call
/// `Z3_optimize_check` afterward). Parse/execution errors set `Z3_EXCEPTION`.
///
/// # Safety
/// `c` must be a valid context pointer; `o` a valid optimize handle; `s` a
/// null-terminated C string (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_from_string(c: Z3_context, o: Z3_optimize, s: Z3_string) {
    // Extract the string outside the guard (raw-pointer deref).
    let input = if s.is_null() {
        None
    } else {
        // SAFETY: the caller's contract guarantees `s`, when non-null, is a valid
        // null-terminated C string owned by the caller for this call's duration.
        Some(unsafe { ffi_read_bounded_parser_text(s) })
    };
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in from_string".to_string());
                return;
            };
            let input = match input.as_ref() {
                None => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some("Z3_optimize_from_string: null input string".to_string());
                    return;
                }
                Some(Ok(input)) => input,
                Some(Err(error)) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_optimize_from_string: {error}"));
                    return;
                }
            };
            parse_optimize_transaction(ctx, opt, input, "Z3_optimize_from_string");
        });
        // SAFETY: the guard has returned; see `finish_optimize_operation`.
        finish_optimize_operation(c, o);
    }
}

/// Parse an SMT-LIB2 file into the optimization context (see
/// [`Z3_optimize_from_string`]). A file-read failure sets `Z3_FILE_ACCESS_ERROR`.
///
/// # Safety
/// `c` must be a valid context pointer; `o` a valid optimize handle; `s` a
/// null-terminated path C string (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_from_file(c: Z3_context, o: Z3_optimize, s: Z3_string) {
    let path: Option<String> = if s.is_null() {
        None
    } else {
        // SAFETY: caller guarantees a valid null-terminated C string when non-null.
        unsafe { ffi_read_bounded_text(s) }.ok()
    };
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in from_file".to_string());
                return;
            };
            let Some(path) = path.as_deref() else {
                ctx.last_error = Z3_FILE_ACCESS_ERROR;
                ctx.error_msg = Some("Z3_optimize_from_file: null/invalid path".to_string());
                return;
            };
            let contents = match ffi_read_bounded_parser_file(path) {
                Ok(v) => v,
                Err(e) => {
                    ctx.last_error = Z3_FILE_ACCESS_ERROR;
                    ctx.error_msg = Some(format!("Z3_optimize_from_file: {e}"));
                    return;
                }
            };
            parse_optimize_transaction(ctx, opt, &contents, "Z3_optimize_from_file");
        });
        // SAFETY: the guard has returned; see `finish_optimize_operation`.
        finish_optimize_operation(c, o);
    }
}

// ============================================================================
// Params / help / param-descriptors.
// ============================================================================

/// Set parameters on the optimization context.
///
/// As `Z3_solver_set_params`, AY honors `timeout` (uint, ms) and
/// `produce-proofs` (bool) for this handle's own checks, and the
/// `priority`/`opt.priority` objective policy (`lex`, `box`, or `pareto`).
/// Priority is validated before any parameter is applied, so an invalid value
/// cannot leave a partially updated optimization configuration.
///
/// # Safety
/// `c` must be a valid context pointer; `o` a valid optimize handle; `p` a valid
/// params handle (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_set_params(c: Z3_context, o: Z3_optimize, p: Z3_params) {
    if c.is_null() || p.is_null() {
        return;
    }
    // SAFETY: `p` was null-checked and is a params handle kept alive by the
    // context's `params_cache`; single-threaded per context, so no race.
    let params_owned: Vec<(String, String)> = unsafe { &(*p).params }.clone();
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `o` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in set_params".to_string());
                return;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_set_params") {
                return;
            }
            let priority = params_owned.iter().rev().find_map(|(key, value)| {
                let key = key.trim().trim_start_matches(':');
                matches!(key, "priority" | "opt.priority").then_some(value.as_str())
            });
            if let Some(value) = priority {
                if !matches!(value, "lex" | "box" | "pareto") {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!(
                        "Z3_optimize_set_params: invalid priority '{value}' (expected lex, box, or pareto)"
                    ));
                    return;
                }
                if let Err(e) = ctx.solver.try_set_option(":opt.priority", value) {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_optimize_set_params: {e}"));
                    return;
                }
            }
            // `timeout` and proof production belong to THIS handle and are
            // applied for its own checks only (libz3 5.1.0: an Optimize's
            // `timeout` of 1 ms leaves a later Solver's pigeonhole `unsat`).
            opt.params.record(&params_owned);
            // Parameters govern the next decision transaction. Retire copied
            // result artifacts so no caller can mistake a pre-configuration
            // snapshot for the outcome of the newly configured optimizer.
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
            ctx.error_msg = None;
        });
        // SAFETY: the guard has returned; see `finish_optimize_operation`.
        finish_optimize_operation(c, o);
    }
}

/// Return a human-readable description of the parameters the optimize engine
/// accepts. Honest: it documents exactly what AY honors.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_help(c: Z3_context, o: Z3_optimize) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if o.as_ref().is_none() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in get_help".to_string());
            }
            let help = "\
Parameters honored by the AY optimize engine:
  timeout (unsigned int)  solve timeout in milliseconds (0 = no limit)
  produce_proofs (bool)   enable proof production for the solve
  priority (string)       objective combination: lex, box, or pareto
Other z3 optimize parameters are accepted for API compatibility but ignored.\n";
            cache_string(ctx, help.to_string())
        })
    }
}

/// Return the parameter-descriptor set the optimize engine recognizes.
///
/// A REAL, queryable list (name + `Z3_param_kind` + documentation) of the
/// parameters AY honors — never a fake/empty stub disguised as z3's full set.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_param_descrs(
    c: Z3_context,
    o: Z3_optimize,
) -> Z3_param_descrs {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if o.as_ref().is_none() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in get_param_descrs".to_string());
            }
            let entries = vec![
                ParamDescr {
                    name: "timeout".to_string(),
                    kind: Z3_PK_UINT,
                    doc: "solve timeout in milliseconds (0 = no limit)".to_string(),
                },
                ParamDescr {
                    name: "produce_proofs".to_string(),
                    kind: Z3_PK_BOOL,
                    doc: "enable proof production for the solve".to_string(),
                },
                ParamDescr {
                    name: "priority".to_string(),
                    kind: Z3_PK_STRING,
                    doc: "objective combination: 'lex' (default), 'box', or \
                          'pareto' — honored via opt.priority (pareto/box \
                          enumerate via repeated check())"
                        .to_string(),
                },
            ];
            let handle = Box::into_raw(Box::new(ParamDescrsHandle { entries }));
            ctx.param_descrs_cache.push(handle);
            handle
        })
    }
}

// ============================================================================
// Honest deferrals (documented no-ops — never fake state).
// ============================================================================

/// Provide an initial-value hint for a variable. HONEST NO-OP.
///
/// AY's optimizer does not consume initialization hints. A hint only biases
/// search order in z3 — it never changes the reported optimum — so ignoring it
/// is semantically safe and z3-consistent (the same optimum is still found).
/// Documented rather than faked.
///
/// # Safety
/// Pointers must be valid; arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_set_initial_value(
    _c: Z3_context,
    _o: Z3_optimize,
    _v: Z3_ast,
    _val: Z3_ast,
) {
}

/// Register a model-event handler. HONEST NO-OP.
///
/// AY does not expose an incremental new-model callback hook, so no handler is
/// invoked. The FINAL optimal model remains available via `Z3_optimize_get_model`
/// after `Z3_optimize_check`. Documented rather than faked (no fabricated
/// callback invocations).
///
/// # Safety
/// Pointers must be valid; arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_register_model_eh(
    _c: Z3_context,
    _o: Z3_optimize,
    _m: Z3_model,
    _ctx: *mut c_void,
    _model_eh: Option<unsafe extern "C" fn(*mut c_void)>,
) {
}

// ============================================================================
// Z3_param_descrs accessors (backing Z3_optimize_get_param_descrs).
// ============================================================================

/// Increment param-descrs ref count (bookkeeping-only no-op; arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_param_descrs_inc_ref(_c: Z3_context, _p: Z3_param_descrs) {}

/// Decrement param-descrs ref count (bookkeeping-only no-op; arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_param_descrs_dec_ref(_c: Z3_context, _p: Z3_param_descrs) {}

/// Number of parameter descriptors in the set.
///
/// # Safety
/// `c` must be a valid context pointer; `p` a valid param-descrs handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_param_descrs_size(c: Z3_context, p: Z3_param_descrs) -> c_uint {
    // SAFETY: `ffi_guard_uint` handles null `c` and catches panics; `p` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match p.as_ref() {
            Some(h) => h.entries.len() as c_uint,
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_param_descrs handle in size".to_string());
                0
            }
        })
    }
}

/// Name (as a `Z3_symbol`) of the `i`'th parameter descriptor.
///
/// # Safety
/// `c` must be a valid context pointer; `p` a valid param-descrs handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_param_descrs_get_name(
    c: Z3_context,
    p: Z3_param_descrs,
    i: c_uint,
) -> Z3_symbol {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `p` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let name = match p.as_ref().and_then(|h| h.entries.get(i as usize)) {
                Some(d) => d.name.clone(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg =
                        Some("Z3_param_descrs_get_name: index out of range".to_string());
                    return ptr::null_mut();
                }
            };
            cache_symbol(ctx, name)
        })
    }
}

/// Kind (`Z3_param_kind`) of the parameter named `n`, or `Z3_PK_INVALID` if the
/// set has no such parameter.
///
/// # Safety
/// `c` must be a valid context pointer; `p` a valid param-descrs handle; `n` a
/// valid symbol handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_param_descrs_get_kind(
    c: Z3_context,
    p: Z3_param_descrs,
    n: Z3_symbol,
) -> c_uint {
    // Read the queried name outside the guard (raw-pointer deref).
    let query: Option<String> = if n.is_null() {
        None
    } else {
        // SAFETY: `n`, when non-null, is a symbol handle kept alive by the
        // context's `symbol_cache`; single-threaded per context, so no race.
        Some(unsafe { &*n }.display_name())
    };
    // SAFETY: `ffi_guard_uint` handles null `c` and catches panics; `p` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_uint(c, Z3_PK_INVALID, |ctx| {
            let Some(h) = p.as_ref() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_param_descrs handle in get_kind".to_string());
                return Z3_PK_INVALID;
            };
            match query
                .as_deref()
                .and_then(|q| h.entries.iter().find(|d| d.name == q))
            {
                Some(d) => d.kind,
                None => Z3_PK_INVALID,
            }
        })
    }
}

/// Documentation string for the parameter named `s`, or empty if not present.
///
/// # Safety
/// `c` must be a valid context pointer; `p` a valid param-descrs handle; `s` a
/// valid symbol handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_param_descrs_get_documentation(
    c: Z3_context,
    p: Z3_param_descrs,
    s: Z3_symbol,
) -> Z3_string {
    let query: Option<String> = if s.is_null() {
        None
    } else {
        // SAFETY: `s`, when non-null, is a symbol handle kept alive by the
        // context's `symbol_cache`; single-threaded per context, so no race.
        Some(unsafe { &*s }.display_name())
    };
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics; `p` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let doc = p
                .as_ref()
                .and_then(|h| {
                    query
                        .as_deref()
                        .and_then(|q| h.entries.iter().find(|d| d.name == q))
                })
                .map(|d| d.doc.clone())
                .unwrap_or_default();
            cache_string(ctx, doc)
        })
    }
}

/// Render the parameter-descriptor set as a string (one `name (kind) : doc` line
/// per parameter).
///
/// # Safety
/// `c` must be a valid context pointer; `p` a valid param-descrs handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_param_descrs_to_string(c: Z3_context, p: Z3_param_descrs) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics; `p` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let mut out = String::from("(param_descrs\n");
            if let Some(h) = p.as_ref() {
                for d in &h.entries {
                    let kind = match d.kind {
                        Z3_PK_UINT => "uint",
                        Z3_PK_BOOL => "bool",
                        Z3_PK_STRING => "string",
                        _ => "other",
                    };
                    out.push_str(&format!("  {} ({}) : {}\n", d.name, kind, d.doc));
                }
            }
            out.push(')');
            cache_string(ctx, out)
        })
    }
}

#[cfg(test)]
#[path = "optimize_ffi_tests.rs"]
mod optimize_ffi_tests;
