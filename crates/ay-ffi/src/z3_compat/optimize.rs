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
//! AY does NOT jointly optimize arithmetic objectives and soft constraints in a
//! single solve. `Z3_optimize_check` routes as follows:
//!
//! - objectives and soft constraints both registered → return honest
//!   `Z3_L_UNDEF`/`Z3_INVALID_ARG`; AY does not yet implement Z3's joint priority
//!   semantics and never presents a partial optimization as the joint optimum.
//! - objectives only → run the OBJECTIVE optimizer.
//! - no objectives, softs present → run MaxSMT (`check_sat_max`).
//! - neither → plain `check_sat`.
//!
//! This restriction is documented rather than faked: a wrong joint optimum is
//! never reported. Callers needing both should split the problems.
//!
//! # Handle model
//!
//! A `Z3_optimize` is a context-arena-owned handle. UNLIKE `Z3_solver` — whose
//! handles each own an independent replayable assertion stack (see
//! [`super::Z3SolverHandle`]) — an optimize handle still ALIASES the context's
//! single `ay_dpll::api::Solver` ENGINE STATE. AY therefore ENFORCES one
//! optimize handle per context and rejects mixing Optimize with solver/global
//! parser semantic state (`Z3_INVALID_USAGE` + null constructor result). This is
//! a deliberate fail-closed compatibility frontier until Optimize gains exact
//! per-handle replay; silent union/wipe behavior is never allowed. Fixedpoint
//! handles may coexist because they only read the shared term arena and solve in
//! an independent CHC engine. `inc_ref`/`dec_ref` are bookkeeping-only no-ops;
//! the handle lives until `Z3_del_context` frees the arena.
//!
//! Because the optimize handle aliases the one engine, soft constraints are
//! scoped to that engine's `soft_constraints` list. A program that wants a
//! fresh optimization problem should use a fresh context (the typical z3py
//! pattern is one `Optimize()` per `Context`).
//!
//! # Model capture
//!
//! `Solver::check_sat_max` transactionally restores the user's hard formula and
//! then revalidates the selected optimal model. `Z3_optimize_check` captures
//! exactly that consumer-accepted witness. It never re-solves a weaker set of
//! satisfied softs, which could select a different model and sever the model from
//! the certified optimum/accounting.
//!
use std::ffi::{c_int, c_uint, c_void, CStr};
use std::ptr;

use ay_dpll::api::{MaxSmtStatus, ObjectiveValue, Sort, Term};
use ay_frontend::Command;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::{
    apply_supported_params, ast_to_term, cache_ast_vector, cache_string, cache_symbol,
    ffi_guard_ast, ffi_guard_const_ptr, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint,
    ffi_guard_void, flatten_statistics, record_ast_sort, term_to_ast, DecisionOwnerFamily,
    ModelHandle, OptimizeCheckOutcome, OptimizeHandle, OptimizeScopeMarker, ParamDescr,
    ParamDescrsHandle, SoftRecord, StatsHandle, Z3Context, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_model, Z3_optimize, Z3_param_descrs, Z3_params, Z3_stats, Z3_string, Z3_symbol,
    Z3_EXCEPTION, Z3_FILE_ACCESS_ERROR, Z3_INVALID_ARG, Z3_INVALID_USAGE, Z3_L_FALSE, Z3_L_TRUE,
    Z3_L_UNDEF, Z3_OK, Z3_PK_BOOL, Z3_PK_INVALID, Z3_PK_STRING, Z3_PK_UINT,
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
            if !ctx.optimize_handle_cache.is_empty() {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_mk_optimize: AY supports exactly one optimize handle per context; use a separate Z3_context"
                        .to_string(),
                );
                return ptr::null_mut();
            }
            if !ctx.claim_decision_owner(DecisionOwnerFamily::Optimize, "Z3_mk_optimize") {
                return ptr::null_mut();
            }
            let handle = Box::into_raw(Box::new(OptimizeHandle {
                _ctx: c,
                hard: Vec::new(),
                softs: Vec::new(),
                last_model: None,
                last_check_outcome: None,
                tracked: Vec::new(),
                scope_markers: Vec::new(),
                last_unsat_core: None,
                last_reason_unknown: None,
                last_statistics: None,
                terminal_error: None,
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
        false
    } else {
        true
    }
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
    // cannot cross the FFI boundary. `a` is a u64 AST handle (Copy), validated by `ast_to_term`.
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
            let term = ast_to_term(a);
            if let Err(e) = ctx.solver.try_assert_term(term) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            // Mirror onto the handle's clean assertion set (for get_assertions).
            opt.hard.push(term);
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
        });
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
/// Returns the index of the newly asserted soft constraint.
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
        match unsafe { CStr::from_ptr(weight) }.to_str() {
            Ok(s) => Some(s.to_string()),
            Err(_) => Some(String::new()), // non-UTF-8 → treated as invalid below
        }
    };
    let group: Option<String> = if id.is_null() {
        None
    } else {
        // SAFETY: `id`, when non-null, is a `SymbolHandle` produced by a prior `Z3_mk_*_symbol`
        // and kept alive in the context's `symbol_cache` for the context's lifetime. The Z3 C
        // API is single-threaded per context, so this shared read does not race.
        Some(unsafe { &*id }.display_name())
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
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

            let term = ast_to_term(a);
            match ctx.solver.assert_soft(term, w, group.as_deref()) {
                Ok(idx) => {
                    // Record the soft locally so `to_string` can render the
                    // handle's soft set. The exact witness itself is captured
                    // directly from the solver's admitted MaxSMT result. `idx`
                    // is the solver-side index; it
                    // equals `opt.softs.len()` because the optimize handle owns
                    // the only soft constraints on this solver.
                    opt.softs.push(SoftRecord {
                        term,
                        weight: w,
                        group: group.clone(),
                    });
                    opt.clear_check_artifacts();
                    ctx.last_error = Z3_OK;
                    idx as c_uint
                }
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    opt.softs.len() as c_uint
                }
            }
        })
    }
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
/// `num_assumptions` MUST be 0: neither AY's MaxSMT nor its objective entry
/// point threads check-time assumptions through the optimization loop. A
/// non-zero `num_assumptions` is rejected honestly with `Z3_L_UNDEF` and
/// `Z3_INVALID_ARG` on the context (we never silently ignore assumptions and
/// return a possibly-wrong optimum). Callers needing assumptions should encode
/// them as hard constraints via `Z3_optimize_assert`.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
/// `assumptions` must point to `num_assumptions` elements when `num_assumptions > 0`.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_check(
    c: Z3_context,
    o: Z3_optimize,
    num_assumptions: c_uint,
    _assumptions: *const Z3_ast,
) -> c_int {
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
                opt.last_reason_unknown = Some(reason);
                opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
                return Z3_L_UNDEF;
            }

            if let Some(reason) = opt.terminal_error.clone() {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(reason.clone());
                opt.last_reason_unknown = Some(reason);
                opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
                return Z3_L_UNDEF;
            }

            // Honest handling of assumptions: not threaded through optimization.
            if num_assumptions > 0 {
                let reason =
                    "Z3_optimize_check: assumptions are not supported by AY's optimization path; \
                     encode them as hard constraints via Z3_optimize_assert"
                        .to_string();
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(reason.clone());
                opt.last_reason_unknown = Some(reason);
                opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
                return Z3_L_UNDEF;
            }

            // Inject theory-internal background axioms (special-relation orders,
            // Char range invariants) so they constrain the optimization solve.
            // Unlike the plain-solver path this engine state is not reset per
            // check, so a repeated check may re-assert them — harmless (asserting
            // a Bool constraint twice is idempotent) and always sound (they only
            // add constraints over fresh predicates / bounded Char code points).
            // The Optimize engine state is incremental (asserted at
            // `Z3_optimize_assert` time), so check-time goal expansion is not
            // available here: the rec-def axioms are ALWAYS included (keeps
            // the sound definitional UNSAT power), and a SAT/optimum outcome
            // over any rec-f mention is demoted below.
            if let Err(e) = super::assert_background_axioms(ctx, true) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(e.clone());
                opt.last_reason_unknown = Some(e);
                opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
                return Z3_L_UNDEF;
            }

            let has_objectives = ctx.solver.num_objectives() > 0;
            let has_parsed_softs = ctx.solver.num_parsed_soft_constraints() > 0;
            let has_api_softs = ctx.solver.num_soft_constraints() > 0;
            if has_objectives && (has_parsed_softs || has_api_softs) {
                let reason = "Z3_optimize_check: joint arithmetic-objective + soft-constraint optimization is not implemented; split the problems".to_string();
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(reason.clone());
                opt.last_reason_unknown = Some(reason);
                opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
                return Z3_L_UNDEF;
            }

            // Route the solve. Three paths (see module docs):
            //   1. arithmetic objectives registered, OR (mutually exclusively)
            //      soft constraints parsed into the executor via
            //      `Z3_optimize_from_string`/`_from_file` → the executor's native
            //      `(check-sat)` dispatch for that single objective class. The
            //      mixed case was rejected above; executor dispatch also fails it
            //      closed as defense in depth.
            //   2. else API-level softs (from `Z3_optimize_assert_soft`) present
            //      → the weight-exact MaxSMT engine (`check_sat_max`).
            //   3. else a plain check-sat.
            let verdict = if has_objectives || has_parsed_softs {
                optimize_check_objectives(ctx, opt)
            } else {
                let result = match ctx.solver.check_sat_max() {
                    Ok(r) => r,
                    Err(e) => {
                        ctx.last_error = Z3_EXCEPTION;
                        ctx.error_msg = Some(format!("{e}"));
                        capture_check_diagnostics(ctx, opt, Z3_L_UNDEF);
                        return Z3_L_UNDEF;
                    }
                };
                match result.status {
                    MaxSmtStatus::Optimal => {
                        // Capture the exact model selected, restored, and
                        // revalidated by the MaxSMT transaction. An Optimal
                        // result without a consumer-admissible witness violates
                        // the boundary contract and must fail closed.
                        match ctx.solver.model_for_consumer() {
                            Some(model) => {
                                opt.last_model = Some(model.into_inner());
                                ctx.last_error = Z3_OK;
                                Z3_L_TRUE
                            }
                            None => {
                                ctx.last_error = Z3_EXCEPTION;
                                ctx.error_msg = Some(
                                    "MaxSMT optimum has no consumer-admissible witnessing model"
                                        .to_string(),
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
                }
            };

            capture_check_diagnostics(ctx, opt, verdict);
            // Transitive-closure SAT gate: the background axioms for a
            // `Z3_mk_transitive_closure` predicate are only PARTIAL (see
            // `verify_transitive_closure_model` in solver.rs), so a SAT here
            // could rest on an over-approximated TC. The optimize path has no
            // snapshot verifier wired, so it honestly reports unknown rather
            // than release an unverified SAT (never a fabricated verdict).
            if verdict == Z3_L_TRUE && !ctx.transitive_closure_regs.is_empty() {
                opt.last_reason_unknown = Some(
                    "transitive-closure model verification is not wired into the \
                     optimization path; refusing an unverified sat"
                        .to_string(),
                );
                // The backend model and objective values were captured before
                // this FFI trust gate. Downgrading SAT to UNKNOWN must revoke
                // their public authority while retaining the reason/statistics
                // for this completed query.
                opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
                return Z3_L_UNDEF;
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
            if verdict == Z3_L_TRUE && !ctx.rec_fun_defs.is_empty() {
                let mut scan: Vec<Term> = opt.hard.clone();
                scan.extend(opt.softs.iter().map(|s| s.term));
                for &(p, a) in &opt.tracked {
                    scan.push(p);
                    scan.push(a);
                }
                for idx in 0..ctx.solver.num_objectives() {
                    if let Some(t) = ctx.solver.objective_term(idx) {
                        scan.push(t);
                    }
                }
                let parsed_softs_present = ctx.solver.num_parsed_soft_constraints() > 0;
                if parsed_softs_present
                    || ctx.solver.contains_rec_fun_apps(&scan, &ctx.rec_fun_defs)
                {
                    opt.last_reason_unknown = Some(
                        "recursive definitions are not expanded on the Optimize path; \
                         optimum not certified"
                            .to_string(),
                    );
                    opt.record_check_outcome(OptimizeCheckOutcome::Unknown);
                    return Z3_L_UNDEF;
                }
            }
            verdict
        })
    }
}

/// Capture the per-check diagnostics into the optimize handle: the reason-unknown
/// string and the executor statistics snapshot.
///
/// UNSAT-CORE — HONEST DIVERGENCE FROM Z3: `Z3_optimize_get_unsat_core` returns
/// an EMPTY vector. AY's Optimize engine cannot extract a *participating-only*
/// core: it does not thread check-time assumptions through the optimization loop
/// (see `Z3_optimize_check`'s `num_assumptions == 0` requirement), the tracked
/// hard assertions are asserted UNCONDITIONALLY (so an assumption-gated core
/// would poison the optimum), and `Solver::reset` invalidates term handles — so
/// there is no sound way to compute which tracked literals actually participate.
/// Rather than return the FULL tracked set (which would include non-participating
/// literals — a WRONG core value per Z3's contract), we return an empty core.
/// `Z3_optimize_assert_and_track` still asserts its tracked constraint (so the
/// verdict/optimum are correct); only the participating-core extraction is
/// unsupported, and this is documented in `ay_z3_compat.h`. A future engine with
/// assumption threading can populate this soundly.
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
    // Intentionally NOT populating last_unsat_core: see the doc above — an
    // over-approximate full-tracked-set core would report non-participating
    // literals (a wrong value). Empty is the sound, honest floor.
    let outcome = match verdict {
        Z3_L_TRUE => OptimizeCheckOutcome::Sat,
        Z3_L_FALSE => OptimizeCheckOutcome::Unsat,
        _ => OptimizeCheckOutcome::Unknown,
    };
    opt.record_check_outcome(outcome);
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
            if opt.last_check_outcome != Some(OptimizeCheckOutcome::Sat) {
                return ptr::null_mut();
            }
            match opt.last_model.clone() {
                Some(model) => {
                    // The optimize path materializes no raw model text, so
                    // the snapshot carries no function tables (honest
                    // absence: UF applications stay symbolic under eval).
                    let handle = Box::into_raw(Box::new(ModelHandle {
                        model,
                        func_interps: Vec::new(),
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
            // Hard assertions, by internal term id (best-effort).
            for t in ctx.solver.assertions() {
                out.push_str(&format!("  (assert t!{})\n", t.to_raw()));
            }
            // Soft constraints recorded on this optimize handle.
            if let Some(opt) = o.as_mut() {
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
    // SAFETY: see `Z3_optimize_maximize`.
    unsafe { optimize_register_objective(c, o, t, ObjectiveSense::Minimize) }
}

/// Optimization sense for the shared registration path.
#[derive(Clone, Copy)]
enum ObjectiveSense {
    Maximize,
    Minimize,
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
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(opt) = o.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in maximize/minimize".to_string());
                return 0;
            };
            if !optimize_handle_is_usable(ctx, opt, "Z3_optimize_maximize/minimize") {
                return 0;
            }
            let term = ast_to_term(t);
            let idx = match sense {
                ObjectiveSense::Maximize => ctx.solver.maximize(term),
                ObjectiveSense::Minimize => ctx.solver.minimize(term),
            };
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
            idx as c_uint
        })
    }
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
/// finite numeral that represents infinity, so it returns null rather than
/// fabricate one. (Note that an unbounded INT objective already makes
/// `Z3_optimize_check` return `Z3_L_UNDEF`, so `get_lower`/`get_upper` are not
/// usefully reached for it; only an unbounded REAL objective — which AY reports
/// SAT with `oo` — reaches this null return.) A finite optimum is always an exact
/// numeral, never fabricated.
///
/// Returns the null AST (0) and sets `Z3_INVALID_ARG` if `idx` is out of range;
/// returns 0 (with `Z3_OK`) if no optimum is available (last check not SAT) or
/// the optimum is unbounded.
///
/// # Safety
/// `c` must be a valid context pointer; `o` must be a valid optimize handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_get_lower(
    c: Z3_context,
    o: Z3_optimize,
    idx: c_uint,
) -> Z3_ast {
    // SAFETY: see `Z3_optimize_get_upper`.
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
        ffi_guard_ast(c, |ctx| {
            let Some(opt) = o.as_ref() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in get_lower/get_upper".to_string());
                return 0;
            };
            let idx = idx as usize;
            // Validate the index against the registered objectives.
            let Some(sort) = ctx.solver.objective_sort(idx) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_optimize_get_lower/upper: objective index {idx} out of range"
                ));
                return 0;
            };
            if opt.last_check_outcome != Some(OptimizeCheckOutcome::Sat) {
                ctx.last_error = Z3_OK;
                return 0;
            }
            let Some(value) = ctx.solver.get_objective_value(idx) else {
                // No optimum available (last check not SAT, or inconclusive).
                // Honest: return null rather than a fabricated numeral.
                ctx.last_error = Z3_OK;
                return 0;
            };
            ctx.last_error = Z3_OK;
            build_objective_numeral(ctx, &value, &sort)
        })
    }
}

/// Build a Z3 numeral AST for an objective optimum in the given sort.
///
/// Finite optima: an exact numeral in the objective's sort. Unbounded optima
/// (`+oo` / `-oo`): AY has no first-class infinity term and there is no finite
/// numeral that represents `oo`, so this returns the null AST (0) — honest
/// rather than a fabricated finite value. See [`Z3_optimize_get_lower`] for the
/// documented divergence from Z3 (which returns a structured `oo` AST).
fn build_objective_numeral(ctx: &mut Z3Context, value: &ObjectiveValue, sort: &Sort) -> Z3_ast {
    match value {
        ObjectiveValue::Finite(r) => build_finite_numeral(ctx, r, sort),
        // Unbounded: no representable numeral. Return null (0). The native API
        // exposes the +oo/-oo distinction via `Solver::get_objective_value`;
        // the C numeral surface cannot, so it returns null honestly.
        ObjectiveValue::PosInfinity | ObjectiveValue::NegInfinity => 0,
    }
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
    let ast = term_to_ast(term);
    record_ast_sort(ctx, ast, out_sort);
    ast
}

/// Build an `Int` numeral AST for the exact integer `v` and record its sort.
fn int_numeral_ast(ctx: &mut Z3Context, v: &BigInt) -> Z3_ast {
    let term = ctx.solver.int_const_bigint(v);
    let ast = term_to_ast(term);
    record_ast_sort(ctx, ast, Sort::Int);
    ast
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
            // The popped scope's model / core no longer apply.
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
        });
    }
}

// ============================================================================
// Tracked assertions + unsat core.
// ============================================================================

/// Assert a tracked hard constraint `a`, associated with the tracking literal
/// `t`.
///
/// `a` is asserted as a REAL hard constraint (unconditional, exactly like
/// `Z3_optimize_assert`): it genuinely holds for every solve, so the optima and
/// SAT/UNSAT verdict are unaffected — nothing is faked. The Boolean tracking
/// literal `t` is retained, but participating-only Optimize core extraction is
/// not implemented; [`Z3_optimize_get_unsat_core`] therefore returns empty.
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
    // null-checked via `as_mut`; `a`/`t` are validated by `ast_to_term`.
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
            let a_term = ast_to_term(a);
            let t_term = ast_to_term(t);
            // The tracking literal must be Boolean (z3 requires a Boolean atom).
            if ctx.solver.term_sort(t_term) != Sort::Bool {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_optimize_assert_and_track: tracking literal must be Boolean".to_string(),
                );
                return;
            }
            // Assert `a` as a real hard constraint (validates its Bool sort).
            if let Err(e) = ctx.solver.try_assert_term(a_term) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return;
            }
            opt.hard.push(a_term);
            opt.tracked.push((t_term, a_term));
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
        });
    }
}

/// Retrieve the unsat core of the last `Z3_optimize_check`.
///
/// HONEST DIVERGENCE FROM Z3: always returns an empty vector. AY's Optimize path
/// does not thread tracking literals as assumptions and therefore cannot extract
/// a participating-only core. Returning the complete tracked set would include
/// non-participating literals and misstate Z3's core contract, so this accessor
/// fails to the sound empty floor. See [`capture_check_diagnostics`].
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
                        Some(core) => core.iter().copied().map(term_to_ast).collect(),
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
            if o.as_ref().is_none() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_optimize handle in get_objectives".to_string());
                return cache_ast_vector(ctx, Vec::new());
            }
            let n = ctx.solver.num_objectives();
            // Collect (term, sort) with immutable borrows before mutating ctx.
            let items: Vec<(Term, Option<Sort>)> = (0..n)
                .filter_map(|i| {
                    ctx.solver
                        .objective_term(i)
                        .map(|t| (t, ctx.solver.objective_sort(i)))
                })
                .collect();
            let mut asts = Vec::with_capacity(items.len());
            for (term, sort) in items {
                let ast = term_to_ast(term);
                if let Some(s) = sort {
                    record_ast_sort(ctx, ast, s);
                }
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
                Some(opt) => opt.hard.iter().copied().map(term_to_ast).collect(),
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
    // SAFETY: see `optimize_get_objective_vector`.
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
    // SAFETY: see `optimize_get_objective_vector`.
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
            let idx = idx as usize;
            let Some(sort) = ctx.solver.objective_sort(idx) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_optimize_get_lower/upper_as_vector: objective index {idx} out of range"
                ));
                return cache_ast_vector(ctx, Vec::new());
            };
            if opt.last_check_outcome != Some(OptimizeCheckOutcome::Sat) {
                ctx.last_error = Z3_OK;
                return cache_ast_vector(ctx, Vec::new());
            }
            let Some(value) = ctx.solver.get_objective_value(idx) else {
                // No optimum available (last check not SAT): honest empty vector.
                ctx.last_error = Z3_OK;
                return cache_ast_vector(ctx, Vec::new());
            };
            ctx.last_error = Z3_OK;
            // Decompose into (infinity coeff a, finite b, epsilon coeff c).
            let (a, finite, eps) = match value {
                ObjectiveValue::Finite(r) => (BigInt::from(0), Some(r), BigInt::from(0)),
                ObjectiveValue::PosInfinity => (BigInt::from(1), None, BigInt::from(0)),
                ObjectiveValue::NegInfinity => (BigInt::from(-1), None, BigInt::from(0)),
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

    // Fail-close reserved `map[...]` symbol capture (measured wrong-verdict
    // channel through the core elaborator) — see `smtlib2_reserved_error`.
    if let Some(msg) = super::smtlib2_reserved_error(input) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!("{operation}: {msg}"));
        return;
    }

    let commands = match ay_frontend::parse(input) {
        Ok(commands) => commands,
        Err(e) => {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{operation}: {e}"));
            return;
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

    match ctx.solver.parse_smtlib2(input) {
        Ok(new_asserts) => {
            opt.hard.extend(new_asserts);
            opt.terminal_error = None;
            ctx.last_error = Z3_OK;
            ctx.error_msg = None;
        }
        Err(e) => {
            let mut reason = format!("{operation}: parse execution failed: {e}");
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
    let input: Option<String> = if s.is_null() {
        None
    } else {
        // SAFETY: the caller's contract guarantees `s`, when non-null, is a valid
        // null-terminated C string owned by the caller for this call's duration.
        match unsafe { CStr::from_ptr(s) }.to_str() {
            Ok(v) => Some(v.to_string()),
            Err(_) => Some(String::new()), // non-UTF-8 → treated as parse error below
        }
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
            let Some(input) = input.as_deref() else {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some("Z3_optimize_from_string: null input string".to_string());
                return;
            };
            parse_optimize_transaction(ctx, opt, input, "Z3_optimize_from_string");
        });
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
        match unsafe { CStr::from_ptr(s) }.to_str() {
            Ok(v) => Some(v.to_string()),
            Err(_) => None,
        }
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
            let contents = match std::fs::read_to_string(path) {
                Ok(v) => v,
                Err(e) => {
                    ctx.last_error = Z3_FILE_ACCESS_ERROR;
                    ctx.error_msg = Some(format!("Z3_optimize_from_file: {e}"));
                    return;
                }
            };
            parse_optimize_transaction(ctx, opt, &contents, "Z3_optimize_from_file");
        });
    }
}

// ============================================================================
// Params / help / param-descriptors.
// ============================================================================

/// Set parameters on the optimization context.
///
/// Routes through the same param application as `Z3_solver_set_params`: AY
/// honors `timeout` (uint, ms), `produce-proofs` (bool), and the
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
            apply_supported_params(&mut ctx.solver, &params_owned);
            // Parameters govern the next decision transaction. Retire copied
            // result artifacts so no caller can mistake a pre-configuration
            // snapshot for the outcome of the newly configured optimizer.
            opt.clear_check_artifacts();
            ctx.last_error = Z3_OK;
            ctx.error_msg = None;
        });
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
