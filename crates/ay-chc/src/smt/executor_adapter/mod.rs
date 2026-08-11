// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thin adapter dispatching array-containing SMT queries to ay-dpll's Executor.
//!
//! When the CHC solver's internal DPLL(T) loop (`check_sat.rs`) encounters
//! formulas with array operations (select, store, const-array), the loop lacks
//! proper array axiom generation and returns Unknown. This adapter converts the
//! ChcExpr to SMT-LIB text and delegates to ay-dpll's Executor, which has full
//! array theory support (eager axioms, extensionality, ROW lemmas, N-O fixpoint).
//!
//! Design: the development design notes
//! Approach C — thin adapter, array logics only.

mod logic_detection;
mod model_parsing;

// Re-export for sibling modules (persistent.rs) and crate-level re-export (smt/mod.rs #7983).
pub(crate) use logic_detection::{
    collect_dt_declarations, collect_dt_declarations_for_expr, detect_logic, emit_declare_datatype,
    quote_symbol, sort_to_smtlib,
};
pub(crate) use model_parsing::parse_model_into;

// Re-export test-visible helpers (tests.rs uses super::*).
#[cfg(test)]
pub(super) use model_parsing::{
    parse_decimal_to_rational, parse_model_simple, parse_simple_value, term_body_to_smt_value,
};

use super::context::SmtContext;
use super::executor_sort_guard::unsupported_executor_expr_reason;
use super::model_verify::verify_sat_model_conjunction_strict_with_mod_retry;
use super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::pdr::model::InvariantModel;
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::panic::AssertUnwindSafe;

/// Per-call executor trace (inc-13 per-check cost attribution): active at
/// `AY_CHECKSAT_TRACE>=2`. Logs construction/execute split plus the
/// executor-internal phase timers so the 0.3-0.7s per-check fallback cost
/// can be attributed to a concrete sink.
fn exec_trace_enabled() -> bool {
    super::check_sat::checksat_trace_level() >= 2
}

/// Inc-18 SAT-direction EqDiffVar retry gate (`AY_EXEC_DV_RETRY`, default
/// ON; `0`/`false` disables). Forced OFF when the inc-14 master switch
/// `AY_EQ_DIFFVAR=0` already disables the pass globally — a retry without
/// the pass would re-run an identical pipeline. Read per call (not cached)
/// so A/B harnesses can toggle within a process, matching the inc-14 gate.
pub(super) fn dv_unknown_retry_enabled() -> bool {
    if std::env::var("AY_EQ_DIFFVAR").is_ok_and(|v| v == "0") {
        return false;
    }
    std::env::var("AY_EXEC_DV_RETRY").map_or(true, |v| v != "0" && !v.eq_ignore_ascii_case("false"))
}

fn execute_commands_via_executor(commands: &[ay_frontend::Command]) -> Result<Vec<String>, ()> {
    let trace = exec_trace_enabled();
    let t_new = ay_core::time::Instant::now();
    let mut exec = ay_dpll::Executor::new();
    let new_dt = t_new.elapsed();
    let t_exec = ay_core::time::Instant::now();
    let result = ay_core::catch_ay_panics(
        AssertUnwindSafe(|| match exec.execute_all(commands) {
            Ok(out) => Ok(out),
            Err(e) => {
                tracing::debug!("executor_adapter: execution error: {e}");
                Err(())
            }
        }),
        |reason| {
            tracing::debug!("executor_adapter: ay panic: {reason}");
            Err(())
        },
    );
    if trace {
        let stats = exec.statistics();
        let phase = |name: &str| stats.get_float(name).unwrap_or(0.0);
        safe_eprintln!(
            "[EXEC-TRACE {:?}] new={:.1}ms exec={:.1}ms (quant={:.1}ms logic={:.1}ms dispatch={:.1}ms map={:.1}ms) conflicts={} decisions={}",
            std::thread::current().id(),
            new_dt.as_secs_f64() * 1e3,
            t_exec.elapsed().as_secs_f64() * 1e3,
            phase("phase.quantifier_preprocess.seconds") * 1e3,
            phase("phase.logic_detection.seconds") * 1e3,
            phase("phase.solver_dispatch.seconds") * 1e3,
            phase("phase.quantifier_result_mapping.seconds") * 1e3,
            stats.conflicts,
            stats.decisions
        );
    }
    result
}

/// Run a raw SMT-LIB script through the ay-dpll executor and return `true`
/// only when the first output is literally `unsat`.
///
/// Used by the ghost-pair quantified certification fallback
/// (`transform::array_ghost_pairs::certify`), whose discharge queries contain
/// explicit `forall` assertions that have no `ChcExpr` representation. The
/// executor's `unsat` verdict is trusted here exactly as it is trusted by
/// `check_sat_via_executor` above (same engine, same proof pipeline); any
/// parse error, execution error, panic, `sat`, or `unknown` returns `false`
/// (fail-closed).
pub(crate) fn check_unsat_smtlib_via_executor(smt: &str) -> bool {
    let commands = match ay_frontend::parse(smt) {
        Ok(commands) => commands,
        Err(error) => {
            tracing::debug!("executor_adapter: quantified script parse error: {error}");
            return false;
        }
    };
    match execute_commands_via_executor(&commands) {
        Ok(outputs) => outputs.first().map(String::as_str) == Some("unsat"),
        Err(()) => false,
    }
}

/// Run a raw SMT-LIB script through the ay-dpll executor with an optional
/// wall-clock timeout and return the first verdict output (`sat` / `unsat` /
/// `unknown`), or `None` on parse error, execution error, or ay panic.
///
/// Used by the CHC checked-replay pass (`proof_metadata::replay_check`) to
/// re-execute digest-bound certificate obligation queries on a fresh executor.
/// The timeout is injected as a prepended `(set-option :timeout <ms>)` command
/// rather than by editing the obligation text, so the hashed artifact bytes
/// stay exactly what was emitted; a timeout can only degrade a definite
/// verdict to `unknown` (never flip sat/unsat), so the injection cannot change
/// what the obligation proves. Fail-closed like
/// [`check_unsat_smtlib_via_executor`].
pub(crate) fn smtlib_first_verdict_via_executor(
    smt: &str,
    timeout: Option<std::time::Duration>,
) -> Option<String> {
    let script_with_timeout;
    let effective_script = match timeout {
        Some(timeout) if !timeout.is_zero() => {
            let ms = u64::try_from(timeout.as_millis())
                .unwrap_or(u64::MAX)
                .max(1);
            script_with_timeout = format!("(set-option :timeout {ms})\n{smt}");
            script_with_timeout.as_str()
        }
        _ => smt,
    };
    let commands = match ay_frontend::parse(effective_script) {
        Ok(commands) => commands,
        Err(error) => {
            tracing::debug!("executor_adapter: replay obligation parse error: {error}");
            return None;
        }
    };
    match execute_commands_via_executor(&commands) {
        Ok(outputs) => outputs.first().cloned(),
        Err(()) => None,
    }
}

/// A native strict-Alethe UNSAT certificate for one CHC replay obligation.
///
/// Produced by [`smtlib_strict_unsat_cert_via_executor`] on a proof-enabled
/// `ay-dpll` `Solver`. Both fields are self-contained and require NO external
/// process (no z3, no carcara): `strict_verdict` is AY's own in-process strict
/// Alethe check (`export_last_unsat_artifact().strict_verdict`), and `bundle`
/// is the portable proof that AY's own offline checker
/// (`ay_dpll::api::re_check_bundle_strict`) re-validates with no solver run.
pub(crate) struct StrictUnsatCert {
    /// Offline-recheckable proof bundle (re-checked by `re_check_bundle_strict`).
    pub bundle: ay_dpll::api::SerializableProofBundle,
    /// Rendered Alethe proof text (the human/tool-visible certificate).
    pub alethe: String,
    /// In-process strict verdict from `export_last_unsat_artifact()`.
    pub strict_verdict: ay_dpll::api::StrictProofVerdict,
}

/// Discharge one UNSAT replay obligation with a NATIVE STRICT ALETHE self-check.
///
/// This is the proof-emitting sibling of [`smtlib_first_verdict_via_executor`]:
/// rather than merely returning a trusted `unsat`/`sat`/`unknown` verdict, it
/// builds a proof-enabled `ay-dpll` [`Solver`](ay_dpll::api::Solver), executes
/// the obligation, and — only when the obligation is genuinely `unsat` and a
/// proof was produced — returns the strict Alethe certificate: an in-process
/// [`StrictProofVerdict`](ay_dpll::api::StrictProofVerdict) plus the portable
/// [`SerializableProofBundle`](ay_dpll::api::SerializableProofBundle) that AY's
/// own offline checker can re-validate. Everything here is self-contained: no
/// z3, no external checker.
///
/// The proof machinery is enabled by prepending
/// `(set-option :produce-proofs true)`; the obligation carries its own
/// `(set-logic …)`, declarations, and assertions, which `parse_smtlib2`
/// executes while skipping its `(check-sat)` (we drive the solve ourselves so
/// we can capture the proof artifact).
///
/// Fail-closed like [`smtlib_first_verdict_via_executor`]: any parse error,
/// executor error, ay panic, a non-`unsat` verdict, or a missing proof returns
/// `None`. A `None` return must be treated by the caller as "not strictly
/// discharged" (fail-close to metadata-only / unknown), never as a pass.
/// Re-export of the shared splitter that lives with the `Solver` API it
/// exists to serve; see [`ay_dpll::api::split_leading_set_logic`].
pub(crate) use ay_dpll::api::split_leading_set_logic;

pub(crate) fn smtlib_strict_unsat_cert_via_executor(
    smt: &str,
    timeout: Option<std::time::Duration>,
) -> Option<StrictUnsatCert> {
    use ay_dpll::api::{Solver, SolverConfig};

    ay_core::catch_ay_panics(
        AssertUnwindSafe(|| {
            let config = match timeout {
                Some(timeout) if !timeout.is_zero() => {
                    SolverConfig::default().with_timeout(timeout)
                }
                _ => SolverConfig::default(),
            };
            // Take the obligation's OWN `(set-logic …)` and build the solver
            // with it, rather than opening at `Logic::All` and letting the
            // script re-select.
            //
            // `Solver::try_new_with_config` dispatches a `set-logic` of its
            // own, so a `set-logic` left in the script is the SECOND one — and
            // since `118630ef6` ("z3 exit-code contract … reject a second
            // set-logic") the elaborator rejects that, exactly as z3 does.
            // `parse_smtlib2` would then fail and `.ok()?` would swallow it as
            // a bare `None`, which every caller must read as "not strictly
            // discharged". The visible symptom was checked replay reporting
            // "did not produce a native strict-Alethe UNSAT certificate;
            // staying metadata-only" for obligations that are perfectly
            // provable.
            //
            // Constructing with the declared logic keeps the obligation's own
            // semantics instead of silently widening it to `ALL`; an
            // unrecognized or absent declaration falls back to `ALL`, which is
            // what this path used before.
            let (logic, body) = split_leading_set_logic(smt, ay_dpll::api::Logic::All);
            let mut solver = Solver::try_new_with_config(logic, config).ok()?;

            // Enable proof production BEFORE any assertion is installed so the
            // executor retains parsed assertions for proof rebuild. The
            // obligation text's `(check-sat)` is skipped by `parse_smtlib2`; we
            // run the solve ourselves below to capture the proof artifact.
            let script = format!("(set-option :produce-proofs true)\n{body}");
            solver.parse_smtlib2(&script).ok()?;

            let result = solver.check_sat();
            if !result.is_unsat() {
                tracing::debug!(
                    "executor_adapter: strict-unsat-cert obligation was not unsat; failing closed"
                );
                return None;
            }

            // `export_last_unsat_artifact().strict_verdict` is AY's own
            // in-process strict Alethe check; the bundle is the offline-
            // recheckable twin. Both are required — a missing proof (e.g. the
            // executor decided unsat on a path that produced no proof) fails
            // closed.
            let artifact = solver.export_last_unsat_artifact()?;
            let bundle = solver.export_last_unsat_bundle()?;
            Some(StrictUnsatCert {
                bundle,
                alethe: artifact.alethe,
                strict_verdict: artifact.strict_verdict,
            })
        }),
        |reason| {
            tracing::debug!("executor_adapter: strict-unsat-cert ay panic: {reason}");
            None
        },
    )
}

fn needs_strict_reparsed_validation(exprs: &[&ChcExpr]) -> bool {
    exprs
        .iter()
        .any(|expr| expr.contains_array_ops() || expr.contains_dt_ops() || expr.has_mod_aux_vars())
}

/// Axiomatize integer div/mod with constant divisors before executor dispatch (#A3).
///
/// ay-dpll's AUFLIA/ALIA fragments reject raw integer `div`/`mod` terms with
/// "(unsupported arithmetic)", which turns satisfiable validator replays
/// (counterexample verification on original clauses) into Unknown and rejects
/// valid Unsafe results. Rewriting `(div x k)` / `(mod x k)` for literal `k`
/// into fresh quotient/remainder variables constrained by
/// `x = k*q + r ∧ 0 ≤ r < |k|` (SMT-LIB Euclidean semantics — the #1362
/// transform in `ChcExpr::eliminate_mod`) is equisatisfiable: the constraints
/// are total in `x`, so every model of the original extends to the rewritten
/// form and every model of the rewritten form restricts to the original.
///
/// Returns `None` when the expression contains no mod/div (no rewrite needed).
/// SAT models must still be validated against the ORIGINAL expression — the
/// caller keeps using the untransformed expr for `accept_reparsed_sat_model`.
pub(crate) fn axiomatize_mod_div_for_executor(expr: &ChcExpr) -> Option<ChcExpr> {
    if !expr.contains_mod_or_div() {
        return None;
    }
    let eliminated = expr.eliminate_mod();
    if eliminated.contains_mod_or_div() {
        // Non-constant divisors survive elimination; the executor would still
        // report unsupported arithmetic. Returning the partial rewrite is
        // still sound and lets constant-divisor sites succeed.
        tracing::debug!(
            "executor_adapter: mod/div with non-constant divisor survives axiomatization"
        );
    }
    Some(eliminated)
}

pub(super) fn accept_reparsed_sat_model(
    exprs: &[&ChcExpr],
    model: FxHashMap<String, SmtValue>,
    source: &'static str,
) -> Option<FxHashMap<String, SmtValue>> {
    let verify_result =
        verify_sat_model_conjunction_strict_with_mod_retry(exprs.iter().copied(), &model);
    let requires_strict = needs_strict_reparsed_validation(exprs);
    match verify_result {
        ModelVerifyResult::Invalid => {
            tracing::warn!(
                "{source}: reparsed SAT model violates original CHC expression; returning Unknown"
            );
            None
        }
        ModelVerifyResult::Indeterminate if requires_strict => {
            tracing::debug!(
                "{source}: reparsed SAT model is indeterminate for array/DT/mod query; returning Unknown"
            );
            None
        }
        ModelVerifyResult::Indeterminate => {
            // FAIL-CLOSED (2026-07-08, wishlist rank 1 — the executor twin of the
            // `sat_or_unknown` fix): an Indeterminate verification whose model is
            // MISSING an assignment for a variable in an evaluable theory position
            // is the dropped-definition signature — the model then says nothing
            // about the original expression. In the model-checker-consumer midpoint repro the
            // internal DPLL(T) loop's bad models were demoted by `sat_or_unknown`,
            // and the EXECUTOR fallback then shipped an under-assigned model
            // through this very arm, surfacing as a spurious CHC refutation.
            // Fully-assigned models with only predicate/UF-caused indeterminacy
            // are still accepted (#4712 semantics), as before.
            // PRECISION (FIX 5, aychc-completeness): the executor twin of the
            // `sat_or_unknown` bindings completion, tried BEFORE the
            // scalar-defaults attempt. Derive the missing evaluable-position
            // variables from their SSA defining equalities present in `exprs`
            // (forced values, never defaults), then require a strict `Valid`
            // conjunction verdict before accepting — the SAME verifier as the
            // acceptance gate above, so no new acceptance channel. On any other
            // outcome fall through (with the ORIGINAL model) to the defaults
            // attempt and the unchanged fail-closed None.
            {
                let mut derived = model.clone();
                let mut changed = false;
                for e in exprs {
                    changed |= super::check_sat::complete_model_from_bindings(e, &mut derived);
                }
                if changed
                    && matches!(
                        verify_sat_model_conjunction_strict_with_mod_retry(
                            exprs.iter().copied(),
                            &derived,
                        ),
                        ModelVerifyResult::Valid
                    )
                {
                    tracing::debug!(
                        "{source}: reparsed SAT model completed from SSA defining-equality \
                         bindings and strict-verified Valid; accepting"
                    );
                    return Some(derived);
                }
            }
            if let Some((completed, missing)) =
                super::check_sat::complete_model_with_scalar_defaults(exprs.iter().copied(), &model)
            {
                // Model-completion-then-strict-reverify (2026-07), the executor
                // twin of the identical path in `sat_or_unknown`: fill every
                // missing evaluable-position scalar with a type-appropriate
                // default (BitVec→0, Int→0, Bool→false, Real→0), then re-run
                // the SAME strict conjunction verifier used at the acceptance
                // gate above.
                //
                // SOUNDNESS INVARIANT (non-negotiable): this path may only ever
                // emit Sat-with-verified-witness (`Some(completed)`) or Unknown
                // (`None`), NEVER Unsat. Acceptance is gated EXCLUSIVELY on the
                // strict verifier evaluating the ORIGINAL expressions to
                // Bool(true) under the completed model
                // (`ModelVerifyResult::Valid`). Accepting a completed model
                // WITHOUT re-verification would reopen the under-assigned-model
                // fail-open described above (spurious CHC refutation, model-checker-consumer
                // midpoint repro). Invalid AND Indeterminate completions both
                // fall through to Unknown.
                if matches!(
                    verify_sat_model_conjunction_strict_with_mod_retry(
                        exprs.iter().copied(),
                        &completed
                    ),
                    ModelVerifyResult::Valid
                ) {
                    tracing::debug!(
                        "{source}: reparsed SAT model was missing {} evaluable-position scalar \
                         assignment(s); default-completed model strictly verifies against the \
                         original expression(s); accepting",
                        missing.len()
                    );
                    return Some(completed);
                }
                let (first_missing, _) = &missing[0];
                tracing::warn!(
                    "{source}: reparsed SAT model is missing an assignment for free \
                     variable `{first_missing}` (in an evaluable theory position); \
                     default-value completion was attempted but the completed model did \
                     not strictly verify; returning Unknown instead of accepting"
                );
                return None;
            }
            tracing::debug!("{source}: reparsed SAT model verification indeterminate; accepting");
            Some(model)
        }
        ModelVerifyResult::Valid => {
            debug_assert!(
                !requires_strict || matches!(verify_result, ModelVerifyResult::Valid),
                "BUG: reparsed SAT model for array/DT/mod query must validate before acceptance"
            );
            Some(model)
        }
    }
}

impl SmtContext {
    /// Dispatch an array-containing formula to ay-dpll's Executor for full
    /// array theory support. Falls back to SmtResult::Unknown on any error.
    ///
    /// The `propagated_model` contains var=value bindings discovered during
    /// preprocessing (constant propagation, singleton bounds). These are merged
    /// into the executor's model on Sat so PDR cube extraction has access to all
    /// known bindings.
    pub(crate) fn check_sat_via_executor(
        &self,
        expr: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: std::time::Duration,
    ) -> SmtResult {
        self.check_sat_via_executor_with_opts(expr, propagated_model, timeout, false)
    }

    /// `check_sat_via_executor` with per-run executor options (inc-18).
    ///
    /// `disable_eq_diffvar` emits `(set-option :ay-eq-diffvar false)` into the
    /// executor script, disabling the inc-14 EqDiffVar preprocessing pass for
    /// THIS run only. Used by the SAT-direction retry in `check_sat`: on
    /// IMC-class itp-strengthened transition checks the reduction defeats the
    /// model search that the plain pipeline decides in milliseconds.
    /// Soundness: identical adapter pipeline — UNSAT carries the same trust as
    /// every executor verdict at this call site, and SAT models pass the same
    /// strict validation against the ORIGINAL expression below.
    pub(crate) fn check_sat_via_executor_with_opts(
        &self,
        expr: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: std::time::Duration,
        disable_eq_diffvar: bool,
    ) -> SmtResult {
        // Step 0 (#A3): Axiomatize div/mod before serialization so the
        // executor's AUFLIA/ALIA fragments never see raw integer div/mod.
        // Equisatisfiable; SAT models are still validated against the
        // ORIGINAL expression below.
        let trace = exec_trace_enabled();
        let t_build = ay_core::time::Instant::now();
        let mod_div_axiomatized = axiomatize_mod_div_for_executor(expr);
        let solve_expr = mod_div_axiomatized.as_ref().unwrap_or(expr);

        // Step 1: Collect free variables and their sorts from the expression.
        let vars = solve_expr.vars();
        if vars.is_empty() {
            // No variables -- constant expression. Let the normal path handle it.
            return SmtResult::Unknown;
        }

        // Step 2: Detect the appropriate logic based on sorts present.
        let logic = detect_logic(&vars, solve_expr);

        // Step 3: Build SMT-LIB text.
        let mut smt = String::with_capacity(512);
        smt.push_str(&format!("(set-logic {logic})\n"));
        smt.push_str("(set-option :produce-models true)\n");

        // Set timeout if available -- ay-dpll uses :timeout option in ms.
        let timeout_ms = timeout.as_millis();
        if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
            smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
        }

        // Inc-18: per-run EqDiffVar opt-out (see method docs). The extra
        // option line also changes the memo fingerprint, so dv-on and dv-off
        // attempts are memoised independently.
        if disable_eq_diffvar {
            smt.push_str("(set-option :ay-eq-diffvar false)\n");
        }

        // Declare datatypes before any constants that use them.
        let dt_decls = collect_dt_declarations_for_expr(&vars, solve_expr);
        for (dt_name, ctors) in &dt_decls {
            smt.push_str(&emit_declare_datatype(dt_name, ctors));
        }

        // Declare variables.
        for var in &vars {
            let sort_str = sort_to_smtlib(&var.sort);
            let name = quote_symbol(&var.name);
            smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
        }

        // Assert the formula. Split top-level conjunctions into separate
        // (assert ...) statements so ay-dpll's DT axiom generation sees each
        // conjunct individually. Without this, (assert (and A B C)) hides
        // DT constructor equalities from the reachability filter (#7016).
        let conjuncts = solve_expr.conjuncts();
        if let Some(reason) = conjuncts
            .iter()
            .find_map(|expr| unsupported_executor_expr_reason(expr))
        {
            tracing::debug!(
                "executor_adapter: unsupported SMT-LIB executor term: {reason}; returning Unknown"
            );
            return SmtResult::Unknown;
        }
        for c in &conjuncts {
            let c_str = InvariantModel::expr_to_smtlib(c);
            smt.push_str(&format!("(assert {c_str})\n"));
        }
        smt.push_str("(check-sat)\n");
        smt.push_str("(get-model)\n");
        let build_dt = t_build.elapsed();

        // Timeout-class unknown memo (inc-13): a byte-identical query that
        // already exhausted an equal-or-larger budget in this context
        // short-circuits to Unknown instead of re-burning the executor.
        // See `executor_unknown_memo` for the soundness argument; kill
        // switch AY_EXEC_UNKNOWN_MEMO=0.
        let memo_enabled = super::executor_unknown_memo::executor_unknown_memo_enabled();
        let budget_ms = u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX);
        let query_fingerprint = if memo_enabled {
            let fp = super::executor_unknown_memo::fingerprint_query_text(&smt);
            if super::executor_unknown_memo::should_skip_query(fp, budget_ms) {
                if trace {
                    safe_eprintln!(
                        "[EXEC-TRACE {:?}] memo skip budget={budget_ms}ms smt_bytes={}",
                        std::thread::current().id(),
                        smt.len()
                    );
                }
                return SmtResult::Unknown;
            }
            Some(fp)
        } else {
            None
        };
        let t_solve_start = ay_core::time::Instant::now();

        // Step 4: Parse and execute via ay-dpll.
        let t_parse = ay_core::time::Instant::now();
        let commands = match ay_frontend::parse(&smt) {
            Ok(cmds) => cmds,
            Err(e) => {
                tracing::debug!("executor_adapter: parse error: {e}");
                return SmtResult::Unknown;
            }
        };
        let parse_dt = t_parse.elapsed();

        let outputs = match execute_commands_via_executor(&commands) {
            Ok(out) => out,
            Err(()) => return SmtResult::Unknown,
        };

        // Step 5: Interpret the result.
        let t_model = ay_core::time::Instant::now();
        let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
        let result = match result_str {
            "unsat" => SmtResult::Unsat,
            "sat" => {
                // Parse model from the second output (get-model response).
                let model_str = outputs.get(1).map(String::as_str).unwrap_or("");
                let mut model = propagated_model.clone();
                let dt_ctor_names: FxHashSet<String> = dt_decls
                    .iter()
                    .flat_map(|(_, ctors)| ctors.iter().map(|c| c.name.clone()))
                    .collect();
                parse_model_into(&mut model, model_str, &dt_ctor_names);
                let validation_exprs = [expr];
                if let Some(model) =
                    accept_reparsed_sat_model(&validation_exprs, model, "executor_adapter")
                {
                    SmtResult::Sat(model)
                } else {
                    SmtResult::Unknown
                }
            }
            "unknown" => SmtResult::Unknown,
            other => {
                tracing::warn!(
                    "executor_adapter: unexpected result string: {other:?}, treating as Unknown"
                );
                SmtResult::Unknown
            }
        };
        // Memo recording (inc-13): only a RAW executor "unknown" that consumed
        // its budget counts as a timeout-class unknown. A SAT downgraded to
        // Unknown by model validation is an answered query and is never
        // memoised; fast structural unknowns are filtered inside the memo.
        if let Some(fp) = query_fingerprint {
            if result_str == "unknown" {
                let elapsed_ms =
                    u64::try_from(t_solve_start.elapsed().as_millis()).unwrap_or(u64::MAX);
                super::executor_unknown_memo::record_unknown_query(fp, budget_ms, elapsed_ms);
            }
        }
        if trace {
            safe_eprintln!(
                "[EXEC-TRACE {:?}] adapter build={:.1}ms parse={:.1}ms model+verify={:.1}ms smt_bytes={} vars={} conjuncts={} raw={} final_unknown={}",
                std::thread::current().id(),
                build_dt.as_secs_f64() * 1e3,
                parse_dt.as_secs_f64() * 1e3,
                t_model.elapsed().as_secs_f64() * 1e3,
                smt.len(),
                vars.len(),
                conjuncts.len(),
                result_str,
                matches!(result, SmtResult::Unknown)
            );
            // Slow-check capture (inc-13 attribution): dump the exact SMT-LIB
            // text of timeout-class checks for offline differential analysis.
            if let Ok(dir) = std::env::var("AY_CHECKSAT_DUMP") {
                let dt = t_build.elapsed();
                if result_str == "unknown"
                    || matches!(result, SmtResult::Unknown)
                    || dt.as_millis() > 500
                {
                    use std::sync::atomic::{AtomicUsize, Ordering};
                    static DUMP_SEQ: AtomicUsize = AtomicUsize::new(0);
                    let n = DUMP_SEQ.fetch_add(1, Ordering::Relaxed);
                    let path = format!("{dir}/check_{n:04}_{}ms_{result_str}.smt2", dt.as_millis());
                    let _ = std::fs::write(path, &smt);
                }
            }
        }
        result
    }
}

/// Dispatch a conjunction of expressions (background + assumptions) to ay-dpll's
/// Executor for full array theory support. Used by `IncrementalQueryContext` when
/// the internal DPLL(T) loop returns Unknown on array-containing formulas.
///
/// Combines all expressions into a single `(and ...)` assertion and runs it
/// through the executor. Returns `IncrementalCheckResult` matching the caller's
/// expected return type.
pub(crate) fn check_sat_conjunction_via_executor(
    exprs: &[ChcExpr],
    propagated_equalities: &FxHashMap<String, i128>,
    timeout: std::time::Duration,
) -> super::incremental::IncrementalCheckResult {
    use super::incremental::IncrementalCheckResult;

    // Collect all free variables across all expressions for declarations.
    let combined = ChcExpr::and_all(exprs.iter().cloned());
    let vars = combined.vars();
    if vars.is_empty() {
        return IncrementalCheckResult::Unknown;
    }

    let logic = detect_logic(&vars, &combined);

    let mut smt = String::with_capacity(1024);
    smt.push_str(&format!("(set-logic {logic})\n"));
    smt.push_str("(set-option :produce-models true)\n");

    let timeout_ms = timeout.as_millis();
    if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
        smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
    }

    // Declare datatypes before any constants that use them.
    let dt_decls = collect_dt_declarations_for_expr(&vars, &combined);
    for (dt_name, ctors) in &dt_decls {
        smt.push_str(&emit_declare_datatype(dt_name, ctors));
    }

    for var in &vars {
        let sort_str = sort_to_smtlib(&var.sort);
        let name = quote_symbol(&var.name);
        smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
    }

    // Assert each expression separately, splitting top-level conjunctions
    // into individual asserts for DT axiom reachability (#7016).
    for expr in exprs {
        let conjuncts = expr.conjuncts();
        if let Some(reason) = conjuncts
            .iter()
            .find_map(|expr| unsupported_executor_expr_reason(expr))
        {
            tracing::debug!(
                "executor_adapter (incremental): unsupported SMT-LIB executor term: {reason}; returning Unknown"
            );
            return IncrementalCheckResult::Unknown;
        }
        for c in &conjuncts {
            let c_str = InvariantModel::expr_to_smtlib(c);
            smt.push_str(&format!("(assert {c_str})\n"));
        }
    }
    smt.push_str("(check-sat)\n");
    smt.push_str("(get-model)\n");

    // Timeout-class unknown memo (inc-13) — same contract as the
    // `check_sat_via_executor` wiring; see `executor_unknown_memo`.
    let memo_enabled = super::executor_unknown_memo::executor_unknown_memo_enabled();
    let budget_ms = u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX);
    let query_fingerprint = if memo_enabled {
        let fp = super::executor_unknown_memo::fingerprint_query_text(&smt);
        if super::executor_unknown_memo::should_skip_query(fp, budget_ms) {
            return IncrementalCheckResult::Unknown;
        }
        Some(fp)
    } else {
        None
    };
    let t_solve_start = ay_core::time::Instant::now();

    let commands = match ay_frontend::parse(&smt) {
        Ok(cmds) => cmds,
        Err(e) => {
            tracing::debug!("executor_adapter (incremental): parse error: {e}");
            return IncrementalCheckResult::Unknown;
        }
    };

    let outputs = match execute_commands_via_executor(&commands) {
        Ok(out) => out,
        Err(()) => return IncrementalCheckResult::Unknown,
    };

    let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
    if let Some(fp) = query_fingerprint {
        if result_str == "unknown" {
            let elapsed_ms = u64::try_from(t_solve_start.elapsed().as_millis()).unwrap_or(u64::MAX);
            super::executor_unknown_memo::record_unknown_query(fp, budget_ms, elapsed_ms);
        }
    }
    match result_str {
        "unsat" => IncrementalCheckResult::Unsat,
        "sat" => {
            let model_str = outputs.get(1).map(String::as_str).unwrap_or("");
            let mut model = FxHashMap::default();
            // Merge propagated equalities into model.
            for (name, value) in propagated_equalities {
                model.insert(name.clone(), SmtValue::Int(*value));
            }
            let dt_ctor_names: FxHashSet<String> = dt_decls
                .iter()
                .flat_map(|(_, ctors)| ctors.iter().map(|c| c.name.clone()))
                .collect();
            parse_model_into(&mut model, model_str, &dt_ctor_names);
            let validation_exprs: Vec<&ChcExpr> = exprs.iter().collect();
            if let Some(model) = accept_reparsed_sat_model(
                &validation_exprs,
                model,
                "executor_adapter (incremental)",
            ) {
                IncrementalCheckResult::Sat(model)
            } else {
                IncrementalCheckResult::Unknown
            }
        }
        "unknown" => IncrementalCheckResult::Unknown,
        other => {
            tracing::warn!(
                "executor_adapter (incremental): unexpected result string: {other:?}, treating as Unknown"
            );
            IncrementalCheckResult::Unknown
        }
    }
}

#[cfg(test)]
mod tests;
