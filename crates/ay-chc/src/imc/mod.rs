// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! IMC (Interpolation-based Model Checking) engine for CHC problems.
//!
//! Port of Golem's IMC engine (`reference/golem/src/engine/IMC.cc`) for AY's
//! `TransitionSystem` abstraction. Part of #1904.
//!
//! MVP scope: single-predicate, linear CHC transition systems only.

use crate::engine_config::ChcEngineConfig;
use crate::engine_result::build_single_pred_model;
use crate::engine_utils::{
    check_sat_with_timeout, search_budget_exhausted, search_check_sat_with_timeout,
};
use crate::ground_derivation::linear_trace::{engine_trace_counterexample, LinearTrace};
use crate::interpolant_validation::{
    collect_conjuncts_for_interpolation, is_valid_interpolant_with_check_sat,
    validate_inductive_invariant,
};
use crate::interpolation::stats::{self, EngineTag, ExitReason};
use crate::interpolation::{
    interpolating_sat_constraints_with_proof_provenance, proof_interpolant_stats,
    proof_itp_solve_timeouts, InterpolatingSatResult,
};
use crate::pdr::Counterexample;
use crate::smt::SmtResult;
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, ChcSort};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use std::sync::OnceLock;
use std::time::Duration;

/// Attribution-only per-iteration loop stats (rank-4 inc-7), gated on
/// `--chc-imc-stats`. Prints one line per IMC phase (k-check / interpolation /
/// fixpoint) to stderr so wall-time attribution per phase is possible without
/// a profiler. Never on by default; zero effect on the solve itself.
fn imc_stats_enabled() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| ay_core::misc_cli_flags().chc_imc_stats)
}

/// Proof-derived interpolation default for the IMC ROUTE (inc-16 S2).
///
/// Resolution order (first match wins):
///   1. `ImcConfig.proof_interpolants = Some(_)` — explicit config (tests).
///   2. `AY_IMC_PROOF_ITP` env — IMC-route kill switch (`0`/`false` = off).
///   3. `AY_PROOF_INTERPOLANTS` env — the process-wide inc-3 gate, honored
///      when explicitly set.
///   4. Default ON for the IMC route only (inc-16 keystone: derive ONE
///      interpolant from the k-unrolling refutation via the proof-backed
///      module instead of stalling in the per-conjunct cascade; the inc-7
///      A/B measured ON at zero losses). Other consumers of the proof-itp
///      module keep the process-wide default (OFF).
///
/// SOUNDNESS: unchanged — every proof-derived interpolant still passes the
/// existing Craig validation inside the proof path, and IMC's fixpoint +
/// inductive-invariant validation remain mandatory.
fn imc_route_proof_interpolants_enabled() -> bool {
    // B9 deleted the legacy alias; B27 retires the kill-switch env too —
    // the CLI carrier (--chc-no-imc-proof-itp) is the sole opt-out.
    crate::ab_switches::get().imc_proof_itp
}

/// Render an expression for stats lines, truncated to keep logs bounded.
fn stats_expr(expr: &ChcExpr) -> String {
    let s = format!("{expr}");
    if s.len() > 600 {
        let cut = s
            .char_indices()
            .take_while(|(i, _)| *i <= 600)
            .last()
            .map_or(0, |(i, _)| i);
        format!("{}...<{} chars>", &s[..cut], s.len())
    } else {
        s
    }
}

/// A base-check `Unknown` that consumed at least this share of the per-query
/// cap is budget-shaped (the development design notes at 9598c4206, §4.1): the query may be
/// decidable with more time, so it gets exactly one retry.
const BUDGET_SHAPED_FRACTION: f64 = 0.9;

/// What the proof-interpolation path did for one IMC interpolation request,
/// read from the proof path's process-wide counters around the call (IMC is
/// the only default proof-path caller, so the delta is IMC's). The exact
/// `ItpFail` kind is on the ITP-BOARD, attributed to `engine=imc`.
fn proof_path_outcome(
    proof_budget: Option<Duration>,
    before: (usize, usize, usize, usize),
    solve_timeouts_before: usize,
) -> &'static str {
    if proof_budget.is_none() {
        return "off";
    }
    let (served, fallbacks, not_applicable, panics) = proof_interpolant_stats();
    if served > before.0 {
        "served"
    } else if panics > before.3 {
        "panic"
    } else if proof_itp_solve_timeouts() > solve_timeouts_before {
        "budget"
    } else if not_applicable > before.2 {
        "not_applicable"
    } else if fallbacks > before.1 {
        "fallback"
    } else {
        "none"
    }
}

#[cfg(test)]
thread_local! {
    /// Test seam: the next `.0` base checks answer `Unknown` as if they had
    /// used `.1` permille of the per-query cap (1000 = budget-shaped).
    static TEST_FORCE_BASE_UNKNOWN: std::cell::Cell<(usize, u32)> =
        const { std::cell::Cell::new((0, 0)) };
    /// Test seam: replaces `convert_path` in the k→1 step.
    static TEST_K_TO_1_CONVERTER: std::cell::Cell<Option<TestKTo1Converter>> =
        const { std::cell::Cell::new(None) };
}

#[cfg(test)]
type TestKTo1Converter = fn(&ChcExpr, usize, &TransitionSystem) -> Option<ChcExpr>;

/// Apply [`TEST_FORCE_BASE_UNKNOWN`] to one base-check outcome.
#[cfg(test)]
fn test_force_base_unknown(
    result: SmtResult,
    dt: Duration,
    query_timeout: Duration,
) -> (SmtResult, Duration) {
    TEST_FORCE_BASE_UNKNOWN.with(|cell| {
        let (remaining, permille) = cell.get();
        if remaining == 0 {
            return (result, dt);
        }
        cell.set((remaining - 1, permille));
        (SmtResult::Unknown, query_timeout * permille / 1000)
    })
}

/// One-word name of a `validate_inductive_invariant` leg, for `key=value`
/// stats lines.
fn validation_leg_name(leg: &str) -> &'static str {
    match leg {
        "init => invariant" => "init",
        "invariant => not query" => "query",
        "inductiveness" => "inductive",
        _ => "other",
    }
}

/// `sat` / `unsat` / `unknown` for stats lines.
fn smt_verdict_name(result: &SmtResult) -> &'static str {
    if result.is_sat() {
        "sat"
    } else if result.is_unsat() {
        "unsat"
    } else {
        "unknown"
    }
}

/// IMC solver result (type alias for unified ChcEngineResult).
pub(crate) type ImcResult = crate::engine_result::ChcEngineResult;

/// IMC solver configuration.
///
/// Internal — only `Default::default()` is used in production.
#[derive(Debug, Clone)]
pub struct ImcConfig {
    /// Common engine settings (verbose, cancellation).
    pub base: ChcEngineConfig,
    /// Maximum unrolling depth k (default: 100).
    pub max_k: usize,
    /// Maximum iterations per unrolling depth (default: 100).
    pub max_iters_per_k: usize,
    /// Timeout per SMT query.
    pub query_timeout: Duration,
    /// Total solver timeout.
    pub total_timeout: Duration,
    /// Proof-derived interpolation (rank-4 inc-3). `None` reads the
    /// `AY_PROOF_INTERPOLANTS` env gate (default OFF); `Some(_)` forces the
    /// state (tests/diagnostics). When enabled, each interpolation query first
    /// attempts ONE proof-producing ay-dpll solve (budgeted by
    /// `query_timeout`) and uses the resulting interpolant only after it
    /// passes the existing Craig validation; any failure falls back to the
    /// unchanged syntactic cascade.
    pub proof_interpolants: Option<bool>,
}

impl Default for ImcConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_k: 50,
            max_iters_per_k: 100,
            query_timeout: Duration::from_secs(5),
            total_timeout: Duration::from_secs(30),
            proof_interpolants: None,
        }
    }
}

/// IMC solver.
pub(crate) struct ImcSolver {
    problem: ChcProblem,
    config: ImcConfig,
}

impl Drop for ImcSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl ImcSolver {
    pub(crate) fn new(problem: ChcProblem, config: ImcConfig) -> Self {
        Self { problem, config }
    }

    pub(crate) fn solve(&self) -> ImcResult {
        let start = Instant::now();

        let ts = match TransitionSystem::from_chc_problem(&self.problem) {
            Ok(ts) => ts,
            Err(err) => {
                if self.config.base.verbose {
                    safe_eprintln!("IMC: Not applicable: {}", err);
                }
                stats::record_engine_exit_detail(
                    EngineTag::Imc,
                    ExitReason::Other,
                    0,
                    "not_applicable=transition_system",
                );
                return ImcResult::NotApplicable;
            }
        };

        // Sort precheck: IMC interpolation supports arithmetic sorts (Int, Real),
        // Array, AND Bool state variables (F1, the LRA-Lin unlock). Bool state
        // vars are versioned/kept propositional and the interpolating backend's
        // dual-MBP strategy handles mixed Bool+LIA; without this, the mixed
        // Bool+Real predicates that dominate the LRA-Lin track make IMC self-skip
        // even though Golem's IMC solves them in 0.05–1.5s. Soundness: every Safe
        // invariant / Unsafe cex is still replayed against the ORIGINAL clauses
        // by the portfolio acceptance pipeline (#5660/#5877 fail-closed), so a
        // Bool+Real result that fails to validate becomes Unknown.
        // Reference: Golem's IMC also handles Bool+Real, rejecting only arrays
        // (reference/golem/src/engine/IMC.cc:26).
        if let Some(bad_sort) = ts.find_unsupported_interpolation_state_sort_allowing_bool() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "IMC: Not applicable: state variable has unsupported sort {}",
                    bad_sort
                );
            }
            stats::record_engine_exit_detail(
                EngineTag::Imc,
                ExitReason::Other,
                0,
                "not_applicable=state_sort",
            );
            return ImcResult::NotApplicable;
        }
        // IMC-local guard: reject BitVec state sorts. Bool is now admitted (F1);
        // BitVec interpolation is still out of scope for IMC's Craig backend.
        for var in ts.state_vars() {
            if matches!(&var.sort, ChcSort::BitVec(_)) {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "IMC: Not applicable: state variable has non-arithmetic sort {}",
                        var.sort
                    );
                }
                stats::record_engine_exit_detail(
                    EngineTag::Imc,
                    ExitReason::Other,
                    0,
                    "not_applicable=bitvec_state",
                );
                return ImcResult::NotApplicable;
            }
        }

        // Precheck: SAT(init ∧ query) => unsafe at depth 0.
        let init_and_query = ChcExpr::and(ts.init.clone(), ts.query.clone());
        let precheck = self.search_check_sat(&init_and_query);
        if let SmtResult::Sat(model) = &precheck {
            stats::record_engine_exit(EngineTag::Imc, ExitReason::Unsafe, 0);
            return ImcResult::Unsafe(self.unrolling_counterexample(&ts, model, 0));
        } else if !precheck.is_unsat() {
            self.record_budget_or_cancel_exit(ExitReason::BaseUnknown, 0, "precheck=unknown");
            return ImcResult::Unknown;
        }

        let boundary_vars_t1 = ts.state_var_names_at(1);
        let prefix = ts.transition_at(0);
        // Init with its clause locals versioned like every transition copy
        // (`init_at(0)`), so a model of a base check reads as a counterexample
        // (`BmcSolver::counterexample_from_ts_model`).
        let init = ts.init_at(0);

        // Rank-4 inc-3: opt-in proof-derived interpolation budget. The proof
        // attempt is bounded by the SAME per-query timeout the cascade's own
        // SMT checks use, so it never exceeds the cascade's budget shape.
        // Rank-4 inc-7 (attribution): AY_PROOF_ITP_BUDGET_MS overrides the
        // per-query proof budget for offline budget-sensitivity measurements.
        // Only read when the proof path is already opted in; default unchanged.
        let proof_mode = self
            .config
            .proof_interpolants
            .unwrap_or_else(imc_route_proof_interpolants_enabled);
        // B8: the AY_PROOF_ITP_BUDGET_MS env override is deleted; the typed
        // config.query_timeout rules.
        let mut proof_budget = proof_mode.then(|| self.config.query_timeout);
        // Inc-16 S2 strike rule: when the proof-producing solve exhausts its
        // budget without UNSAT (lustre guarded-eq networks: EqDiffVar is
        // disabled under proof production, so the proof-mode solver hits the
        // pre-inc-14 wall), retrying at every (k, iter) only taxes the loop
        // ~proof_budget per iteration. Two budget-exhausted solves in one
        // run disable further attempts; the cascade (bounded by
        // `cascade_budget`) carries the rest of the run.
        const IMC_PROOF_TIMEOUT_STRIKES: usize = 2;
        let mut proof_timeout_strikes = 0usize;
        // Inc-16 S1a: the syntactic cascade must NEVER run unbudgeted from the
        // IMC loop. With proof mode OFF the old path called
        // `interpolating_sat_constraints` with NO deadline, and its strategy
        // legs (dual-MBP AllSAT enumeration, UNSAT-core solve) issue internal
        // `check_sat` calls with `timeout=None` — observed wedging the engine
        // thread for the rest of the wall (ctigar dillig01 k=2: ~55s silence
        // after `theory loop (timeout=None)`). Threading the per-query budget
        // converts that hang into a bounded Unknown (inc-10 pattern); on
        // Unknown the loop breaks to the next k exactly as before.
        let cascade_budget = Some(self.config.query_timeout);

        // Rank-4 inc-7: in (opt-in) proof-itp mode, let the PORTFOLIO's engine
        // budget (enforced by cancellation, both sequential and parallel
        // schedules) be the binding limit instead of the stock 30s internal
        // cap: attribution showed the cap idles the engine for the rest of a
        // 60s window exactly when the loop is making progress. The scaled cap
        // still bounds runaway for any direct (non-portfolio) embedding.
        // Default (proof mode OFF) keeps the configured cap byte-for-byte.
        const PROOF_MODE_TOTAL_BUDGET_SCALE: u32 = 4;
        let total_timeout = if proof_mode {
            self.config.total_timeout * PROOF_MODE_TOTAL_BUDGET_SCALE
        } else {
            self.config.total_timeout
        };

        let stats = imc_stats_enabled();

        for k in 1..=self.config.max_k {
            if search_budget_exhausted(&self.config.base, start, total_timeout) {
                if stats {
                    safe_eprintln!(
                        "[IMC-STATS] exit=budget_at_k k={} elapsed={:.1}s",
                        k,
                        start.elapsed().as_secs_f64()
                    );
                }
                self.record_budget_or_cancel_exit(ExitReason::Budget, k, "at=k_start");
                return ImcResult::Unknown;
            }

            let suffix = Self::build_suffix(&ts, k);
            let mut b_constraints = Vec::new();
            collect_conjuncts_for_interpolation(&suffix, &mut b_constraints);
            let b_flat = ChcExpr::and_all(b_constraints.iter().cloned());
            let mut moving_init = init.clone();
            let mut reached = init.clone();

            if self.config.base.verbose {
                safe_eprintln!("IMC: k={} starting", k);
            }
            if stats {
                safe_eprintln!(
                    "[IMC-STATS] k={} start elapsed={:.1}s b_constraints={}",
                    k,
                    start.elapsed().as_secs_f64(),
                    b_constraints.len()
                );
            }

            for iter in 0..self.config.max_iters_per_k {
                if search_budget_exhausted(&self.config.base, start, total_timeout) {
                    if stats {
                        safe_eprintln!(
                            "[IMC-STATS] exit=budget_in_iter k={} iter={} elapsed={:.1}s",
                            k,
                            iter,
                            start.elapsed().as_secs_f64()
                        );
                    }
                    self.record_budget_or_cancel_exit(
                        ExitReason::Budget,
                        k,
                        &format!("at=iter iter={iter}"),
                    );
                    return ImcResult::Unknown;
                }

                let a = ChcExpr::and(moving_init.clone(), prefix.clone());
                let full = ChcExpr::and(a.clone(), suffix.clone());

                let t_check = Instant::now();
                if stats {
                    safe_eprintln!(
                        "[IMC-STATS {:?}] k={} iter={} bmc_check_start elapsed={:.1}s",
                        std::thread::current().id(),
                        k,
                        iter,
                        start.elapsed().as_secs_f64()
                    );
                }
                let full_result = self.search_check_sat(&full);
                let check_dt = t_check.elapsed();
                #[cfg(test)]
                let (full_result, check_dt) =
                    test_force_base_unknown(full_result, check_dt, self.config.query_timeout);
                let mut full_result = full_result;
                if stats {
                    safe_eprintln!(
                        "[IMC-STATS] k={} iter={} bmc_check={} dt={:.3}s elapsed={:.1}s",
                        k,
                        iter,
                        smt_verdict_name(&full_result),
                        check_dt.as_secs_f64(),
                        start.elapsed().as_secs_f64()
                    );
                }
                // Budget-shaped base-check Unknown: one retry with the rest
                // of the engine budget (§4.1; the portfolio lane deadline
                // still bounds it). An undecided base check ends the run, so
                // the remaining budget has no other use: the LRA-Lin base
                // checks that a 2x cap left undecided (scenario2 k=2, the
                // k=3 stops) get the time Golem's unbounded IMC gives them.
                // A decided retry is the same query's verdict, so it never
                // flips an answer; an undecided retry exits as before.
                let mut budget_shaped = false;
                let mut retried = false;
                if full_result.is_unknown() {
                    budget_shaped = check_dt.as_secs_f64()
                        >= BUDGET_SHAPED_FRACTION * self.config.query_timeout.as_secs_f64();
                    let retry_cap = total_timeout.saturating_sub(start.elapsed());
                    if budget_shaped && !retry_cap.is_zero() && !self.config.base.is_cancelled() {
                        retried = true;
                        let t_retry = Instant::now();
                        full_result = search_check_sat_with_timeout(&full, retry_cap);
                        if stats {
                            safe_eprintln!(
                                "[IMC-STATS] k={} iter={} bmc_retry={} cap={:.1}s dt={:.3}s elapsed={:.1}s",
                                k,
                                iter,
                                smt_verdict_name(&full_result),
                                retry_cap.as_secs_f64(),
                                t_retry.elapsed().as_secs_f64(),
                                start.elapsed().as_secs_f64()
                            );
                        }
                    }
                }
                if let SmtResult::Sat(model) = &full_result {
                    // Real cex only from the true init image (`full` = plain k-step unrolling).
                    if moving_init == init {
                        stats::record_engine_exit(EngineTag::Imc, ExitReason::Unsafe, k);
                        return ImcResult::Unsafe(self.unrolling_counterexample(&ts, model, k));
                    }
                    // Spurious: try larger k.
                    break;
                } else if full_result.is_unknown() {
                    // From an interpolant image (iter > 0) the check is not
                    // the BMC query: an undecided one only ends this k's
                    // sequence, like a failed interpolant, and the next k
                    // builds a different one (om1_with_relays_general_3_10:
                    // k=1 iter=2 undecided in 1.3 s, IMC idle for the rest
                    // of the run). Only the true-init check ends the run.
                    if moving_init != init && !self.config.base.is_cancelled() {
                        if stats {
                            safe_eprintln!(
                                "[IMC-STATS] k={} iter={} image_check=unknown -> next k elapsed={:.1}s",
                                k,
                                iter,
                                start.elapsed().as_secs_f64()
                            );
                        }
                        break;
                    }
                    if stats {
                        safe_eprintln!(
                            "[IMC-STATS] exit=bmc_unknown k={} iter={} elapsed={:.1}s",
                            k,
                            iter,
                            start.elapsed().as_secs_f64()
                        );
                    }
                    self.record_budget_or_cancel_exit(
                        ExitReason::BaseUnknown,
                        k,
                        &format!("iter={iter} budget_shaped={budget_shaped} retried={retried}"),
                    );
                    return ImcResult::Unknown;
                }

                // UNSAT: compute interpolant
                let mut a_constraints = Vec::new();
                collect_conjuncts_for_interpolation(&a, &mut a_constraints);

                let proof_before = proof_interpolant_stats();
                let served_before = proof_before.0;
                let solve_timeouts_before = proof_itp_solve_timeouts();
                let t_itp = Instant::now();
                let (itp_result, proof_validated) =
                    interpolating_sat_constraints_with_proof_provenance(
                        &a_constraints,
                        &b_constraints,
                        &boundary_vars_t1,
                        proof_budget,
                        cascade_budget,
                    );
                // Inc-16 S2 strike rule (see IMC_PROOF_TIMEOUT_STRIKES).
                if proof_budget.is_some() && proof_itp_solve_timeouts() > solve_timeouts_before {
                    proof_timeout_strikes += 1;
                    if proof_timeout_strikes >= IMC_PROOF_TIMEOUT_STRIKES {
                        proof_budget = None;
                        if stats {
                            safe_eprintln!(
                                "[IMC-STATS] k={} iter={} proof_itp=DISABLED after {} budget-exhausted solves",
                                k,
                                iter,
                                proof_timeout_strikes
                            );
                        }
                    }
                }
                let itp_t1 = match itp_result {
                    InterpolatingSatResult::Unsat(i) => i,
                    InterpolatingSatResult::Unknown => {
                        if stats {
                            safe_eprintln!(
                                "[IMC-STATS] k={} iter={} itp=NONE dt={:.3}s elapsed={:.1}s proof={} -> break",
                                k,
                                iter,
                                t_itp.elapsed().as_secs_f64(),
                                start.elapsed().as_secs_f64(),
                                proof_path_outcome(
                                    proof_budget,
                                    proof_before,
                                    solve_timeouts_before
                                )
                            );
                        }
                        break;
                    }
                };
                if stats {
                    let source = if proof_interpolant_stats().0 > served_before {
                        "proof"
                    } else {
                        "cascade"
                    };
                    safe_eprintln!(
                        "[IMC-STATS] k={} iter={} itp_source={} dt={:.3}s elapsed={:.1}s itp={}",
                        k,
                        iter,
                        source,
                        t_itp.elapsed().as_secs_f64(),
                        start.elapsed().as_secs_f64(),
                        stats_expr(&itp_t1)
                    );
                }

                // Validate Craig conditions before using the interpolant.
                // Proof-served interpolants already passed THIS exact gate
                // (`is_valid_interpolant_until` runs the same
                // `is_valid_interpolant_with_check_sat` checks on the same
                // `and_all(a)`/`and_all(b)`/boundary-vars inputs inside the
                // proof path), so re-running it here is a byte-identical
                // duplicate — measured at ~40% of per-iteration cost and the
                // observed wedge point at deeper k (rank-4 inc-7). Cascade
                // results are validated here exactly as before.
                if proof_validated {
                    if stats {
                        safe_eprintln!(
                            "[IMC-STATS] k={} iter={} craig=already_validated_by_proof_path elapsed={:.1}s",
                            k,
                            iter,
                            start.elapsed().as_secs_f64()
                        );
                    }
                } else {
                    let a_flat = ChcExpr::and_all(a_constraints.iter().cloned());
                    let t_val = Instant::now();
                    if !is_valid_interpolant_with_check_sat(
                        &a_flat,
                        &b_flat,
                        &itp_t1,
                        &boundary_vars_t1,
                        |q| self.check_sat(q),
                    ) {
                        if stats {
                            safe_eprintln!(
                                "[IMC-STATS] k={} iter={} craig=FAIL dt={:.3}s elapsed={:.1}s -> break",
                                k,
                                iter,
                                t_val.elapsed().as_secs_f64(),
                                start.elapsed().as_secs_f64()
                            );
                        }
                        break;
                    }
                    if stats {
                        safe_eprintln!(
                            "[IMC-STATS] k={} iter={} craig=ok dt={:.3}s elapsed={:.1}s",
                            k,
                            iter,
                            t_val.elapsed().as_secs_f64(),
                            start.elapsed().as_secs_f64()
                        );
                    }
                }

                let itp = ts.shift_versioned_state_vars(&itp_t1, -1);

                // Fixpoint: if itp ⇒ reached, we're done.
                let itp_and_not_reached = ChcExpr::and(itp.clone(), ChcExpr::not(reached.clone()));
                let t_fix = Instant::now();
                let fixpoint_result = self.search_check_sat(&itp_and_not_reached);
                if stats {
                    safe_eprintln!(
                        "[IMC-STATS] k={} iter={} fixpoint={} dt={:.3}s elapsed={:.1}s",
                        k,
                        iter,
                        if fixpoint_result.is_unsat() {
                            "REACHED"
                        } else if fixpoint_result.is_unknown() {
                            "unknown"
                        } else {
                            "no"
                        },
                        t_fix.elapsed().as_secs_f64(),
                        start.elapsed().as_secs_f64()
                    );
                }
                if fixpoint_result.is_unsat() {
                    match self.build_safe_result(&ts, &reached, k, start, total_timeout) {
                        // No witness from this fixpoint (not 1-inductive and
                        // no k→1 conversion): a larger k builds a different
                        // sequence. Golem's IMC never stops here, its k→1
                        // conversion cannot fail.
                        ImcResult::Unknown
                            if !search_budget_exhausted(
                                &self.config.base,
                                start,
                                total_timeout,
                            ) =>
                        {
                            break;
                        }
                        result => return result,
                    }
                } else if fixpoint_result.is_unknown() {
                    self.record_budget_or_cancel_exit(
                        ExitReason::Other,
                        k,
                        &format!("fixpoint=unknown iter={iter}"),
                    );
                    return ImcResult::Unknown;
                }

                moving_init = itp.clone();
                reached = ChcExpr::or(reached, itp);
            }
        }

        if stats {
            safe_eprintln!(
                "[IMC-STATS] exit=max_k elapsed={:.1}s",
                start.elapsed().as_secs_f64()
            );
        }
        stats::record_engine_exit(EngineTag::Imc, ExitReason::MaxK, self.config.max_k);
        ImcResult::Unknown
    }

    /// `[D-EXIT]` for an undecided exit: `cancelled` when IMC's token was
    /// cancelled (portfolio winner, lane budget), else `reason`.
    fn record_budget_or_cancel_exit(&self, reason: ExitReason, k: usize, detail: &str) {
        let token_cancelled = self
            .config
            .base
            .cancellation_token
            .as_ref()
            .is_some_and(crate::CancellationToken::is_cancelled);
        let reason = if token_cancelled {
            ExitReason::Cancelled
        } else {
            reason
        };
        stats::record_engine_exit_detail(EngineTag::Imc, reason, k, detail);
    }

    /// Pinned check (INV-S2): Craig validation and the final inductive
    /// validation of `build_safe_result`.
    fn check_sat(&self, constraint: &ChcExpr) -> SmtResult {
        check_sat_with_timeout(constraint, self.config.query_timeout)
    }

    /// The counterexample for a SAT `k`-step unrolling
    /// (`init ∧ Tr@0 ∧ … ∧ query@k`): its model as ground evidence, else as a
    /// derivation witness, else a skeleton.
    fn unrolling_counterexample(
        &self,
        ts: &TransitionSystem,
        model: &FxHashMap<String, crate::smt::SmtValue>,
        k: usize,
    ) -> Counterexample {
        let traced = engine_trace_counterexample(
            &self.problem,
            &LinearTrace::from_ts_unrolling(ts, model, k),
            k,
            self.config.base.cancellation_token.as_ref(),
            "IMC",
        );
        if traced.ground_derivation.is_some() {
            return traced;
        }
        // Not ground-validated: the model's derivation witness when every step
        // attributes to a clause (acceptance still re-validates it), else the
        // skeleton.
        crate::BmcSolver::new(self.problem.clone(), crate::BmcConfig::default())
            .counterexample_from_ts_model(ts, model, k)
            .unwrap_or(traced)
    }

    /// Search check (#horn-smt-session Rung 4): the init/query precheck, the
    /// BMC-style full check, the fixpoint check and the strengthening probe.
    /// A wrong answer here can only cost the solve: an Unsafe is re-derived
    /// by the portfolio's pinned counterexample check, a Safe by
    /// `validate_inductive_invariant` on [`Self::check_sat`].
    fn search_check_sat(&self, constraint: &ChcExpr) -> SmtResult {
        search_check_sat_with_timeout(constraint, self.config.query_timeout)
    }

    fn build_suffix(ts: &TransitionSystem, k: usize) -> ChcExpr {
        let mut conjuncts = Vec::new();
        for i in 1..k {
            conjuncts.push(ts.transition_at(i));
        }
        conjuncts.push(ts.query_at(k));
        ChcExpr::and_all(conjuncts)
    }

    fn build_safe_result(
        &self,
        ts: &TransitionSystem,
        reached: &ChcExpr,
        k: usize,
        start: Instant,
        total_timeout: Duration,
    ) -> ImcResult {
        let stats = imc_stats_enabled();
        let mut inv = reached.clone();

        // If inv intersects query, try strengthening with ¬query.
        let inv_and_query = ChcExpr::and(inv.clone(), ts.query.clone());
        let t_q = Instant::now();
        let query_check = self.search_check_sat(&inv_and_query);
        if stats {
            safe_eprintln!(
                "[IMC-STATS] safe_result inv_and_query={} dt={:.3}s",
                if query_check.is_sat() {
                    "sat->strengthen"
                } else if query_check.is_unsat() {
                    "unsat"
                } else {
                    "unknown"
                },
                t_q.elapsed().as_secs_f64()
            );
        }
        match query_check {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Sat(_) => {
                inv = ChcExpr::and(inv, ChcExpr::not(ts.query.clone()));
            }
            SmtResult::Unknown => {
                self.record_budget_or_cancel_exit(
                    ExitReason::Other,
                    k,
                    "safe_result=query_unknown",
                );
                return ImcResult::Unknown;
            }
        }

        let t_v = Instant::now();
        let failed_leg = validate_inductive_invariant(ts, &inv, |q| self.check_sat(q));
        if stats {
            safe_eprintln!(
                "[IMC-STATS] safe_result inductive_validation={} dt={:.3}s",
                failed_leg.unwrap_or("ok"),
                t_v.elapsed().as_secs_f64()
            );
        }
        if let Some(leg) = failed_leg {
            // `reached ∧ ¬query` is only k-inductive (Golem IMC.cc:122-131):
            // convert it with one path-interpolation proof. `convert_path` is
            // self-validating (C-P1): `Some(C)` only when C is 1-inductive,
            // init ⇒ C and C ⇒ inv. That makes C ⇒ ¬query only because
            // `validate_inductive_invariant` checks its legs in order, so a
            // failed `inductiveness` leg means `init ⇒ inv` and `inv ⇒ ¬query`
            // already passed on the pinned lane (INV-S2). On the other legs
            // (`inv ∧ query` not refuted, e.g. a Search/pinned disagreement
            // on the strengthening check above) C ⇒ inv proves nothing about
            // the query, so the candidate is refused exactly as before the
            // k→1 step existed. (The portfolio validates every IMC Safe again.)
            let t_k1 = Instant::now();
            let converted = if leg == "inductiveness" {
                self.convert_k_inductive(ts, &inv, k, start, total_timeout)
            } else {
                None
            };
            if stats {
                safe_eprintln!(
                    "[IMC-STATS] safe_result k_to_1={} k={} failed_leg={} dt={:.3}s",
                    if converted.is_some() {
                        "served"
                    } else {
                        "none"
                    },
                    k,
                    validation_leg_name(leg),
                    t_k1.elapsed().as_secs_f64()
                );
            }
            match converted {
                Some(one_inductive) => inv = one_inductive,
                None => {
                    self.record_budget_or_cancel_exit(
                        ExitReason::Other,
                        k,
                        &format!(
                            "safe_result=not_inductive leg={} k_to_1=none",
                            validation_leg_name(leg)
                        ),
                    );
                    return ImcResult::Unknown;
                }
            }
        }

        let result =
            build_single_pred_model(&self.problem, inv).map_or(ImcResult::Unknown, ImcResult::Safe);
        if stats {
            safe_eprintln!(
                "[IMC-STATS] safe_result model_built={}",
                matches!(result, ImcResult::Safe(_))
            );
        }
        if matches!(result, ImcResult::Safe(_)) {
            stats::record_engine_exit(EngineTag::Imc, ExitReason::Safe, k);
        } else {
            stats::record_engine_exit_detail(EngineTag::Imc, ExitReason::Other, k, "model=none");
        }
        result
    }

    /// k→1 conversion of IMC's k-inductive candidate through the one-proof
    /// path interpolants (`k_to_1_inductive::path::convert_path`, C-P1),
    /// bounded by the engine budget. A panic in the converter is a failed
    /// conversion (`None`), never an engine crash.
    fn convert_k_inductive(
        &self,
        ts: &TransitionSystem,
        k_inv: &ChcExpr,
        k: usize,
        start: Instant,
        total_timeout: Duration,
    ) -> Option<ChcExpr> {
        let remaining = total_timeout.saturating_sub(start.elapsed());
        if k == 0 || remaining.is_zero() || self.config.base.is_cancelled() {
            return None;
        }
        #[cfg(test)]
        if let Some(convert) = TEST_K_TO_1_CONVERTER.with(std::cell::Cell::get) {
            return convert(k_inv, k, ts);
        }
        // D-6 / INV-8: the one-proof k→1 conversion is wired for Real (and
        // Bool) state only until an LIA A/B; integer problems keep the
        // historical Unknown here.
        if ts
            .state_vars()
            .iter()
            .any(|v| !matches!(v.sort, ChcSort::Real | ChcSort::Bool))
        {
            return None;
        }
        let deadline = Instant::now() + remaining;
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            crate::k_to_1_inductive::path::convert_path(k_inv, k, ts, deadline)
        }))
        .ok()
        .flatten()
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
