// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs::{self, File};
use std::io::{self, BufWriter, Read, Write};
use std::panic;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};

use anyhow::{Context, Result};
use clap::Subcommand;

use crate::stats_output::{RunStatistics, SolveMode};
use ay_pb::{
    eval_objective_exact, gf2_parity_detects_unsat_with_recovery, gf2_parity_unsat_cp_checked,
    is_linear, linearize, matching_cardinality_unsat_cp_checked, parse_opb_interruptible,
    parse_wbo_interruptible, pigeonhole_unsat_cp_checked, portfolio,
    profile_jit_candidate_telemetry, try_wbo_to_pbo, write_max_clique_conflict_row_import_map_csv,
    PbCdclResult, PbCdclSolver, PbExactSolution, PbInstance, PbJitCandidateTelemetry,
    PbOutputWriter, PbSolution, PbStatus, WboInstance,
};

const HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS: u64 = 5_000;
const HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS: u32 = 900_000;
const HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS: usize = 1_000_000;
const PARSE_STOP_POLL_INTERVAL: usize = 4096;
const NONLINEAR_OPT_FRONTEND_TIMEOUT_RESERVE_MS: u64 = 600;
/// Wall-clock margin the decision-frontend watchdog stops before the true
/// deadline, so the answer is printed before the competition's CPU-time limit
/// triggers SIGKILL. The decision portfolio runs on a worker thread; a slow
/// internal phase (e.g. a SAT-encoding or native-CDCL loop that polls the
/// termination flag too coarsely) would otherwise overrun the limit by seconds
/// (observed: a 30s limit running to 34s), which in the PB competition means the
/// process is killed before any answer is emitted.
const DECISION_FRONTEND_TIMEOUT_RESERVE_MS: u64 = 500;

/// PB solver subcommands.
#[derive(Subcommand)]
pub(crate) enum PbCommand {
    /// Solve an OPB or WBO pseudo-Boolean instance.
    Solve {
        /// Input file in OPB or WBO format.
        file: PathBuf,

        /// Timeout in milliseconds.
        #[arg(short = 't', long, value_name = "MS")]
        timeout: Option<u64>,

        /// Write VeriPB proof to file.
        #[arg(long, value_name = "FILE")]
        proof: Option<PathBuf>,

        /// Print PB-specific comments before the result.
        #[arg(long)]
        stats: bool,

        /// Print shared stats envelope as JSON to stderr.
        #[arg(long)]
        stats_json: bool,

        /// INTERNAL benchmarking override: force the native PB CDCL engine and
        /// bypass automatic engine selection. Not a normal solving option — the
        /// solver already picks the best engine per instance automatically
        /// (`portfolio::select_strategy`). Kept hidden for A/B measurement
        /// (development sweep tooling) and tests only.
        #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
        native: bool,
    },
}

pub(crate) fn run(cmd: &PbCommand) -> Result<PbStatus> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();

    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        run_with_writer(cmd, &mut handle)
    }));

    match result {
        Ok(inner) => inner,
        Err(_) => {
            let mut out = PbOutputWriter::new(&mut handle);
            let _ = out.write_comment("internal error: solver panicked");
            let _ = out.write_status(PbStatus::Unknown);
            Ok(PbStatus::Unknown)
        }
    }
}

pub(crate) fn pb_exit_code(status: PbStatus) -> i32 {
    match status {
        PbStatus::Satisfiable => 10,
        PbStatus::Unsatisfiable => 20,
        PbStatus::OptimumFound => 30,
        PbStatus::Unknown | PbStatus::Unsupported => 0,
    }
}

fn run_with_writer<W: Write>(cmd: &PbCommand, writer: W) -> Result<PbStatus> {
    match cmd {
        PbCommand::Solve {
            file,
            timeout,
            proof,
            stats,
            stats_json,
            native,
        } => run_solve(
            file,
            proof.as_deref(),
            *timeout,
            *stats,
            *stats_json,
            *native,
            writer,
        ),
    }
}

/// Activate process memory-limit protection for `ay pb solve`.
///
/// PB-COMP supplies the per-instance memory budget in the `MEMLIMIT` (MiB)
/// environment variable. Until a limit is set, every
/// `ay_sys::process_memory_exceeded()` guard throughout the PB solver is dead
/// code, so a pathological allocation (e.g. a large-coefficient SAT encoding
/// or an exact-rational bound computation) OOMs the process instead of
/// returning the best-known answer.
///
/// SOUNDNESS / behavior reconciliation (three explicit cases; the guard is
/// decline-only everywhere, so no case can ever produce a WRONG SAT/UNSAT — the
/// only observable effect is that a near-watermark run may return the best
/// incumbent as SATISFIABLE / Unknown instead of proving OPTIMUM):
///
/// 1. `MEMLIMIT` set to a positive MiB integer (the competition path) — arm it,
///    reserving ~10% headroom so the solver trips its guard and flushes any
///    incumbent BEFORE the harness's hard kill. Mirrors the `ay-pb` binary.
/// 2. `MEMLIMIT` UNSET — arm the physical-RAM-derived standalone default, the
///    same policy the `ay` SAT frontend applies when `--memory` is absent. This
///    protects an interactive machine from a runaway solve; because the default
///    sits at ~85% of physical RAM it only ever engages far past any realistic
///    budget, so the OPTIMUM->SATISFIABLE downgrade it can cause is confined to
///    genuinely machine-threatening runs (where declining is the correct
///    behavior anyway).
/// 3. `MEMLIMIT` set but MALFORMED (e.g. `512MB`, `1.5`) — the user asked for a
///    budget we could not parse. Silently substituting the (possibly far larger)
///    physical default would contradict that intent, so warn on stderr and then
///    fall back to the same protective default as the unset case rather than
///    running fully unguarded. Still decline-only and answer-preserving.
fn apply_memory_limit() {
    let raw = std::env::var("MEMLIMIT")
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty());
    let bytes = match raw.as_deref().map(|v| (v, v.parse::<usize>())) {
        // Case 1: explicit, well-formed, positive budget.
        Some((_, Ok(mib))) if mib > 0 => {
            let limit = mib.saturating_mul(1024 * 1024);
            // ~10% headroom below the hard external limit (RSS keeps growing
            // for a short lag after the guard observes the threshold).
            limit - limit / 10
        }
        // Case 3: MEMLIMIT present but not a positive MiB integer.
        Some((value, _)) => {
            eprintln!(
                "c warning: MEMLIMIT={value:?} is not a positive MiB integer; \
                 using the physical-RAM standalone default memory limit"
            );
            ay_sys::default_standalone_memory_limit()
        }
        // Case 2: MEMLIMIT unset.
        None => ay_sys::default_standalone_memory_limit(),
    };
    if bytes > 0 {
        ay_sys::set_process_memory_limit(bytes);
    }
}

fn run_solve<W: Write>(
    file: &Path,
    proof: Option<&Path>,
    timeout: Option<u64>,
    stats: bool,
    stats_json: bool,
    native: bool,
    writer: W,
) -> Result<PbStatus> {
    apply_memory_limit();
    let solve_start = std::time::Instant::now();
    let sigterm = SigtermMonitor::install().context("failed to install SIGTERM monitor")?;
    let term_flag = sigterm.flag();
    let mut out = PbOutputWriter::new(writer);
    if let Some(proof_path) = proof {
        clear_existing_proof(proof_path)?;
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
    }
    let input_bytes = match read_file_interruptible(file, &mut || {
        term_flag.load(Ordering::SeqCst) || timeout_expired(timeout, solve_start)
    }) {
        Ok(Some(input)) => input,
        Ok(None) => {
            out.write_comment("timeout or termination during PB parse")?;
            out.write_status(PbStatus::Unknown)?;
            emit_pb_json_stats(stats_json, solve_start, PbStatus::Unknown, None, None);
            return Ok(PbStatus::Unknown);
        }
        Err(err) => {
            return Err(err).with_context(|| format!("failed to read '{}'", file.display()));
        }
    };

    let input = std::str::from_utf8(&input_bytes)
        .map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))
        .with_context(|| format!("failed to read '{}'", file.display()))?;
    let format = detect_pb_format(file, input);
    let parse_should_stop = periodic_stop_check(
        term_flag.as_ref(),
        timeout,
        solve_start,
        PARSE_STOP_POLL_INTERVAL,
    );
    let instance = match parse_instance_interruptible(format, input, parse_should_stop) {
        Ok(instance) => instance,
        Err(ay_pb::ParseError::Interrupted { .. }) => {
            out.write_comment("timeout or termination during PB parse")?;
            out.write_status(PbStatus::Unknown)?;
            emit_pb_json_stats(stats_json, solve_start, PbStatus::Unknown, None, None);
            return Ok(PbStatus::Unknown);
        }
        Err(err) if err.is_unsupported_input() => {
            out.write_comment(&format!("unsupported input at parse time: {err}"))?;
            out.write_status(PbStatus::Unsupported)?;
            emit_pb_json_stats(stats_json, solve_start, PbStatus::Unsupported, None, None);
            return Ok(PbStatus::Unsupported);
        }
        Err(err) => {
            return Err(err).with_context(|| format!("failed to parse '{}'", file.display()));
        }
    };

    let best_solution = Mutex::new(None);
    let mut jit_telemetry = if stats || stats_json {
        Some(jit_candidate_telemetry(&instance, timeout))
    } else {
        None
    };

    out.write_comment("ay PB solver v0.1")?;

    if stats {
        write_stats(
            &mut out,
            file,
            &instance,
            timeout,
            jit_telemetry
                .as_ref()
                .expect("PB stats requested telemetry above"),
        )?;
    }

    if term_flag.load(Ordering::SeqCst) {
        write_best_known_result(&mut out, &best_solution)?;
        emit_pb_json_stats(
            stats_json,
            solve_start,
            PbStatus::Unknown,
            jit_telemetry.as_ref(),
            None,
        );
        return Ok(PbStatus::Unknown);
    }

    let result = solve_pb(
        &instance,
        proof,
        timeout,
        solve_start,
        native,
        stats_json,
        term_flag.as_ref(),
        &mut out,
        &best_solution,
        Some(input),
    );

    let mut result = match result {
        Ok(solution) => solution,
        Err(e) if proof.is_some() => return Err(e),
        Err(e) => {
            out.write_comment(&format!("internal error: {e}"))?;
            out.write_status(PbStatus::Unknown)?;
            emit_pb_json_stats(
                stats_json,
                solve_start,
                PbStatus::Unknown,
                jit_telemetry.as_ref(),
                None,
            );
            return Ok(PbStatus::Unknown);
        }
    };
    if let Some(telemetry) = jit_telemetry.as_mut() {
        telemetry.pb_native_code_helper_applications = result.pb_native_code_helper_applications;
    }

    // DECISION-SAT Verified-SAT-Gate: every decision (`objective.is_none()`) SAT
    // path — native, portfolio, frontend-timeout, and proof — funnels through here
    // before emit. Re-verify the returned model against the ORIGINAL constraints
    // with the proven `ay_pb::verify_all_constraints`; fail-closed to UNKNOWN if it
    // does not satisfy every constraint, so a wrong `s SATISFIABLE` is impossible
    // by construction. Feasible models pass through unchanged (0 regression).
    // Optimization instances are skipped: their incumbent is already re-verified by
    // the incumbent VIG (`sanitize_optimization_incumbent`).
    if let ParsedPbInstance::Opb(pb) = &instance {
        if pb.objective.is_none() {
            result.solution = decision_sat_self_checked(result.solution, pb);
        }
    }

    let termination_requested = term_flag.load(Ordering::SeqCst);
    let final_status = write_result_or_best_known(
        &mut out,
        &result.solution,
        termination_requested,
        &best_solution,
    )?;

    let elapsed = solve_start.elapsed();
    if stats {
        if let Some(timings) = &result.portfolio_timings {
            write_portfolio_timing_stats(&mut out, timings)?;
        }
    }
    out.write_comment(&format!("solve time: {:.3}s", elapsed.as_secs_f64()))?;
    emit_pb_json_stats(
        stats_json,
        solve_start,
        final_status,
        jit_telemetry.as_ref(),
        result.portfolio_timings.as_ref(),
    );

    Ok(final_status)
}

/// Solves a PB instance.
///
/// For decision problems with proof logging enabled, use the native PB CDCL
/// solver so it can emit a VeriPB proof. Other decision problems are encoded to
/// CNF and solved once with the SAT solver.
/// Optimization proof logging uses the native PB CDCL path for linear OPB.
/// WBO and non-linear certified solving are rejected rather than silently
/// solving uncertified.
fn solve_pb<W: Write>(
    instance: &ParsedPbInstance,
    proof: Option<&Path>,
    timeout: Option<u64>,
    solve_start: std::time::Instant,
    native: bool,
    collect_native_helper_applications: bool,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
    source_text: Option<&str>,
) -> Result<PbSolveOutcome> {
    if let Some(proof_path) = proof {
        clear_existing_proof(proof_path)?;
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
    }

    if proof.is_some() {
        if let ParsedPbInstance::Opb(pb) = instance {
            if is_linear(pb) {
                if pb.objective.is_some() {
                    if let Some(label) = dobutsu_no_cert_parsed_optimization_label(pb) {
                        out.write_comment(&format!(
                            "{label} incumbent is no-certificate; proof mode is unsupported",
                        ))?;
                        return Ok(PbSolveOutcome::without_native_helpers(
                            unsupported_solution(),
                        ));
                    }
                }
            }
        }
    }

    if term_flag.load(Ordering::SeqCst) || timeout_expired(timeout, solve_start) {
        if proof.is_some() {
            let mut guard = best_solution
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            *guard = None;
        }
        return Ok(PbSolveOutcome::without_native_helpers(PbSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: None,
        }));
    }

    match instance {
        ParsedPbInstance::Opb(pb) => solve_opb(
            pb,
            proof,
            timeout,
            solve_start,
            native,
            collect_native_helper_applications,
            term_flag,
            out,
            best_solution,
            None,
            source_text,
        ),
        ParsedPbInstance::Wbo(wbo) => {
            if proof.is_some() {
                out.write_comment(
                    "proof logging for WBO is not supported; refusing uncertified solve",
                )?;
                return Ok(PbSolveOutcome::without_native_helpers(
                    unsupported_solution(),
                ));
            }
            // Official WBO semantics admit only models whose falsified-soft
            // cost is STRICTLY LESS than the `soft:` top cost. Costs are
            // non-negative, so a top cost <= 0 admits no model regardless of
            // the constraints (the converter's falsity backstop row covers
            // any other caller). The non-negativity premise is only validated
            // by the converter (NegativeSoftCost), so when a parser-accepted
            // negative weight is present, fall through to its fail-closed
            // UNSUPPORTED instead of asserting a verdict.
            if wbo.top_cost.is_some_and(|top| top <= 0)
                && wbo.soft_constraints.iter().all(|(cost, _)| *cost >= 0)
            {
                out.write_comment("WBO top cost admits no model (every cost is >= 0)")?;
                return Ok(PbSolveOutcome::without_native_helpers(PbSolution {
                    status: PbStatus::Unsatisfiable,
                    assignment: Vec::new(),
                    objective: None,
                }));
            }
            // Root EDAC/VAC-lite lower-bound probe over the reconstructed
            // WCSP view (campaign soft-1; opt-in AY_PB_WCSP_EDAC=1, default
            // OFF). Soundness of the UNSAT verdict: the probe's `c0` is a
            // trail-CHECKED floor on the falsified-soft cost of EVERY
            // assignment satisfying the instance's hard one-hot rows (the
            // probe returns Some only after `check_wcsp_transfer_trail`
            // independently replayed its audit trail against a fresh
            // reconstruction); assignments violating any hard row are not
            // models either, and official WBO semantics admit only models
            // with cost STRICTLY LESS than `top` — so `c0 >= top` proves
            // there is no model at all. Costs are verified non-negative by
            // the reconstruction itself (it declines negative soft weights),
            // independent of the converter's NegativeSoftCost path.
            if ay_pb::wcsp_edac_enabled() {
                if let (Some(top), Some(probe)) = (
                    wbo.top_cost,
                    ay_pb::wcsp_root_edac_probe(wbo, Some(term_flag)),
                ) {
                    out.write_comment(&format!(
                        "wcsp edac root probe: c0={} top={top} domains={} trail={} fixpoint={}",
                        probe.c0, probe.num_domains, probe.trail_len, probe.fixpoint
                    ))?;
                    if probe.c0 >= top {
                        out.write_comment(
                            "wcsp edac trail-checked floor reaches top cost: no admissible model",
                        )?;
                        return Ok(PbSolveOutcome::without_native_helpers(PbSolution {
                            status: PbStatus::Unsatisfiable,
                            assignment: Vec::new(),
                            objective: None,
                        }));
                    }
                }
            }
            let pbo = match try_wbo_to_pbo(wbo) {
                Ok(pbo) => pbo,
                Err(err) => {
                    out.write_comment(&format!("unsupported WBO conversion: {err}"))?;
                    return Ok(PbSolveOutcome::without_native_helpers(
                        unsupported_solution(),
                    ));
                }
            };
            let wbo_best_solution = Mutex::new(None);
            let solution = solve_opb(
                &Arc::new(pbo),
                None,
                timeout,
                solve_start,
                native,
                collect_native_helper_applications,
                term_flag,
                out,
                &wbo_best_solution,
                Some(wbo),
                None,
            )?;

            let maybe_best = wbo_best_solution
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .clone();
            if let Some(best) = maybe_best {
                let mut guard = best_solution
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                *guard = Some(best);
            }

            Ok(solution)
        }
    }
}

struct PbSolveOutcome {
    solution: PbSolution,
    pb_native_code_helper_applications: u64,
    portfolio_timings: Option<portfolio::PbPortfolioPhaseTimings>,
}

impl PbSolveOutcome {
    fn without_native_helpers(solution: PbSolution) -> Self {
        Self {
            solution,
            pb_native_code_helper_applications: 0,
            portfolio_timings: None,
        }
    }
}

/// Solves an OPB instance (decision or optimization).
///
/// Strategy selection:
/// - `--proof`: native PB CDCL with VeriPB proof logging
///   linear optimization instances use the native optimization proof path
/// - `--native`: force native PB CDCL solver
/// - default: portfolio solver (automatic strategy selection)
fn solve_opb<W: Write>(
    instance_arc: &Arc<PbInstance>,
    proof: Option<&Path>,
    timeout: Option<u64>,
    start: std::time::Instant,
    native: bool,
    collect_native_helper_applications: bool,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
    wbo_projection: Option<&WboInstance>,
    source_opb_text: Option<&str>,
) -> Result<PbSolveOutcome> {
    // Telemetry sink is process-scoped and monotone: clear it so a dual proven
    // for a PREVIOUS instance can never be reported against this one.
    ay_pb::optimize::shared_bounds::reset_reported_dual_global();
    // Borrowed view for the body; the `Arc` itself is only needed by the
    // decision frontend-timeout path (shared ownership for its worker thread).
    let instance: &PbInstance = instance_arc;
    let timeout_dur = timeout.map(std::time::Duration::from_millis);

    // Proof mode: must use native PB CDCL for VeriPB proof emission.
    if let Some(proof_path) = proof {
        clear_existing_proof(proof_path)?;
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
        if !is_linear(instance) {
            out.write_comment(
                "proof logging for non-linear PB is not supported; refusing uncertified solve",
            )?;
            return Ok(PbSolveOutcome::without_native_helpers(
                unsupported_solution(),
            ));
        }
        if let Some(objective) = instance.objective.as_ref() {
            if let Some(label) = dobutsu_no_cert_parsed_optimization_label(instance) {
                out.write_comment(&format!(
                    "{label} incumbent is no-certificate; proof mode is unsupported",
                ))?;
                return Ok(PbSolveOutcome::without_native_helpers(
                    unsupported_solution(),
                ));
            }
            maybe_write_clique_conflict_row_import_map_sidecar(
                instance,
                objective,
                source_opb_text,
                proof_path,
                timeout,
                start,
                term_flag,
                out,
            )?;
            return solve_optimization_with_proof(
                instance,
                objective,
                proof_path,
                timeout_dur,
                start,
                term_flag,
                collect_native_helper_applications,
                out,
                best_solution,
            );
        }
        if let Some(outcome) = try_exact_decision_sat_incumbent_with_proof(
            instance,
            proof_path,
            timeout_dur,
            start,
            term_flag,
        )? {
            return Ok(outcome);
        }
        // Strong SAT-encoding DRAT-lift certified-UNSAT route (DEC-LIN-CERT): solve
        // the CNF encoding with ay-sat and lift its DRAT refutation to a VeriPB
        // proof. Certifies aux-free decision instances the native engine cannot
        // solve (e.g. koops mat98); declines (-> native fallback below) on SAT,
        // interrupt, or a not-yet-liftable encoding.
        if let Some(outcome) =
            try_drat_lift_certified_unsat(instance, proof_path, timeout_dur, start, term_flag)?
        {
            return Ok(outcome);
        }
        return solve_decision_with_proof(
            instance,
            proof_path,
            timeout_dur,
            start,
            term_flag,
            collect_native_helper_applications,
        );
    }

    // EARLY self-checked structural-UNSAT recognizers. These O(n+m), size-capped,
    // fail-closed recognizers emit UNSAT only when an explicit cutting-planes /
    // GF(2) refutation over the ORIGINAL rows replays to `0 >= 1` against the
    // kernel-verified algebra. They MUST run here — BEFORE the full-timeout native
    // decision solve (`solve_decision_native`) and the decision portfolio below —
    // because a NATIVE LINEAR DECISION instance takes the
    // `solve_decision_native(.., timeout_dur, ..)` branch (or the portfolio) for
    // its FULL budget and `return`s straight out. This MAIN `ay` CLI has its own
    // duplicated solve path and carried NO structural recognizers, so pure
    // pigeonhole (php-original, php-exit v1), GF(2)-parity, and even-colouring
    // UNSAT instances ran the entire budget and printed `s UNKNOWN` even though a
    // recognizer decides them in well under a second. Running them here first hands
    // those families an instant certificate on the submission binary.
    //
    // SOUND: a feasible (SAT) instance can never produce a self-checked `0 >= 1`,
    // so this can NEVER flip SAT to UNSAT. ZERO-REGRESSION: the pass is cheap and
    // fail-closed, declining fast on every non-matching shape; the SAT / OPTIMUM
    // paths are untouched (the guard is `objective.is_none()`). `proof.is_none()`
    // holds unconditionally here (the proof branch returned earlier in `solve_opb`),
    // keeping the certified-proof path on its own dedicated emission route.
    if instance.objective.is_none() && proof.is_none() && structural_unsat_self_checked(instance) {
        if std::env::var_os("AY_CERT_DEBUG").is_some() {
            eprintln!(
                "c refutation self-checked EARLY: structural 0>=1 (kernel-algebra), \
                 emitting s UNSATISFIABLE"
            );
        }
        return Ok(structural_unsat_outcome());
    }

    // Explicit --native flag: force native PB CDCL.
    if native {
        if instance.objective.is_none() {
            if is_linear(instance) {
                return solve_decision_native(
                    instance,
                    timeout_dur,
                    start,
                    term_flag,
                    collect_native_helper_applications,
                );
            }
            let linearized = linearize(instance);
            let mut outcome = solve_decision_native(
                &linearized,
                timeout_dur,
                start,
                term_flag,
                collect_native_helper_applications,
            )?;
            outcome.solution = project_solution_assignment(outcome.solution, instance.num_vars);
            return Ok(outcome);
        }
        // For optimization with --native, fall through to portfolio
        // (native optimization is part of portfolio).
    }

    // Default: portfolio solver with automatic strategy selection.
    if instance.objective.is_none() {
        // With a deadline, run the decision portfolio under a frontend watchdog
        // so a slow internal phase can never overrun the wall clock (it would
        // get SIGKILL'd before printing). Without a deadline there is nothing to
        // enforce, so run inline and skip the worker-thread/clone overhead.
        if let Some(timeout_dur) = timeout_dur {
            return solve_decision_with_frontend_timeout(
                instance_arc,
                timeout_dur,
                start,
                term_flag,
            );
        }
        let portfolio_result = portfolio::solve_decision_portfolio_with_timings(
            instance,
            timeout_dur,
            start,
            term_flag,
        );
        return Ok(PbSolveOutcome {
            solution: portfolio_result.solution,
            pb_native_code_helper_applications: 0,
            portfolio_timings: Some(portfolio_result.timings),
        });
    }

    // Optimization: use portfolio-based optimization.
    // Write intermediate `o` lines for anytime behavior (flushed immediately).
    // Deduplicate: only emit `o` when value strictly improves (decreases).
    let objective = instance.objective.as_ref().expect("checked above");
    // NON-LINEAR front-end-timeout wrapper — UNLESS the parallel portfolio
    // takes the instance (`should_parallelize_optimization`, batteries-included
    // default on multi-core): the parallel route runs its own NLC-safe worker
    // set (P1 = the full sequential routing on a dedicated core, the internally
    // linearizing SAT-encoded arms, and the product-native `nlc-sls-opt`
    // primal) and enforces the wall clock itself via the coordinator's hard
    // collection deadline. With parallelism unavailable (`AY_PB_PARALLEL=0` /
    // single core / memory clamp) this sequential wrapper path is
    // byte-identical to before.
    if wbo_projection.is_none()
        && !is_linear(instance)
        && timeout_dur.is_some()
        && !instance.constraints.is_empty()
        && !portfolio::should_parallelize_optimization(instance)
    {
        return solve_nonlinear_optimization_with_frontend_timeout(
            instance,
            objective,
            timeout_dur,
            start,
            term_flag,
            out,
            best_solution,
        );
    }

    let mut best_obj: Option<i128> = None;
    let mut streamed_best_obj: Option<i128> = None;
    let mut on_improve = |obj_value: i128, model: &[bool]| {
        let exact_solution = exact_incumbent_from_model(
            instance,
            objective,
            wbo_projection,
            PbStatus::Satisfiable,
            obj_value,
            best_obj,
            model,
        );
        let Some(exact_obj_value) = exact_solution.objective else {
            return;
        };
        let dominated = best_obj.is_some_and(|prev| exact_obj_value >= prev);
        if dominated {
            return;
        }

        // The bar advances only from a VERIFIED construction (the helper
        // fails closed to `objective: None` on an infeasible model above).
        best_obj = Some(exact_obj_value);
        if wbo_projection.is_none() {
            let _ = out.write_objective_exact(exact_obj_value);
            streamed_best_obj = Some(exact_obj_value);
        }
        cache_exact_solution(best_solution, exact_solution);
    };
    // PARALLEL OPTIMIZATION TRACK (batteries-included default; design §2.3):
    // when the memory-clamped core budget is >= 2 (`AY_PB_PARALLEL` unset
    // defaults to AUTO, `NBCORE`-sized; `=0` disables) and the instance is
    // eligible (`should_parallelize_optimization` — linear, the NLC-safe
    // non-linear subset, and WBO reductions, which are linear by
    // construction) — run the diverse-strategy parallel portfolio. Its
    // priority-1 worker IS the full sequential routing on a dedicated core
    // (never weaker than baseline), a definitive verdict is adopted only from
    // a complete baseline engine, and every incumbent streams through the
    // coordinator's `sanitize_optimization_incumbent` gate into the SAME
    // `on_improve` as the sequential path (its strict-improvement filter
    // keeps the `o` line stream monotone). Huge instances degrade gracefully
    // toward sequential via the memory clamp inside the parallel entry. Proof
    // mode never reaches here (the `proof` branch returned at the top of
    // `solve_opb`). WBO: the parallel route only changes WHO searches the
    // REDUCED PBO (`try_wbo_to_pbo` output, including its top-cost budget
    // row); incumbents flow through this SAME `on_improve` closure (which
    // re-projects + re-scores against the ORIGINAL WBO via
    // `exact_incumbent_from_model` and suppresses intermediate `o` lines
    // under `wbo_projection.is_some()`), and the final result takes the
    // identical `project_wbo_solution` /
    // `prefer_cheaper_cached_wbo_incumbent` /
    // `exact_wbo_solution_from_assignment` top-cost fail-closed gates below.
    let (portfolio_solution_raw, portfolio_timings) =
        if portfolio::should_parallelize_optimization(instance) {
            let parallel_solution = if wbo_projection.is_some() {
                portfolio::solve_wbo_reduced_optimization_portfolio_parallel(
                    instance_arc,
                    objective,
                    timeout_dur,
                    start,
                    term_flag,
                    &mut on_improve,
                )
            } else {
                portfolio::solve_optimization_portfolio_parallel(
                    instance_arc,
                    objective,
                    timeout_dur,
                    start,
                    term_flag,
                    &mut on_improve,
                )
            };
            (parallel_solution, None)
        } else {
            let portfolio_result = portfolio::solve_optimization_portfolio_with_timings(
                instance,
                objective,
                timeout_dur,
                start,
                term_flag,
                &mut on_improve,
            );
            (portfolio_result.solution, Some(portfolio_result.timings))
        };
    let result = match wbo_projection {
        Some(wbo) => project_wbo_solution(portfolio_solution_raw, wbo),
        None => portfolio_solution_raw,
    };
    // WBO final-answer reconciliation: the portfolio ranks incumbents by the
    // relaxed-PBO objective, which can overstate the true cost (a spurious
    // r_i = 1 on a soft that is actually satisfied), while the streamed cache
    // ranks by the re-scored true cost — so the portfolio's final model can be
    // strictly costlier than an incumbent already cached. Emit the cheaper
    // one. Not needed for OptimumFound: the proven optimum's true cost is
    // minimal, so no cached incumbent can beat it.
    let result = if wbo_projection.is_some() && result.status == PbStatus::Satisfiable {
        prefer_cheaper_cached_wbo_incumbent(result, best_solution)
    } else {
        result
    };
    if result.status == PbStatus::OptimumFound || result.status == PbStatus::Satisfiable {
        let mut guard = best_solution
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        *guard = Some(match wbo_projection {
            Some(wbo) => exact_wbo_solution_from_assignment(
                wbo,
                result.status,
                &result.assignment,
                result.objective,
            ),
            None => exact_solution_from_result(&result, objective),
        });
    }
    // Intermediate `o` lines were already written by on_improve above. Suppress
    // only a duplicate final objective; interrupted incumbents can arrive here
    // before any anytime objective line was streamed.
    Ok(PbSolveOutcome {
        solution: final_optimization_result_after_anytime_stream(result, streamed_best_obj),
        pb_native_code_helper_applications: 0,
        portfolio_timings,
    })
}

enum OptimizationWorkerEvent {
    Improvement(PbExactSolution),
    Done(portfolio::PbPortfolioOutcome),
}

fn solve_nonlinear_optimization_with_frontend_timeout<W: Write>(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    timeout_dur: Option<std::time::Duration>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> Result<PbSolveOutcome> {
    let Some(timeout_dur) = timeout_dur else {
        unreachable!("caller only uses front-end timeout wrapper when timeout is present");
    };
    if objective_has_only_nonnegative_coefficients(objective) {
        if let Some(outcome) = try_nonlinear_optimization_probe(
            instance,
            objective,
            std::time::Duration::from_millis(1),
            std::time::Duration::from_millis(250),
            term_flag,
            out,
            best_solution,
        )? {
            return Ok(outcome);
        }
        if instance.num_vars <= 64 {
            if let Some(outcome) = try_nonlinear_optimization_probe(
                instance,
                objective,
                std::time::Duration::from_secs(1),
                std::time::Duration::from_millis(2_500),
                term_flag,
                out,
                best_solution,
            )? {
                return Ok(outcome);
            }
        }
    }

    let deadline = nonlinear_frontend_deadline(start, timeout_dur);
    let worker_stop = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();
    let worker_instance = instance.clone();
    let worker_objective = objective.clone();
    let worker_stop_for_thread = Arc::clone(&worker_stop);
    let worker = std::thread::spawn(move || {
        let mut best_obj: Option<i128> = None;
        let mut on_improve = |obj_value: i128, model: &[bool]| {
            let exact_solution = exact_incumbent_from_model(
                &worker_instance,
                &worker_objective,
                None,
                PbStatus::Satisfiable,
                obj_value,
                best_obj,
                model,
            );
            let Some(exact_obj_value) = exact_solution.objective else {
                return;
            };
            if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                return;
            }
            best_obj = Some(exact_obj_value);
            let _ = tx.send(OptimizationWorkerEvent::Improvement(exact_solution));
        };
        let result = portfolio::solve_optimization_portfolio_with_timings(
            &worker_instance,
            &worker_objective,
            Some(timeout_dur),
            start,
            worker_stop_for_thread.as_ref(),
            &mut on_improve,
        );
        let _ = tx.send(OptimizationWorkerEvent::Done(result));
    });

    let mut streamed_best_obj: Option<i128> = None;
    let mut best_obj: Option<i128> = None;
    loop {
        if term_flag.load(Ordering::SeqCst) || std::time::Instant::now() >= deadline {
            worker_stop.store(true, Ordering::SeqCst);
            let result = best_known_legacy_solution(best_solution);
            return Ok(PbSolveOutcome {
                solution: final_optimization_result_after_anytime_stream(result, streamed_best_obj),
                pb_native_code_helper_applications: 0,
                portfolio_timings: None,
            });
        }

        let wait = deadline
            .saturating_duration_since(std::time::Instant::now())
            .min(std::time::Duration::from_millis(10));
        match rx.recv_timeout(wait) {
            Ok(OptimizationWorkerEvent::Improvement(exact_solution)) => {
                let Some(exact_obj_value) = exact_solution.objective else {
                    continue;
                };
                if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                    continue;
                }
                best_obj = Some(exact_obj_value);
                out.write_objective_exact(exact_obj_value)?;
                streamed_best_obj = Some(exact_obj_value);
                cache_exact_solution(best_solution, exact_solution);
            }
            Ok(OptimizationWorkerEvent::Done(portfolio_result)) => {
                let _ = worker.join();
                let result = portfolio_result.solution;
                if result.status == PbStatus::OptimumFound || result.status == PbStatus::Satisfiable
                {
                    let mut guard = best_solution
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    *guard = Some(exact_solution_from_result(&result, objective));
                }
                return Ok(PbSolveOutcome {
                    solution: final_optimization_result_after_anytime_stream(
                        result,
                        streamed_best_obj,
                    ),
                    pb_native_code_helper_applications: 0,
                    portfolio_timings: Some(portfolio_result.timings),
                });
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                let _ = worker.join();
                return Ok(PbSolveOutcome {
                    solution: unknown_solution(),
                    pb_native_code_helper_applications: 0,
                    portfolio_timings: None,
                });
            }
        }
    }
}

fn nonlinear_frontend_deadline(
    start: std::time::Instant,
    timeout_dur: std::time::Duration,
) -> std::time::Instant {
    let deadline = start + timeout_dur;
    deadline
        .checked_sub(std::time::Duration::from_millis(
            NONLINEAR_OPT_FRONTEND_TIMEOUT_RESERVE_MS,
        ))
        .filter(|reserved| *reserved > start)
        .unwrap_or(start)
}

fn decision_frontend_deadline(
    start: std::time::Instant,
    timeout_dur: std::time::Duration,
) -> std::time::Instant {
    let deadline = start + timeout_dur;
    deadline
        .checked_sub(std::time::Duration::from_millis(
            DECISION_FRONTEND_TIMEOUT_RESERVE_MS,
        ))
        .filter(|reserved| *reserved > start)
        .unwrap_or(start)
}

/// Runs the decision portfolio on a worker thread and enforces the wall-clock
/// deadline from the main thread. Mirrors the optimization frontend watchdog:
/// the portfolio can return a real answer (SAT/UNSAT, including the model) right
/// up to the deadline, but if it is still grinding when the deadline arrives the
/// main thread returns `UNKNOWN` immediately rather than letting a coarse
/// internal poll overrun the limit. The worker is signalled to stop and then
/// abandoned (the process exits shortly after, terminating it); it never writes
/// to stdout, so abandoning it cannot corrupt output.
fn solve_decision_with_frontend_timeout(
    instance: &Arc<PbInstance>,
    timeout_dur: std::time::Duration,
    start: std::time::Instant,
    term_flag: &AtomicBool,
) -> Result<PbSolveOutcome> {
    let deadline = decision_frontend_deadline(start, timeout_dur);
    let worker_stop = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();
    // Shared ownership for the detached worker (it may outlive this frame on
    // timeout): a refcount bump instead of the previous full-instance clone,
    // which burned a few tenths of a second of the budget at 6.4M rows before
    // the search started (~0.3s measured for the same-shape row copy on
    // lopes-172; ~0.7s on the loaded phase-6 profile).
    let worker_instance = Arc::clone(instance);
    let worker_stop_for_thread = Arc::clone(&worker_stop);
    let worker = std::thread::spawn(move || {
        let result = portfolio::solve_decision_portfolio_with_timings(
            &worker_instance,
            Some(timeout_dur),
            start,
            worker_stop_for_thread.as_ref(),
        );
        let _ = tx.send(result);
    });

    loop {
        if term_flag.load(Ordering::SeqCst) || std::time::Instant::now() >= deadline {
            // Signal the worker and return what we have (nothing decided yet).
            worker_stop.store(true, Ordering::SeqCst);
            return Ok(PbSolveOutcome {
                solution: unknown_solution(),
                pb_native_code_helper_applications: 0,
                portfolio_timings: None,
            });
        }

        let wait = deadline
            .saturating_duration_since(std::time::Instant::now())
            .min(std::time::Duration::from_millis(10));
        match rx.recv_timeout(wait) {
            Ok(portfolio_result) => {
                let _ = worker.join();
                return Ok(PbSolveOutcome {
                    solution: portfolio_result.solution,
                    pb_native_code_helper_applications: 0,
                    portfolio_timings: Some(portfolio_result.timings),
                });
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                let _ = worker.join();
                return Ok(PbSolveOutcome {
                    solution: unknown_solution(),
                    pb_native_code_helper_applications: 0,
                    portfolio_timings: None,
                });
            }
        }
    }
}

fn objective_has_only_nonnegative_coefficients(objective: &ay_pb::PbObjective) -> bool {
    objective.terms.iter().all(|term| term.coeff >= 0)
}

fn try_nonlinear_optimization_probe<W: Write>(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    solver_timeout: std::time::Duration,
    wait_budget: std::time::Duration,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> Result<Option<PbSolveOutcome>> {
    let probe_start = std::time::Instant::now();
    let deadline = probe_start + wait_budget;
    let worker_stop = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();
    let worker_instance = instance.clone();
    let worker_objective = objective.clone();
    let worker_stop_for_thread = Arc::clone(&worker_stop);
    let worker = std::thread::spawn(move || {
        let mut best_obj: Option<i128> = None;
        let mut on_improve = |obj_value: i128, model: &[bool]| {
            let exact_solution = exact_incumbent_from_model(
                &worker_instance,
                &worker_objective,
                None,
                PbStatus::Satisfiable,
                obj_value,
                best_obj,
                model,
            );
            let Some(exact_obj_value) = exact_solution.objective else {
                return;
            };
            if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                return;
            }
            best_obj = Some(exact_obj_value);
            let _ = tx.send(OptimizationWorkerEvent::Improvement(exact_solution));
        };
        let result = portfolio::solve_optimization_portfolio_with_timings(
            &worker_instance,
            &worker_objective,
            Some(solver_timeout),
            probe_start,
            worker_stop_for_thread.as_ref(),
            &mut on_improve,
        );
        let _ = tx.send(OptimizationWorkerEvent::Done(result));
    });

    let mut streamed_best_obj: Option<i128> = None;
    let mut best_obj: Option<i128> = None;
    loop {
        if term_flag.load(Ordering::SeqCst) || std::time::Instant::now() >= deadline {
            worker_stop.store(true, Ordering::SeqCst);
            // On a real SIGTERM, surface the best incumbent now (we are being
            // killed). If only the probe's own (short) wait budget elapsed,
            // return None so the caller runs the FULL optimization with the
            // remaining budget: a feasible probe result is not a proof of
            // optimality and scores zero on OPT tracks. The incumbent is already
            // cached in `best_solution`, so it is not lost.
            if term_flag.load(Ordering::SeqCst) {
                let result = best_known_legacy_solution(best_solution);
                if result.status == PbStatus::Satisfiable || result.status == PbStatus::OptimumFound
                {
                    return Ok(Some(PbSolveOutcome {
                        solution: final_optimization_result_after_anytime_stream(
                            result,
                            streamed_best_obj,
                        ),
                        pb_native_code_helper_applications: 0,
                        portfolio_timings: None,
                    }));
                }
            }
            return Ok(None);
        }

        let wait = deadline
            .saturating_duration_since(std::time::Instant::now())
            .min(std::time::Duration::from_millis(10));
        match rx.recv_timeout(wait) {
            Ok(OptimizationWorkerEvent::Improvement(exact_solution)) => {
                let Some(exact_obj_value) = exact_solution.objective else {
                    continue;
                };
                if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                    continue;
                }
                best_obj = Some(exact_obj_value);
                out.write_objective_exact(exact_obj_value)?;
                streamed_best_obj = Some(exact_obj_value);
                cache_exact_solution(best_solution, exact_solution);
            }
            Ok(OptimizationWorkerEvent::Done(portfolio_result)) => {
                let _ = worker.join();
                let result = portfolio_result.solution;
                // Always cache a feasible incumbent so the full optimization
                // phase keeps it as its starting point / interrupt fallback.
                if result.status == PbStatus::OptimumFound || result.status == PbStatus::Satisfiable
                {
                    let mut guard = best_solution
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    *guard = Some(exact_solution_from_result(&result, objective));
                }
                // Only a DEFINITIVE verdict (proven optimum or UNSAT) ends the
                // solve in the probe. A mere `Satisfiable` is a feasible
                // incumbent, not a proof of optimality, and scores zero on OPT
                // tracks — so return None and let the caller run the full
                // optimization with the remaining budget (it keeps the cached
                // incumbent above and can prove the optimum).
                if result.status == PbStatus::OptimumFound
                    || result.status == PbStatus::Unsatisfiable
                {
                    return Ok(Some(PbSolveOutcome {
                        solution: final_optimization_result_after_anytime_stream(
                            result,
                            streamed_best_obj,
                        ),
                        pb_native_code_helper_applications: 0,
                        portfolio_timings: Some(portfolio_result.timings),
                    }));
                }
                return Ok(None);
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                let _ = worker.join();
                return Ok(None);
            }
        }
    }
}

fn best_known_legacy_solution(best_solution: &Mutex<Option<PbExactSolution>>) -> PbSolution {
    let best = best_known_or_unknown(best_solution).normalized_for_competition();
    PbSolution {
        status: best.status,
        assignment: best.assignment,
        objective: best.objective,
    }
}

#[allow(clippy::too_many_arguments)]
fn maybe_write_clique_conflict_row_import_map_sidecar<W: Write>(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    source_opb_text: Option<&str>,
    proof_path: &Path,
    timeout: Option<u64>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
) -> Result<()> {
    let Some(source_opb_text) = source_opb_text else {
        return Ok(());
    };

    let sidecar_path = clique_conflict_row_import_map_sidecar_path(proof_path);
    let mut buffer = Vec::new();
    let mut should_stop = || term_flag.load(Ordering::SeqCst) || timeout_expired(timeout, start);
    let Some(row_count) = write_max_clique_conflict_row_import_map_csv(
        instance,
        objective,
        source_opb_text,
        &mut buffer,
        &mut should_stop,
    )
    .with_context(|| {
        format!(
            "failed to build clique conflict row/import map '{}'",
            sidecar_path.display()
        )
    })?
    else {
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
        return Ok(());
    };

    let temp_sidecar_path = proof_temp_path(&sidecar_path);
    let result: Result<()> = (|| {
        {
            let sidecar_file = File::create(&temp_sidecar_path).with_context(|| {
                format!(
                    "failed to create clique conflict row/import map '{}'",
                    temp_sidecar_path.display()
                )
            })?;
            let mut writer = BufWriter::new(sidecar_file);
            writer.write_all(&buffer).with_context(|| {
                format!(
                    "failed to write clique conflict row/import map '{}'",
                    temp_sidecar_path.display()
                )
            })?;
            writer.flush().with_context(|| {
                format!(
                    "failed to flush clique conflict row/import map '{}'",
                    temp_sidecar_path.display()
                )
            })?;
        }
        fs::rename(&temp_sidecar_path, &sidecar_path).with_context(|| {
            format!(
                "failed to rename '{}' to '{}'",
                temp_sidecar_path.display(),
                sidecar_path.display()
            )
        })?;
        Ok(())
    })();

    if result.is_err() {
        let _ = fs::remove_file(&temp_sidecar_path);
        let _ = fs::remove_file(&sidecar_path);
    }
    result?;

    out.write_comment(&format!(
        "clique conflict row/import map sidecar: {} ({} rows)",
        sidecar_path.display(),
        row_count
    ))?;
    Ok(())
}

/// Solves a decision PB instance using the native PB CDCL solver (no CNF encoding).
fn solve_decision_native(
    instance: &PbInstance,
    timeout_dur: Option<std::time::Duration>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
    collect_native_helper_applications: bool,
) -> Result<PbSolveOutcome> {
    let mut solver = PbCdclSolver::new_interruptible(instance, || {
        if term_flag.load(Ordering::SeqCst) {
            return true;
        }
        if let Some(dur) = timeout_dur {
            if start.elapsed() >= dur {
                return true;
            }
        }
        false
    });
    solver.set_native_code_helper_validation_enabled(collect_native_helper_applications);

    let result = solver.solve_interruptible(|| {
        if term_flag.load(Ordering::SeqCst) {
            return true;
        }
        if let Some(dur) = timeout_dur {
            if start.elapsed() >= dur {
                return true;
            }
        }
        false
    });
    let helper_applications = solver.native_code_helper_applications();

    Ok(PbSolveOutcome {
        solution: pb_cdcl_result_to_solution(result, instance.num_vars),
        pb_native_code_helper_applications: helper_applications,
        portfolio_timings: None,
    })
}

/// Solves a decision PB instance with native CDCL proof logging.
fn solve_decision_with_proof(
    instance: &PbInstance,
    proof_path: &Path,
    timeout_dur: Option<std::time::Duration>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
    collect_native_helper_applications: bool,
) -> Result<PbSolveOutcome> {
    let temp_proof_path = prepare_proof_temp(proof_path)?;
    let result = (|| {
        let proof_file = File::create(&temp_proof_path)
            .with_context(|| format!("failed to create '{}'", temp_proof_path.display()))?;
        let should_stop = || {
            if term_flag.load(Ordering::SeqCst) {
                return true;
            }
            if let Some(dur) = timeout_dur {
                if start.elapsed() >= dur {
                    return true;
                }
            }
            false
        };
        // Proof-tap spec PHASE 4 default flip: the DENSE conflict path with
        // async micro-op capture is the DEFAULT for proof-on. The legacy
        // synchronous CpConstraint proof path is the escape hatch, selected by
        // AY_PB_PROOF_TAP=legacy (or =0); AY_PB_PROOF_TAP=1 and any other value
        // (including unset) stay on the tap. Fail-closed on both paths: any tap
        // failure surfaces via conclude_proof and no proof commits.
        let tap_enabled = std::env::var("AY_PB_PROOF_TAP").map_or(true, |v| {
            !matches!(v.trim().to_ascii_lowercase().as_str(), "legacy" | "0")
        });
        let mut solver = if tap_enabled {
            PbCdclSolver::with_proof_tap_interruptible(
                instance,
                BufWriter::with_capacity(1 << 20, proof_file),
                should_stop,
            )
        } else {
            PbCdclSolver::with_proof_writer_interruptible(
                instance,
                BufWriter::new(proof_file),
                should_stop,
            )
        }
        .map_err(|e| anyhow::anyhow!("failed to initialize proof writer: {e}"))?;
        solver.set_native_code_helper_validation_enabled(collect_native_helper_applications);

        let result = solver.solve_interruptible(|| {
            if term_flag.load(Ordering::SeqCst) {
                return true;
            }
            if let Some(dur) = timeout_dur {
                if start.elapsed() >= dur {
                    return true;
                }
            }
            false
        });
        let helper_applications = solver.native_code_helper_applications();
        let solution = pb_cdcl_result_to_solution(result, instance.num_vars);

        solver
            .conclude_proof()
            .map_err(|e| anyhow::anyhow!("proof error: {e}"))
            .with_context(|| format!("failed to finalize proof '{}'", proof_path.display()))?;

        commit_or_remove_proof(
            proof_path,
            &temp_proof_path,
            matches!(
                solution.status,
                PbStatus::Satisfiable | PbStatus::Unsatisfiable
            ),
        )?;

        Ok(PbSolveOutcome {
            solution,
            pb_native_code_helper_applications: helper_applications,
            portfolio_timings: None,
        })
    })();

    if result.is_err() {
        cleanup_proof_temp(proof_path, &temp_proof_path);
    }
    result
}

/// Strong certified-UNSAT route for the DEC-LIN-CERT track: solve the CNF
/// encoding with ay-sat (DRAT proof on) and lift its refutation into a VeriPB v3
/// proof of the original PB instance, written atomically to `proof_path`. Returns
/// `Some(UNSAT)` when a proof was produced, or `None` when it declines (SAT /
/// interrupted / encoding not aux-free-liftable) so the caller falls back to the
/// native proof path.
///
/// Soundness: the proof is produced ONLY when ay-sat proves the encoding UNSAT
/// (so the reported UNSAT is sound), and the competition's VeriPB checker is the
/// ultimate validator. A withheld or checker-rejected proof never changes the
/// reported SAT/UNSAT status — certification is strictly additive.
fn try_drat_lift_certified_unsat(
    instance: &PbInstance,
    proof_path: &Path,
    timeout_dur: Option<std::time::Duration>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
) -> Result<Option<PbSolveOutcome>> {
    let should_stop =
        || term_flag.load(Ordering::SeqCst) || timeout_dur.is_some_and(|d| start.elapsed() >= d);
    let Some(pbp) = ay_pb::proof::certify_decision_unsat_interruptible(instance, &should_stop)
    else {
        return Ok(None);
    };
    let temp_proof_path = prepare_proof_temp(proof_path)?;
    fs::write(&temp_proof_path, pbp.as_bytes())
        .with_context(|| format!("failed to write proof '{}'", temp_proof_path.display()))?;
    commit_or_remove_proof(proof_path, &temp_proof_path, true)?;
    Ok(Some(PbSolveOutcome::without_native_helpers(PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: Vec::new(),
        objective: None,
    })))
}

/// OPT-LIN-CERT fallback for the proof path: when native CDCL proof logging does
/// NOT reach `OptimumFound`, run the optimization PORTFOLIO to obtain the exact
/// optimum + a feasible incumbent achieving it, then assemble a VeriPB OPT proof
/// out-of-band via the certified OPT-LIN-CERT helpers (compact first, aux-free
/// second), write it atomically to `proof_path`, and report `OptimumFound`.
///
/// Returns `Some(OptimumFound outcome)` only when (a) the portfolio proves the
/// optimum, (b) the incumbent is complete + feasible + achieves it, and (c) one of
/// the cert helpers produces proof text. Otherwise returns `None` so the caller
/// keeps its existing fail-closed `unknown` behavior. The competition's VeriPB
/// checker is the ultimate validator; a withheld or checker-rejected proof never
/// changes the reported status (certification is strictly additive).
///
/// NOTE: the caller MUST have released the native CDCL proof-writer handle on
/// `temp_proof_path` before calling this (we overwrite that temp file).
fn try_opt_lin_cert_fallback(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    proof_path: &Path,
    temp_proof_path: &Path,
    timeout_dur: Option<std::time::Duration>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> Result<Option<PbSolveOutcome>> {
    // The OPT-LIN-CERT helpers only handle single-literal (linear) objective terms.
    if objective.terms.iter().any(|term| term.lits.len() != 1) {
        return Ok(None);
    }

    // Run the portfolio to (try to) prove the exact optimum + incumbent.
    let mut on_improve = |_obj_value: i128, _model: &[bool]| {};
    let portfolio_result = portfolio::solve_optimization_portfolio_with_timings(
        instance,
        objective,
        timeout_dur,
        start,
        term_flag,
        &mut on_improve,
    );
    let portfolio_solution = portfolio_result.solution;

    // We can only certify a proven optimum (BOUNDS V V). A merely feasible result is
    // not enough; decline so the caller stays fail-closed.
    if portfolio_solution.status != PbStatus::OptimumFound {
        return Ok(None);
    }
    let Some(optimum) = portfolio_solution.objective else {
        return Ok(None);
    };
    let incumbent = portfolio_solution.assignment.clone();
    if incumbent.len() != instance.num_vars as usize {
        return Ok(None);
    }

    let should_stop =
        || term_flag.load(Ordering::SeqCst) || timeout_dur.is_some_and(|d| start.elapsed() >= d);

    // Compact lower bound first (broad coverage: augmented refutations needing Sinz
    // aux registers); fall back to the aux-free lift. Both are re-checked by VeriPB.
    let pbp = ay_pb::proof::certify_opt_lin_bounds_compact_interruptible(
        instance,
        &incumbent,
        optimum,
        &should_stop,
    )
    .or_else(|| {
        ay_pb::proof::certify_opt_lin_bounds_interruptible(
            instance,
            &incumbent,
            optimum,
            &should_stop,
        )
    });
    let Some(pbp) = pbp else {
        return Ok(None);
    };

    fs::write(temp_proof_path, pbp.as_bytes())
        .with_context(|| format!("failed to write proof '{}'", temp_proof_path.display()))?;
    commit_or_remove_proof(proof_path, temp_proof_path, true)?;

    // Cache the exact incumbent so downstream reporting can surface it.
    let solution = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: incumbent,
        objective: Some(optimum),
    };
    cache_exact_solution(
        best_solution,
        exact_solution_from_result(&solution, objective),
    );

    Ok(Some(PbSolveOutcome {
        solution,
        pb_native_code_helper_applications: 0,
        portfolio_timings: Some(portfolio_result.timings),
    }))
}

/// Certify an ALREADY-PROVEN optimum out-of-band and commit its VeriPB proof.
///
/// Used when native CDCL proof logging reached `OptimumFound` but could not
/// close its lower bound with a structural cut (`opt_lower_bound_deferred`).
/// Unlike [`try_opt_lin_cert_fallback`] this does NOT re-run the portfolio — the
/// optimum and a feasible model achieving it are already in `solution` — so it
/// spends the remaining budget only on the certificate assembly itself
/// (compact Sinz lower bound first, then the aux-free lift). Both routes are
/// re-checked by the external VeriPB checker before any CERTIFIED claim.
///
/// Returns `Ok(true)` iff a proof was produced and atomically committed to
/// `proof_path`. `Ok(false)` (certificate withheld) leaves the caller
/// fail-closed: it discards the proof and reports the feasible incumbent rather
/// than an uncertified optimum.
fn commit_certified_known_optimum(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    solution: &PbSolution,
    proof_path: &Path,
    temp_proof_path: &Path,
    timeout_dur: Option<std::time::Duration>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
) -> Result<bool> {
    // The OPT-LIN-CERT helpers only handle single-literal (linear) objectives.
    if objective.terms.iter().any(|term| term.lits.len() != 1) {
        return Ok(false);
    }
    let Some(optimum) = solution.objective else {
        return Ok(false);
    };
    let incumbent = &solution.assignment;
    if incumbent.len() != instance.num_vars as usize {
        return Ok(false);
    }

    let should_stop =
        || term_flag.load(Ordering::SeqCst) || timeout_dur.is_some_and(|d| start.elapsed() >= d);

    // Compact (Sinz) lower bound first — broadest coverage — then the aux-free
    // lift. Each internally re-verifies the incumbent is feasible and achieves
    // `optimum`, and returns `None` (never a wrong proof) otherwise.
    let pbp = ay_pb::proof::certify_opt_lin_bounds_compact_interruptible(
        instance,
        incumbent,
        optimum,
        &should_stop,
    )
    .or_else(|| {
        ay_pb::proof::certify_opt_lin_bounds_interruptible(
            instance,
            incumbent,
            optimum,
            &should_stop,
        )
    });
    let Some(pbp) = pbp else {
        return Ok(false);
    };

    fs::write(temp_proof_path, pbp.as_bytes())
        .with_context(|| format!("failed to write proof '{}'", temp_proof_path.display()))?;
    commit_or_remove_proof(proof_path, temp_proof_path, true)?;
    Ok(true)
}

/// Solves a linear optimization PB instance with native CDCL proof logging.
fn solve_optimization_with_proof<W: Write>(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    proof_path: &Path,
    timeout_dur: Option<std::time::Duration>,
    start: std::time::Instant,
    term_flag: &AtomicBool,
    collect_native_helper_applications: bool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> Result<PbSolveOutcome> {
    let temp_proof_path = prepare_proof_temp(proof_path)?;
    let result = (|| {
        let proof_file = File::create(&temp_proof_path)
            .with_context(|| format!("failed to create '{}'", temp_proof_path.display()))?;
        let mut solver = PbCdclSolver::with_proof_writer_interruptible(
            instance,
            BufWriter::new(proof_file),
            || {
                if term_flag.load(Ordering::SeqCst) {
                    return true;
                }
                if let Some(dur) = timeout_dur {
                    if start.elapsed() >= dur {
                        return true;
                    }
                }
                false
            },
        )
        .map_err(|e| anyhow::anyhow!("failed to initialize proof writer: {e}"))?;
        solver.set_native_code_helper_validation_enabled(collect_native_helper_applications);

        // PROOF-TO-SCORE: stream every improving incumbent to STDOUT (never
        // into the VeriPB proof) and cache it, exactly like the plain
        // optimization path. Feasible answers are checkable from the v line
        // alone, so certified mode no longer forfeits them when the
        // optimality proof outlasts the budget. This path never sees WBO
        // (refused before dispatch), so the exact objective needs no
        // projection.
        let mut best_obj: Option<i128> = None;
        let mut streamed_best_obj: Option<i128> = None;
        let mut on_improve = |obj_value: i128, model: &[bool]| {
            let exact_solution = exact_incumbent_from_model(
                instance,
                objective,
                None,
                PbStatus::Satisfiable,
                obj_value,
                best_obj,
                model,
            );
            let Some(exact_obj_value) = exact_solution.objective else {
                return;
            };
            if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                return;
            }
            // The bar advances only from a VERIFIED construction (the helper
            // fails closed to `objective: None` on an infeasible model above).
            best_obj = Some(exact_obj_value);
            let _ = out.write_objective_exact(exact_obj_value);
            streamed_best_obj = Some(exact_obj_value);
            cache_exact_solution(best_solution, exact_solution);
        };
        let result = solver.solve_optimize_interruptible(objective, Some(&mut on_improve), || {
            if term_flag.load(Ordering::SeqCst) {
                return true;
            }
            if let Some(dur) = timeout_dur {
                if start.elapsed() >= dur {
                    return true;
                }
            }
            false
        });
        let helper_applications = solver.native_code_helper_applications();
        let solution = pb_cdcl_optimization_result_to_solution(result, instance.num_vars);
        if matches!(
            solution.status,
            PbStatus::OptimumFound | PbStatus::Satisfiable
        ) {
            cache_exact_solution(
                best_solution,
                exact_solution_from_result(&solution, objective),
            );
        }

        if !matches!(
            solution.status,
            PbStatus::Unsatisfiable | PbStatus::OptimumFound
        ) {
            // Native CDCL did not reach OptimumFound. Before falling back to the
            // certified OPT-LIN-CERT route, release the native proof-writer handle
            // on the temp file so the fallback can overwrite it (the native partial
            // proof is unusable — it has no conclusion).
            drop(solver);
            if let Some(outcome) = try_opt_lin_cert_fallback(
                instance,
                objective,
                proof_path,
                &temp_proof_path,
                timeout_dur,
                start,
                term_flag,
                best_solution,
            )? {
                return Ok(PbSolveOutcome {
                    pb_native_code_helper_applications: helper_applications,
                    solution: final_optimization_result_after_anytime_stream(
                        outcome.solution,
                        streamed_best_obj,
                    ),
                    ..outcome
                });
            }

            // No optimality/UNSAT proof: discard the (incomplete) proof file so
            // no certificate is claimed, but KEEP the cached feasible
            // incumbents — write_result_or_best_known re-verifies the best one
            // at the emission boundary and flushes it as s SATISFIABLE.
            // Previously the cache was cleared here, collapsing the certified
            // build to s UNKNOWN on every instance it could not prove within
            // the budget.
            cleanup_proof_temp(proof_path, &temp_proof_path);
            return Ok(PbSolveOutcome {
                solution: unknown_solution(),
                pb_native_code_helper_applications: helper_applications,
                portfolio_timings: None,
            });
        }

        // Native CDCL reached OptimumFound but could not close its optimality
        // proof's lower bound with a structural cut (opt_lower_bound_deferred):
        // the native proof file holds an unverifiable `rup >= 1 ;` and MUST NOT
        // be committed. The optimum itself is correct, so re-certify it
        // out-of-band from the KNOWN optimum (no portfolio re-solve) via the
        // OPT-LIN-CERT helpers, whose RUP steps VeriPB accepts.
        if solution.status == PbStatus::OptimumFound && solver.opt_lower_bound_deferred() {
            drop(solver);
            if commit_certified_known_optimum(
                instance,
                objective,
                &solution,
                proof_path,
                &temp_proof_path,
                timeout_dur,
                start,
                term_flag,
            )? {
                return Ok(PbSolveOutcome {
                    solution: final_optimization_result_after_anytime_stream(
                        solution,
                        streamed_best_obj,
                    ),
                    pb_native_code_helper_applications: helper_applications,
                    portfolio_timings: None,
                });
            }

            // Certification withheld (e.g. out of budget or a non-liftable
            // refutation): fail closed. Discard the proof and keep the cached
            // feasible incumbent — re-verified & flushed as s SATISFIABLE — never
            // an uncertified s OPTIMUM claim without a checkable proof.
            cleanup_proof_temp(proof_path, &temp_proof_path);
            return Ok(PbSolveOutcome {
                solution: unknown_solution(),
                pb_native_code_helper_applications: helper_applications,
                portfolio_timings: None,
            });
        }

        solver
            .conclude_proof()
            .map_err(|e| anyhow::anyhow!("proof error: {e}"))
            .with_context(|| format!("failed to finalize proof '{}'", proof_path.display()))?;

        commit_or_remove_proof(proof_path, &temp_proof_path, true)?;

        Ok(PbSolveOutcome {
            solution: final_optimization_result_after_anytime_stream(solution, streamed_best_obj),
            pb_native_code_helper_applications: helper_applications,
            portfolio_timings: None,
        })
    })();

    if result.is_err() {
        cleanup_proof_temp(proof_path, &temp_proof_path);
    }
    result
}

fn try_exact_decision_sat_incumbent_with_proof(
    _instance: &PbInstance,
    _proof_path: &Path,
    _timeout_dur: Option<std::time::Duration>,
    _start: std::time::Instant,
    _term_flag: &AtomicBool,
) -> Result<Option<PbSolveOutcome>> {
    // The instance-fingerprint decision-SAT incumbent recognizer was removed for
    // integrity; this path no longer short-circuits, so callers fall through to
    // the normal solver.
    Ok(None)
}

fn prepare_proof_temp(proof_path: &Path) -> Result<PathBuf> {
    clear_existing_proof(proof_path)?;
    let temp_proof_path = proof_temp_path(proof_path);
    let _ = fs::remove_file(&temp_proof_path);
    Ok(temp_proof_path)
}

fn clear_existing_clique_conflict_row_import_map_sidecar(proof_path: &Path) -> Result<()> {
    clear_existing_proof(&clique_conflict_row_import_map_sidecar_path(proof_path))
}

fn clear_existing_proof(proof_path: &Path) -> Result<()> {
    match fs::remove_file(proof_path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => {
            Err(error).with_context(|| format!("failed to remove '{}'", proof_path.display()))
        }
    }
}

fn commit_or_remove_proof(
    proof_path: &Path,
    temp_proof_path: &Path,
    proof_complete: bool,
) -> Result<()> {
    if proof_complete {
        fs::rename(temp_proof_path, proof_path).with_context(|| {
            format!(
                "failed to rename '{}' to '{}'",
                temp_proof_path.display(),
                proof_path.display()
            )
        })?;
    } else {
        cleanup_proof_temp(proof_path, temp_proof_path);
    }
    Ok(())
}

fn cleanup_proof_temp(proof_path: &Path, temp_proof_path: &Path) {
    let _ = fs::remove_file(temp_proof_path);
    let _ = fs::remove_file(proof_path);
    let _ = fs::remove_file(clique_conflict_row_import_map_sidecar_path(proof_path));
}

fn clique_conflict_row_import_map_sidecar_path(proof_path: &Path) -> PathBuf {
    let mut sidecar_path = proof_path.to_path_buf();
    let extension = proof_path
        .extension()
        .map(|extension| {
            format!(
                "{}.conflict-row-import-map.csv",
                extension.to_string_lossy()
            )
        })
        .unwrap_or_else(|| "conflict-row-import-map.csv".to_string());
    sidecar_path.set_extension(extension);
    sidecar_path
}

fn proof_temp_path(proof_path: &Path) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let mut temp_path = proof_path.to_path_buf();
    let temp_extension = proof_path
        .extension()
        .map(|extension| {
            format!(
                "{}.tmp-{}-{nonce}",
                extension.to_string_lossy(),
                std::process::id()
            )
        })
        .unwrap_or_else(|| format!("tmp-{}-{nonce}", std::process::id()));
    temp_path.set_extension(temp_extension);
    temp_path
}

fn pb_cdcl_result_to_solution(result: PbCdclResult, num_pb_vars: u32) -> PbSolution {
    match result {
        PbCdclResult::Satisfiable(model) => PbSolution {
            status: PbStatus::Satisfiable,
            assignment: (0..num_pb_vars as usize)
                .map(|i| model.get(i).copied().unwrap_or(false))
                .collect(),
            objective: None,
        },
        PbCdclResult::Unsatisfiable => PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: Vec::new(),
            objective: None,
        },
        _ => unknown_solution(),
    }
}

/// DECISION-SAT Verified-SAT-Gate (VSG) — the decision-track analogue of the
/// optimization incumbent VIG (`sanitize_optimization_incumbent`,
/// crates/ay-pb/src/portfolio.rs). The core CDCL solver's model reaches
/// `pb_cdcl_result_to_solution` and is mapped DIRECTLY to `PbStatus::Satisfiable`
/// with no re-check, so a would-be `s SATISFIABLE` verdict otherwise TRUSTS the
/// core solver's model. This gate re-verifies that model against the ORIGINAL
/// `instance.constraints` with the proven `ay_pb::verify_all_constraints` before
/// the verdict can be emitted.
///
/// SOUNDNESS / fail-closed: a `Satisfiable` model that does NOT satisfy every
/// constraint is downgraded to `Unknown` — NEVER a wrong `s SATISFIABLE`. This
/// makes decision-SAT 0-wrong BY CONSTRUCTION, independent of any core-solver
/// model bug.
///
/// 0-REGRESSION: a model that DOES verify is returned UNCHANGED (no feasible
/// model is ever turned into a false `Unknown`). Only the `Satisfiable` status is
/// gated; `Unsatisfiable` / `Unknown` / `Unsupported` are pass-through (a
/// refutation admits no model to re-verify, and downgrading them would be a
/// regression, not a soundness gain). `verify_all_constraints` is the same
/// cheap+proven oracle the incumbent VIG uses. Optimization SAT/incumbent
/// verdicts are already self-checked by that incumbent VIG, so the caller routes
/// only decision (`objective.is_none()`) instances here — no double-gate.
fn decision_sat_self_checked(solution: PbSolution, instance: &PbInstance) -> PbSolution {
    if solution.status == PbStatus::Satisfiable
        && !ay_pb::verify_all_constraints(&instance.constraints, &solution.assignment)
    {
        return unknown_solution();
    }
    solution
}

fn pb_cdcl_optimization_result_to_solution(result: PbCdclResult, num_pb_vars: u32) -> PbSolution {
    match result {
        PbCdclResult::Optimal(model, value) => {
            solved_model_to_solution(PbStatus::OptimumFound, model, Some(value), num_pb_vars)
        }
        PbCdclResult::Feasible(model, value) => {
            solved_model_to_solution(PbStatus::Satisfiable, model, Some(value), num_pb_vars)
        }
        other => pb_cdcl_result_to_solution(other, num_pb_vars),
    }
}

fn project_solution_assignment(mut solution: PbSolution, num_pb_vars: u32) -> PbSolution {
    let target_len = match usize::try_from(num_pb_vars) {
        Ok(value) => value,
        Err(_) => return solution,
    };
    if solution.assignment.len() > target_len {
        solution.assignment.truncate(target_len);
    }
    if solution.assignment.len() < target_len
        && matches!(
            solution.status,
            PbStatus::Satisfiable | PbStatus::OptimumFound
        )
    {
        return unknown_solution();
    }
    solution
}

fn solved_model_to_solution(
    status: PbStatus,
    model: Vec<bool>,
    objective: Option<i128>,
    num_pb_vars: u32,
) -> PbSolution {
    let Some(assignment) = projected_assignment_vec(&model, num_pb_vars) else {
        return unknown_solution();
    };
    PbSolution {
        status,
        assignment,
        objective,
    }
}

fn project_wbo_solution(mut solution: PbSolution, wbo: &WboInstance) -> PbSolution {
    solution = project_solution_assignment(solution, wbo.num_vars);
    if solution.status == PbStatus::Satisfiable || solution.status == PbStatus::OptimumFound {
        // WBO-VIG (single audited chokepoint, ay_pb::wbo_admissible_cost):
        // hard rows verified, true cost recomputed, strict cost<top enforced.
        // Fail closed to UNKNOWN when any of that cannot be certified.
        let Some(cost) = ay_pb::wbo_admissible_cost(wbo, &solution.assignment) else {
            return unknown_solution();
        };
        solution.objective = Some(cost);
    }
    solution
}

fn exact_wbo_solution_from_assignment(
    wbo: &WboInstance,
    status: PbStatus,
    assignment: &[bool],
    fallback_objective: Option<i128>,
) -> PbExactSolution {
    let Some(projected_assignment) = projected_assignment_vec(assignment, wbo.num_vars) else {
        return unknown_exact_solution();
    };
    let mut solution = PbExactSolution {
        status,
        assignment: projected_assignment,
        objective: fallback_objective,
    };
    if status == PbStatus::Satisfiable || status == PbStatus::OptimumFound {
        // WBO-VIG (same single chokepoint as `project_wbo_solution`): never
        // cache (or later flush) a model that is not a verified admissible
        // WBO model, and never report anything but its true cost.
        let Some(cost) = ay_pb::wbo_admissible_cost(wbo, &solution.assignment) else {
            return unknown_exact_solution();
        };
        solution.objective = Some(cost);
    }
    solution
}

/// Prefer the cached best true-cost WBO incumbent over the portfolio's final
/// model when the cached one is strictly cheaper. Both candidates are already
/// projected to the original WBO variable space and gated admissible (true
/// cost strictly below the top cost) by `exact_wbo_solution_from_assignment` /
/// `project_wbo_solution`.
fn prefer_cheaper_cached_wbo_incumbent(
    result: PbSolution,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> PbSolution {
    let cached = best_solution
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone();
    let Some(cached) = cached else {
        return result;
    };
    if cached.status != PbStatus::Satisfiable {
        return result;
    }
    let (Some(cached_cost), Some(result_cost)) = (cached.objective, result.objective) else {
        return result;
    };
    if cached_cost < result_cost {
        return PbSolution {
            status: PbStatus::Satisfiable,
            assignment: cached.assignment,
            objective: Some(cached_cost),
        };
    }
    result
}

fn exact_solution_from_result(
    solution: &PbSolution,
    objective: &ay_pb::PbObjective,
) -> PbExactSolution {
    let mut exact = solution.to_exact_solution();
    if exact.objective.is_some() {
        // FAIL-CLOSED recompute (design §3.2): on true i128 overflow the
        // objective is WITHHELD (`None` -> no `o` line for this result), never
        // replaced by the producer's legacy value.
        exact.objective = exact_objective_fail_closed(objective, &solution.assignment);
    }
    exact
}

/// `best_obj` is the caller's current strict-improvement bar (its running best
/// exact objective, `None` when no incumbent exists yet). On the non-WBO arm a
/// model whose exactly-recomputed objective does not strictly beat the bar is
/// dropped BEFORE the O(total-terms) `verify_all_constraints` scan — a
/// globally-dominated incumbent would be discarded by the caller's filter
/// anyway, so verifying it first is pure waste. This can only DISCARD
/// candidates, never admit one: the feasibility gate still runs on every model
/// that survives, and callers advance `best_obj` only from a VERIFIED
/// construction, so an infeasible model can never move the bar. The WBO arm is
/// deliberately untouched (its true cost is re-scored inside
/// `exact_wbo_solution_from_assignment`; the caller's own filter applies after).
fn exact_incumbent_from_model(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    wbo_projection: Option<&WboInstance>,
    status: PbStatus,
    obj_value: i128,
    best_obj: Option<i128>,
    model: &[bool],
) -> PbExactSolution {
    match wbo_projection {
        Some(wbo) => exact_wbo_solution_from_assignment(wbo, status, model, Some(obj_value)),
        None => match exact_objective_fail_closed(objective, model) {
            Some(exact_obj_value) => {
                // Dominance filter BEFORE verification (cheap exact recompute
                // first, full constraint scan only for strict improvements).
                // Callers already drop on `objective: None`.
                if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                    return unknown_exact_solution();
                }
                exact_optimization_incumbent(
                    &instance.constraints,
                    instance.num_vars,
                    status,
                    exact_obj_value,
                    model,
                )
            }
            // FAIL-CLOSED: the exact objective recompute overflowed i128 —
            // emit NO incumbent at all (callers skip on `objective: None`).
            None => unknown_exact_solution(),
        },
    }
}

/// FAIL-CLOSED exact objective recompute (design §3.2): the producer's claimed
/// value is always discarded and the objective is recomputed exactly in i128
/// from the model. Returns `None` on true i128 term-sum overflow, in which case
/// the caller must SKIP/withhold the objective (and any incumbent keyed on it)
/// rather than fall back to a legacy or saturated value.
fn exact_objective_fail_closed(objective: &ay_pb::PbObjective, model: &[bool]) -> Option<i128> {
    eval_objective_exact(objective, model).ok()
}

#[cfg(test)]
fn cache_optimization_incumbent(
    best_solution: &Mutex<Option<PbExactSolution>>,
    num_pb_vars: u32,
    obj_value: i64,
    model: &[bool],
) {
    cache_exact_optimization_incumbent(best_solution, num_pb_vars, i128::from(obj_value), model);
}

#[cfg(test)]
fn cache_exact_optimization_incumbent(
    best_solution: &Mutex<Option<PbExactSolution>>,
    num_pb_vars: u32,
    obj_value: i128,
    model: &[bool],
) {
    cache_exact_solution(
        best_solution,
        // Test helper: no constraints, so the feasibility gate is vacuous.
        exact_optimization_incumbent(&[], num_pb_vars, PbStatus::Satisfiable, obj_value, model),
    );
}

fn exact_optimization_incumbent(
    constraints: &[ay_pb::PbConstraint],
    num_pb_vars: u32,
    status: PbStatus,
    obj_value: i128,
    model: &[bool],
) -> PbExactSolution {
    let Some(assignment) = projected_assignment_vec(model, num_pb_vars) else {
        return unknown_exact_solution();
    };
    // Verified Incumbent Gate at the binary entry point (design §3.2): re-check
    // feasibility against the ORIGINAL constraints. An infeasible model yields
    // NO incumbent (fail-closed to UNKNOWN), never a stored objective/witness.
    if !ay_pb::verify_all_constraints(constraints, &assignment) {
        return unknown_exact_solution();
    }
    PbExactSolution {
        status,
        assignment,
        objective: Some(obj_value),
    }
}

fn projected_assignment_vec(model: &[bool], num_pb_vars: u32) -> Option<Vec<bool>> {
    usize::try_from(num_pb_vars)
        .ok()
        .and_then(|num_pb_vars| model.get(..num_pb_vars))
        .map(<[bool]>::to_vec)
}

fn cache_exact_solution(best_solution: &Mutex<Option<PbExactSolution>>, solution: PbExactSolution) {
    let mut guard = best_solution
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *guard = Some(solution);
}

fn write_result_or_best_known<W: Write>(
    out: &mut PbOutputWriter<W>,
    result: &PbSolution,
    termination_requested: bool,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> io::Result<PbStatus> {
    // A late SIGTERM after solving should not override a completed result.
    let emitted = select_result_or_best_known(result, termination_requested, best_solution);
    let status = emitted.status;
    out.write_full_result_exact(&emitted)?;
    Ok(status)
}

fn select_result_or_best_known(
    result: &PbSolution,
    termination_requested: bool,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> PbExactSolution {
    let selected = if termination_requested && result.status == PbStatus::Unknown {
        let mut best_known = best_known_or_unknown(best_solution);
        best_known.objective = None;
        best_known
    } else {
        result.to_exact_solution()
    };

    selected.normalized_for_competition()
}

fn final_optimization_result_after_anytime_stream(
    mut result: PbSolution,
    streamed_best_obj: Option<i128>,
) -> PbSolution {
    if result
        .objective
        .is_some_and(|value| Some(value) == streamed_best_obj)
    {
        result.objective = None;
    }
    result
}

fn write_best_known_result<W: Write>(
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> io::Result<()> {
    out.write_full_result_exact(&best_known_or_unknown(best_solution))
}

fn best_known_or_unknown(best_solution: &Mutex<Option<PbExactSolution>>) -> PbExactSolution {
    match best_solution.lock() {
        Ok(guard) => guard.clone(),
        Err(poisoned) => poisoned.into_inner().clone(),
    }
    .unwrap_or_else(unknown_exact_solution)
}

fn unknown_exact_solution() -> PbExactSolution {
    PbExactSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: None,
    }
}

fn unknown_solution() -> PbSolution {
    PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: None,
    }
}

fn unsupported_solution() -> PbSolution {
    PbSolution {
        status: PbStatus::Unsupported,
        assignment: Vec::new(),
        objective: None,
    }
}

/// EARLY, self-checked structural-UNSAT pass over the ORIGINAL constraint rows.
///
/// Each recognizer is from the kernel-algebra-verified `ay_pb` library and emits
/// `true` EXCLUSIVELY via its own self-check: it reconstructs an explicit
/// cutting-planes / GF(2) refutation and replays it to `0 >= 1` against the
/// verified algebra before returning `true`. Therefore a feasible (SAT) instance
/// can NEVER make this return `true` — it can never flip SAT to UNSAT.
///
/// ZERO-REGRESSION: each recognizer is O(n+m), size-capped and fail-closed
/// (declines fast on non-matching shapes), so the whole pass is only a few hundred
/// milliseconds even on the largest decision instances — which is what makes it
/// safe to run EARLY, before the full-timeout native decision solve. Ordering is
/// decline-cost-first (the two near-constant-time scans run before the linear-scan
/// recognizers) and short-circuits on the first self-check.
///
/// Row-count ceiling mirroring the competition binary's gate: above it the
/// recognizers' own success caps (matching-cardinality 2M modeled rows is the
/// largest; pigeonhole / parity-recovery 200K, plain GF(2) 4096 equality rows)
/// mean the pass cannot certify, while the full-row scans cost ~0.1-0.2s per
/// pass on a 6.4M-row instance (measured, lopes-172). Skipping is always sound:
/// the recognizers are fail-closed advisors, so a decline just means "search".
const STRUCTURAL_PRECHECK_MAX_ROWS: usize = 2_000_000;

fn structural_unsat_self_checked(instance: &PbInstance) -> bool {
    structural_unsat_self_checked_with_cap(instance, STRUCTURAL_PRECHECK_MAX_ROWS)
}

/// Cap-parameterized core of [`structural_unsat_self_checked`] (unit-testable
/// without materializing a multi-million-row instance).
fn structural_unsat_self_checked_with_cap(instance: &PbInstance, max_rows: usize) -> bool {
    // GF(2) parity self-caps on EQUALITY rows (4096) and vars (65536); non-Eq
    // rows cost one relation compare each (~8ms at 6.4M rows, measured), so it
    // is cheap at any total row count and CAN certify far above the row gate
    // (a small parity core padded with millions of inequality rows). Run it
    // ungated so that class keeps its instant kernel-checked refutation
    // (mirrors the competition binary).
    if gf2_parity_unsat_cp_checked(&instance.constraints, instance.num_vars) {
        return true;
    }
    if instance.constraints.len() > max_rows {
        // Size gate for the remaining passes — a deliberate cost/coverage
        // trade, always fail-closed to "go search": matching_cardinality
        // declines internally above this by construction; pigeonhole and
        // recovery-parity could in principle certify above it (their caps
        // count only the modeled-row subset) but their per-row normalization
        // is the expensive scan the gate exists to avoid.
        return false;
    }
    matching_cardinality_unsat_cp_checked(&instance.constraints)
        || pigeonhole_unsat_cp_checked(&instance.constraints)
        || gf2_parity_detects_unsat_with_recovery(&instance.constraints, instance.num_vars)
}

/// The verdict returned when a structural recognizer self-checks: `s UNSATISFIABLE`
/// with an empty model (a refutation admits no satisfying assignment).
fn structural_unsat_outcome() -> PbSolveOutcome {
    PbSolveOutcome::without_native_helpers(PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: Vec::new(),
        objective: None,
    })
}

fn dobutsu_no_cert_parsed_optimization_label(_instance: &PbInstance) -> Option<&'static str> {
    // The Dobutsu-Shogi instance-fingerprint recognizers were removed for
    // integrity; no instance is special-cased.
    None
}

fn timeout_expired(timeout: Option<u64>, start: std::time::Instant) -> bool {
    timeout.is_some_and(|ms| start.elapsed().as_millis() >= u128::from(ms))
}

fn periodic_stop_check(
    term_flag: &AtomicBool,
    timeout: Option<u64>,
    start: std::time::Instant,
    poll_interval: usize,
) -> impl FnMut() -> bool + '_ {
    let poll_interval = poll_interval.max(1);
    let mut poll_budget = 0usize;
    move || {
        if poll_budget > 0 {
            poll_budget -= 1;
            return false;
        }
        poll_budget = poll_interval - 1;
        term_flag.load(Ordering::SeqCst) || timeout_expired(timeout, start)
    }
}

fn read_file_interruptible<F>(path: &Path, should_stop: &mut F) -> io::Result<Option<Vec<u8>>>
where
    F: FnMut() -> bool,
{
    let file = File::open(path)?;
    let capacity_hint = file
        .metadata()
        .ok()
        .and_then(|metadata| usize::try_from(metadata.len()).ok())
        .unwrap_or(0);
    read_reader_interruptible(file, capacity_hint, should_stop)
}

fn read_reader_interruptible<R, F>(
    mut reader: R,
    capacity_hint: usize,
    should_stop: &mut F,
) -> io::Result<Option<Vec<u8>>>
where
    R: Read,
    F: FnMut() -> bool,
{
    const READ_CHUNK_SIZE: usize = 64 * 1024;

    let mut bytes = Vec::with_capacity(capacity_hint);
    let mut chunk = vec![0_u8; READ_CHUNK_SIZE];
    loop {
        if should_stop() {
            return Ok(None);
        }
        let read = reader.read(&mut chunk)?;
        if read == 0 {
            break;
        }
        bytes.extend_from_slice(&chunk[..read]);
    }
    if should_stop() {
        return Ok(None);
    }
    Ok(Some(bytes))
}

fn write_stats<W: Write>(
    out: &mut PbOutputWriter<W>,
    file: &Path,
    instance: &ParsedPbInstance,
    timeout: Option<u64>,
    telemetry: &PbJitCandidateTelemetry,
) -> io::Result<()> {
    out.write_comment(&format!("input: {}", file.display()))?;
    out.write_comment(&format!("format: {}", instance.format_name()))?;
    out.write_comment(&format!("variables: {}", instance.num_vars()))?;
    out.write_comment(&format!("constraints: {}", instance.constraint_count()))?;
    out.write_comment(&format!(
        "problem: {}",
        if instance.is_optimization() {
            "optimization"
        } else {
            "decision"
        }
    ))?;
    if let Some(ms) = timeout {
        out.write_comment(&format!("timeout-ms: {ms}"))?;
    }
    write_jit_candidate_telemetry(out, telemetry)?;
    Ok(())
}

fn jit_candidate_telemetry(
    instance: &ParsedPbInstance,
    timeout_ms: Option<u64>,
) -> PbJitCandidateTelemetry {
    if should_skip_startup_jit_telemetry(instance, timeout_ms) {
        return skipped_jit_candidate_telemetry();
    }

    match instance {
        ParsedPbInstance::Opb(pb) => profile_jit_candidate_telemetry(pb),
        ParsedPbInstance::Wbo(wbo) => match try_wbo_to_pbo(wbo) {
            Ok(pbo) => profile_jit_candidate_telemetry(&pbo),
            Err(_) => skipped_jit_candidate_telemetry(),
        },
    }
}

fn should_skip_startup_jit_telemetry(instance: &ParsedPbInstance, timeout_ms: Option<u64>) -> bool {
    should_skip_startup_jit_telemetry_for_counts(
        timeout_ms,
        instance.is_optimization(),
        instance.num_vars(),
        instance.constraint_count(),
    )
}

fn should_skip_startup_jit_telemetry_for_counts(
    timeout_ms: Option<u64>,
    is_optimization: bool,
    num_vars: u32,
    constraint_count: usize,
) -> bool {
    timeout_ms.is_some_and(|ms| ms <= HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS)
        && is_optimization
        && num_vars >= HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS
        && constraint_count >= HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS
}

fn skipped_jit_candidate_telemetry() -> PbJitCandidateTelemetry {
    PbJitCandidateTelemetry {
        profile_attempts: 0,
        profiled_candidates: 0,
        selected_candidates: 0,
        rejected_candidates: 0,
        rejection_reason: None,
        kernel_kind: None,
        kernel_terms: 0,
        kernel_repetitions: 0,
        objective_profile: None,
        pb_pbo_candidate_applications: 0,
        pb_native_code_helper_applications: 0,
    }
}

fn write_jit_candidate_telemetry<W: Write>(
    out: &mut PbOutputWriter<W>,
    telemetry: &PbJitCandidateTelemetry,
) -> io::Result<()> {
    let objective = telemetry.objective_profile;
    out.write_comment(&format!(
        "pb_jit_profile_attempts: {}",
        telemetry.profile_attempts
    ))?;
    out.write_comment(&format!(
        "pb_jit_profiled_candidates: {}",
        telemetry.profiled_candidates
    ))?;
    out.write_comment(&format!(
        "pb_jit_selected_candidates: {}",
        telemetry.selected_candidates
    ))?;
    out.write_comment(&format!(
        "pb_jit_rejected_candidates: {}",
        telemetry.rejected_candidates
    ))?;
    out.write_comment(&format!(
        "pb_jit_rejection_reason: {}",
        telemetry
            .rejection_reason
            .map_or("none", ay_pb::PbJitRejection::as_str)
    ))?;
    out.write_comment(&format!(
        "pb_jit_kernel_kind: {}",
        telemetry
            .kernel_kind
            .map_or("none", ay_pb::PbKernelKind::as_str)
    ))?;
    out.write_comment(&format!("pb_jit_kernel_terms: {}", telemetry.kernel_terms))?;
    out.write_comment(&format!(
        "pb_jit_kernel_repetitions: {}",
        telemetry.kernel_repetitions
    ))?;
    out.write_comment(&format!(
        "pb_jit_objective_profiled: {}",
        if objective.is_some() { 1 } else { 0 }
    ))?;
    out.write_comment(&format!(
        "pb_jit_objective_terms: {}",
        objective.map_or(0, |profile| profile.terms)
    ))?;
    out.write_comment(&format!(
        "pb_jit_objective_single_lit_terms: {}",
        objective.map_or(0, |profile| profile.single_lit_terms)
    ))?;
    out.write_comment(&format!(
        "pb_jit_objective_unit_weight_terms: {}",
        objective.map_or(0, |profile| profile.unit_weight_terms)
    ))?;
    out.write_comment(&format!(
        "pb_jit_objective_max_abs_coeff: {}",
        objective.map_or(0, |profile| profile.max_abs_coeff)
    ))?;
    out.write_comment(&format!(
        "pb_jit_objective_total_abs_weight: {}",
        objective.map_or(0, |profile| profile.total_abs_weight)
    ))?;
    out.write_comment(&format!(
        "pb_pbo_candidate_applications: {}",
        telemetry.pb_pbo_candidate_applications
    ))?;
    out.write_comment(&format!(
        "pb_native_code_helper_applications: {}",
        telemetry.pb_native_code_helper_applications
    ))?;
    Ok(())
}

fn write_portfolio_timing_stats<W: Write>(
    out: &mut PbOutputWriter<W>,
    timings: &portfolio::PbPortfolioPhaseTimings,
) -> io::Result<()> {
    for (key, value) in timings.stats_fields() {
        out.write_comment(&format!("{key}: {value}"))?;
    }
    Ok(())
}

const PB_PBO_CANDIDATE_ARTIFACT: &str = "pb-pbo-candidates";
const PB_NATIVE_HELPER_ARTIFACT: &str = "pb-native-code-helpers";
const PB_PBO_CANDIDATE_APPLICATION_COUNTER: &str = "pb_pbo_candidate_applications";
const PB_NATIVE_HELPER_APPLICATION_COUNTER: &str = "pb_native_code_helper_applications";
const PB_NATIVE_HELPER_CURRENT_DISPATCH_ENABLED: bool = false;

#[derive(Debug, Clone, PartialEq, Eq)]
struct PbCompetitionJitMetadata {
    artifact: &'static str,
    application_counter: &'static str,
    requested_mode: String,
    candidate_mode: &'static str,
    native_dispatch: bool,
    fail_closed: bool,
}

fn trimmed_env_value(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}

fn pb_competition_jit_metadata(
    pb_pbo_candidate_applications: u64,
    pb_native_code_helper_applications: u64,
) -> PbCompetitionJitMetadata {
    let requested = trimmed_env_value("AY_COMPETITION_JIT_MODE");
    pb_competition_jit_metadata_for_requested(
        requested.as_deref(),
        pb_pbo_candidate_applications,
        pb_native_code_helper_applications,
    )
}

fn pb_competition_jit_metadata_for_requested(
    requested: Option<&str>,
    pb_pbo_candidate_applications: u64,
    pb_native_code_helper_applications: u64,
) -> PbCompetitionJitMetadata {
    let native_helper_available = pb_native_code_helper_applications > 0;
    let native_helper_current_dispatch_available =
        native_helper_available && PB_NATIVE_HELPER_CURRENT_DISPATCH_ENABLED;
    let pbo_candidate_available = pb_pbo_candidate_applications > 0;
    let default_to_pbo_candidate = pbo_candidate_available || !native_helper_available;
    let default_artifact = if default_to_pbo_candidate {
        PB_PBO_CANDIDATE_ARTIFACT
    } else {
        PB_NATIVE_HELPER_ARTIFACT
    };
    let default_application_counter = if default_to_pbo_candidate {
        PB_PBO_CANDIDATE_APPLICATION_COUNTER
    } else {
        PB_NATIVE_HELPER_APPLICATION_COUNTER
    };
    let default_application_count = if default_to_pbo_candidate {
        pb_pbo_candidate_applications
    } else {
        pb_native_code_helper_applications
    };

    match requested {
        Some(value) if value.eq_ignore_ascii_case("off") => PbCompetitionJitMetadata {
            artifact: default_artifact,
            application_counter: default_application_counter,
            requested_mode: value.to_string(),
            candidate_mode: "off",
            native_dispatch: false,
            fail_closed: false,
        },
        Some(value)
            if value.eq_ignore_ascii_case("current")
                && native_helper_current_dispatch_available =>
        {
            PbCompetitionJitMetadata {
                artifact: PB_NATIVE_HELPER_ARTIFACT,
                application_counter: PB_NATIVE_HELPER_APPLICATION_COUNTER,
                requested_mode: value.to_string(),
                candidate_mode: "current",
                native_dispatch: true,
                fail_closed: false,
            }
        }
        Some(value) if value.eq_ignore_ascii_case("current") => PbCompetitionJitMetadata {
            artifact: if native_helper_available {
                PB_NATIVE_HELPER_ARTIFACT
            } else {
                default_artifact
            },
            application_counter: if native_helper_available {
                PB_NATIVE_HELPER_APPLICATION_COUNTER
            } else {
                default_application_counter
            },
            requested_mode: value.to_string(),
            candidate_mode: "off",
            native_dispatch: false,
            fail_closed: true,
        },
        Some(value) if value.eq_ignore_ascii_case("solver-program") && pbo_candidate_available => {
            PbCompetitionJitMetadata {
                artifact: PB_PBO_CANDIDATE_ARTIFACT,
                application_counter: PB_PBO_CANDIDATE_APPLICATION_COUNTER,
                requested_mode: value.to_string(),
                candidate_mode: "solver-program",
                native_dispatch: false,
                fail_closed: false,
            }
        }
        Some(value) if value.eq_ignore_ascii_case("solver-program") => PbCompetitionJitMetadata {
            artifact: PB_PBO_CANDIDATE_ARTIFACT,
            application_counter: PB_PBO_CANDIDATE_APPLICATION_COUNTER,
            requested_mode: value.to_string(),
            candidate_mode: "off",
            native_dispatch: false,
            fail_closed: true,
        },
        Some(value) if value.eq_ignore_ascii_case("profile-only") => PbCompetitionJitMetadata {
            artifact: default_artifact,
            application_counter: default_application_counter,
            requested_mode: value.to_string(),
            candidate_mode: "profile-only",
            native_dispatch: false,
            fail_closed: default_application_count == 0,
        },
        Some(value) => PbCompetitionJitMetadata {
            artifact: default_artifact,
            application_counter: default_application_counter,
            requested_mode: value.to_string(),
            candidate_mode: "off",
            native_dispatch: false,
            fail_closed: true,
        },
        None => PbCompetitionJitMetadata {
            artifact: default_artifact,
            application_counter: default_application_counter,
            requested_mode: "profile-only".to_string(),
            candidate_mode: "profile-only",
            native_dispatch: false,
            fail_closed: default_application_count == 0,
        },
    }
}

impl PbCompetitionJitMetadata {
    fn json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema_version": 1,
            "track": "pb",
            "artifact": self.artifact,
            "application_counter": self.application_counter,
            "requested_mode": self.requested_mode.as_str(),
            "candidate_mode": self.candidate_mode,
            "native_dispatch": self.native_dispatch,
            "fail_closed": self.fail_closed,
        })
    }
}

fn pb_run_stats_json(
    run_stats: &RunStatistics,
    pb_pbo_candidate_applications: u64,
    pb_native_code_helper_applications: u64,
) -> String {
    let json = run_stats.to_json();
    let Ok(mut value) = serde_json::from_str::<serde_json::Value>(&json) else {
        return json;
    };
    let Some(map) = value.as_object_mut() else {
        return json;
    };

    map.insert(
        "competition_jit".to_string(),
        pb_competition_jit_metadata(
            pb_pbo_candidate_applications,
            pb_native_code_helper_applications,
        )
        .json_value(),
    );
    value.to_string()
}

fn emit_pb_json_stats(
    stats_json: bool,
    solve_start: std::time::Instant,
    status: PbStatus,
    telemetry: Option<&PbJitCandidateTelemetry>,
    portfolio_timings: Option<&portfolio::PbPortfolioPhaseTimings>,
) {
    if !stats_json {
        return;
    }

    let mut run_stats = RunStatistics::new(
        SolveMode::Pb,
        pb_status_stats_result(status),
        solve_start.elapsed(),
    );
    let pb_pbo_candidate_applications =
        telemetry.map_or(0, |telemetry| telemetry.pb_pbo_candidate_applications);
    run_stats.insert(
        PB_PBO_CANDIDATE_APPLICATION_COUNTER,
        pb_pbo_candidate_applications,
    );
    let pb_native_code_helper_applications =
        telemetry.map_or(0, |telemetry| telemetry.pb_native_code_helper_applications);
    run_stats.insert(
        PB_NATIVE_HELPER_APPLICATION_COUNTER,
        pb_native_code_helper_applications,
    );
    if let Some(timings) = portfolio_timings {
        for (key, value) in timings.stats_fields() {
            run_stats.insert(key, value);
        }
    }
    safe_eprintln!(
        "{}",
        pb_run_stats_json(
            &run_stats,
            pb_pbo_candidate_applications,
            pb_native_code_helper_applications,
        )
    );
}

fn pb_status_stats_result(status: PbStatus) -> &'static str {
    match status {
        PbStatus::Satisfiable => "sat",
        PbStatus::Unsatisfiable => "unsat",
        PbStatus::OptimumFound => "optimum_found",
        PbStatus::Unknown => "unknown",
        PbStatus::Unsupported => "unsupported",
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PbInputFormat {
    Opb,
    Wbo,
}

fn detect_pb_format(path: &Path, input: &str) -> PbInputFormat {
    match path.extension().and_then(|ext| ext.to_str()) {
        Some(ext) if ext.eq_ignore_ascii_case("wbo") => PbInputFormat::Wbo,
        Some(ext) if ext.eq_ignore_ascii_case("opb") => PbInputFormat::Opb,
        _ if looks_like_wbo(input) => PbInputFormat::Wbo,
        _ => PbInputFormat::Opb,
    }
}

fn looks_like_wbo(input: &str) -> bool {
    input
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty() && !line.starts_with('*'))
        .is_some_and(|line| line.starts_with("soft:"))
}

fn parse_instance_interruptible<F>(
    format: PbInputFormat,
    input: &str,
    should_stop: F,
) -> std::result::Result<ParsedPbInstance, ay_pb::ParseError>
where
    F: FnMut() -> bool,
{
    match format {
        PbInputFormat::Opb => parse_opb_interruptible(input, should_stop)
            .map(|instance| ParsedPbInstance::Opb(Arc::new(instance))),
        PbInputFormat::Wbo => {
            parse_wbo_interruptible(input, should_stop).map(ParsedPbInstance::Wbo)
        }
    }
}

#[derive(Debug, Clone)]
enum ParsedPbInstance {
    /// OPB instances are held behind an `Arc` so the decision frontend-timeout
    /// watchdog can hand its detached worker thread shared ownership of the
    /// rows instead of deep-copying them (a few tenths of a second at 6.4M
    /// rows; ~0.3s measured for the same-shape row copy on lopes-172). The
    /// rows are immutable after parse (every solve path takes `&PbInstance`),
    /// so sharing cannot change any verdict.
    Opb(Arc<PbInstance>),
    Wbo(WboInstance),
}

impl ParsedPbInstance {
    fn format_name(&self) -> &'static str {
        match self {
            Self::Opb(_) => "OPB",
            Self::Wbo(_) => "WBO",
        }
    }

    fn num_vars(&self) -> u32 {
        match self {
            Self::Opb(instance) => instance.num_vars,
            Self::Wbo(instance) => instance.num_vars,
        }
    }

    fn constraint_count(&self) -> usize {
        match self {
            Self::Opb(instance) => instance.constraints.len(),
            Self::Wbo(instance) => {
                instance.hard_constraints.len() + instance.soft_constraints.len()
            }
        }
    }

    fn is_optimization(&self) -> bool {
        match self {
            Self::Opb(instance) => instance.objective.is_some(),
            Self::Wbo(_) => true,
        }
    }
}

#[cfg(unix)]
struct SigtermMonitor {
    flag: Arc<AtomicBool>,
    sig_id: signal_hook::SigId,
}

#[cfg(unix)]
impl SigtermMonitor {
    fn install() -> Result<Self> {
        let flag = Arc::new(AtomicBool::new(false));
        let sig_id = signal_hook::flag::register(signal_hook::consts::SIGTERM, Arc::clone(&flag))
            .context("failed to register SIGTERM flag")?;

        Ok(Self { flag, sig_id })
    }

    fn flag(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.flag)
    }
}

#[cfg(unix)]
impl Drop for SigtermMonitor {
    fn drop(&mut self) {
        let _ = signal_hook::low_level::unregister(self.sig_id);
    }
}

#[cfg(not(unix))]
struct SigtermMonitor {
    flag: Arc<AtomicBool>,
}

#[cfg(not(unix))]
impl SigtermMonitor {
    fn install() -> Result<Self> {
        Ok(Self {
            flag: Arc::new(AtomicBool::new(false)),
        })
    }

    fn flag(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.flag)
    }
}

#[cfg(test)]
mod tests;
