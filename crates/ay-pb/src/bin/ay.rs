// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::cell::Cell;
use std::fs::{self, File};
use std::io::{self, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use ay_pb::{
    break_symmetries, break_symmetries_with_deadline, clique_arm_matches, eval_objective_exact,
    gf2_parity_detects_unsat_with_recovery, gf2_parity_unsat_cp_checked, install_sigterm_flag,
    is_highly_symmetric_candidate, is_linear, linearize, matching_cardinality_unsat_cp_checked,
    parse_opb_interruptible, parse_wbo_interruptible, pigeonhole_unsat_cp_checked, portfolio,
    profile_jit_candidate_telemetry, try_clique_witness, try_wbo_to_pbo,
    write_max_clique_conflict_row_import_map_csv, PbCdclResult, PbCdclSolver, PbExactSolution,
    PbInstance, PbJitCandidateTelemetry, PbOutputWriter, PbSolution, PbStatus, WboInstance,
};

const HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS: u64 = 5_000;
const HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS: u32 = 900_000;
const HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS: usize = 1_000_000;
const PARSE_STOP_POLL_INTERVAL: usize = 4096;
const NONLINEAR_OPT_FRONTEND_TIMEOUT_RESERVE_MS: u64 = 600;

// Certified-optimization budget split (see `solve_optimization_with_proof`):
// the native proof-logging CDCL gets an initial slice of the remaining budget
// R, extendable on verified incumbent improvements up to a hard ceiling; the
// rest goes to the portfolio + out-of-band certification fallback, with a
// reserve kept for the certification re-solve. Warmup data: the portfolio
// proves ~24/199 OPT-LIN optima at full budget vs ~1/199 for native proof
// logging, and native conclusions land early or never — hence the small slice.
// Values mirror the HUGE_OPT_STATS_TELEMETRY_SKIP_* magnitudes but stay
// decoupled (proof-logging I/O dominates on huge instances).
const OPT_CERT_NATIVE_SLICE_DIV: u32 = 6;
const OPT_CERT_NATIVE_SLICE_DIV_HUGE: u32 = 12;
const OPT_CERT_NATIVE_CEIL_DIV: u32 = 3;
const OPT_CERT_NATIVE_CEIL_DIV_HUGE: u32 = 6;
const OPT_CERT_IMPROVE_GRACE_DIV: u32 = 12;
const OPT_CERT_IMPROVE_GRACE_MAX_MS: u64 = 30_000;
const OPT_CERT_CERTIFY_RESERVE_DIV: u32 = 8;
const OPT_CERT_CERTIFY_RESERVE_MIN_MS: u64 = 10_000;
const OPT_CERT_CERTIFY_RESERVE_MAX_MS: u64 = 300_000;
const OPT_CERT_NATIVE_TAIL_MIN_MS: u64 = 2_000;
const OPT_CERT_HUGE_MIN_VARS: u32 = 900_000;
const OPT_CERT_HUGE_MIN_CONSTRAINTS: usize = 1_000_000;

// MEMLIMIT enforcement allocator. `apply_memory_limit` sets the process memory
// budget from the competition `MEMLIMIT`, and the solver consults
// `ay_sys::process_memory_exceeded()` at its cancellation checkpoints to bail
// cleanly (returning UNKNOWN / the best incumbent) before the OS OOM-kills the
// process. That guard has two signals: instantaneous live-heap bytes (this
// allocator) and lagging peak RSS (`getrusage`). Without a `CountingAllocator`
// installed the live-bytes signal stays 0, so the guard relies solely on the
// lagging RSS reading — which a fast allocation burst (e.g. a dense PB row whose
// BDD/counter CNF encoding materializes hundreds of millions of clauses) can
// overshoot by gigabytes before the next checkpoint observes it. Wrapping the
// system allocator makes the live-bytes signal exact and instantaneous, with no
// extra dependency. Soundness-neutral: it only observes bytes and drives
// UNKNOWN, never a wrong SAT/UNSAT.
#[global_allocator]
static GLOBAL: ay_sys::CountingAllocator<std::alloc::System> =
    ay_sys::CountingAllocator::new(std::alloc::System);

/// Process-global "emergency incumbent", read ONLY by the `main` panic handler.
///
/// PROOF-TO-SCORE: if the solve thread unwinds (an internal panic, or an
/// allocation-adjacent failure that surfaces as a panic) AFTER a feasible model
/// has been found, the previous handler discarded everything and printed
/// `s UNKNOWN`, throwing away a perfectly good sound-correct answer. We instead
/// keep the best streamed incumbent here, along with the ORIGINAL constraints, so
/// the handler can re-run the Verified Incumbent Gate (VIG) and flush the model
/// as `SATISFIABLE`. The boundary VIG means a stored model is emitted only if it
/// still satisfies every constraint, so this NEVER prints a wrong answer and
/// NEVER claims OPTIMUM. Armed only for OPB (where the incumbent assignment lives
/// in the original variable space); left disarmed for WBO, preserving the
/// fail-closed `s UNKNOWN` there.
struct EmergencyIncumbent {
    /// The parsed instance, shared by refcount. The store must own the rows
    /// (the solve stack that parsed them unwinds before the panic handler
    /// runs), but an `Arc` clone provides exactly that ownership WITHOUT the
    /// full-row copy the previous `constraints.to_vec()` paid — ~0.3s of
    /// pre-search time on a 6.4M-row instance. The rows are immutable after
    /// parse (every solve path takes `&PbInstance`), so the shared view the
    /// handler re-checks against is byte-identical to the original.
    instance: Arc<ParsedPbInstance>,
    assignment: Option<Vec<bool>>,
}

impl EmergencyIncumbent {
    /// The ORIGINAL constraints for the VIG re-check (`None` only if a WBO
    /// instance were ever armed, which `run_solve` never does; fail-closed to
    /// UNKNOWN in that case).
    fn vig_constraints(&self) -> Option<&[ay_pb::PbConstraint]> {
        self.instance.vig_constraints()
    }
}

static EMERGENCY_INCUMBENT: Mutex<Option<EmergencyIncumbent>> = Mutex::new(None);

fn lock_emergency_incumbent() -> std::sync::MutexGuard<'static, Option<EmergencyIncumbent>> {
    EMERGENCY_INCUMBENT
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Arm the emergency-flush store for an OPB solve. Resets any prior incumbent.
fn arm_emergency_incumbent(instance: Arc<ParsedPbInstance>) {
    *lock_emergency_incumbent() = Some(EmergencyIncumbent {
        instance,
        assignment: None,
    });
}

/// Disarm the emergency-flush store once the normal output path owns emission.
fn disarm_emergency_incumbent() {
    *lock_emergency_incumbent() = None;
}

/// Record the latest VIG-verified feasible incumbent for emergency flushing.
/// No-op when the store is disarmed (e.g. WBO solves).
fn record_emergency_incumbent(assignment: &[bool]) {
    if let Some(slot) = lock_emergency_incumbent().as_mut() {
        slot.assignment = Some(assignment.to_vec());
        EMERGENCY_INCUMBENT_GENERATION.fetch_add(1, Ordering::SeqCst);
    }
}

/// Bumped on every recorded incumbent: lets the SIGTERM watchdog detect a
/// fresher incumbent recorded during the grace window and re-render once, so
/// the flushed `v` line never lags the last streamed `o` improvement.
static EMERGENCY_INCUMBENT_GENERATION: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Pure core of the emergency flush: emit a stored incumbent as `SATISFIABLE`
/// only if it passes the boundary VIG against the original constraints; otherwise
/// fail closed to `UNKNOWN`. Kept side-effect-free for direct unit testing.
fn emergency_emit_solution(
    constraints: &[ay_pb::PbConstraint],
    assignment: Option<&[bool]>,
) -> PbExactSolution {
    match assignment {
        Some(assignment) if ay_pb::verify_all_constraints(constraints, assignment) => {
            PbExactSolution {
                status: PbStatus::Satisfiable,
                assignment: assignment.to_vec(),
                objective: None,
            }
        }
        _ => unknown_exact_solution(),
    }
    .normalized_for_competition()
}

/// Flush the emergency incumbent (VIG-gated) or `UNKNOWN` to `out`.
fn flush_emergency_incumbent_or_unknown<W: Write>(out: &mut PbOutputWriter<W>) -> PbStatus {
    let emitted = {
        let guard = lock_emergency_incumbent();
        match guard.as_ref().and_then(|slot| {
            slot.vig_constraints()
                .map(|constraints| (constraints, slot.assignment.as_deref()))
        }) {
            Some((constraints, assignment)) => emergency_emit_solution(constraints, assignment),
            None => unknown_exact_solution(),
        }
    };
    if out.write_full_result_exact(&emitted).is_ok() {
        emitted.status
    } else {
        PbStatus::Unknown
    }
}

/// Final-emission arbitration between the cooperative output path (incl. the
/// panic-path flush) and the SIGTERM force-flush watchdog. Every writer
/// claims BEFORE its first byte; claim-before-write is what makes a doubled
/// or byte-spliced `s`/`v` emission impossible: the competition allows
/// exactly one `s` line (a second one, or a `v` payload with interleaved
/// fragments, is scored as a WRONG ANSWER, not UNKNOWN), while a
/// claimed-then-SIGKILL-truncated emission degrades to UNKNOWN via the
/// incomplete-`v`-line rule — the fail-closed direction.
///
/// Three states rather than a bool so the arbitration is strictly between
/// the two THREADS, not between successive solves: in-process test harnesses
/// run many solves per process, and a monotonic "claimed" bool would make
/// every solve after the first write nothing. A COOPERATIVE residue from an
/// earlier solve therefore does not block a later cooperative write; only a
/// live WATCHDOG claim does (and a watchdog claim always ends in
/// `process::exit`, so it can never leak into a later solve).
const EMISSION_OPEN: u8 = 0;
const EMISSION_COOPERATIVE: u8 = 1;
const EMISSION_WATCHDOG: u8 = 2;
static FINAL_EMISSION_STATE: std::sync::atomic::AtomicU8 =
    std::sync::atomic::AtomicU8::new(EMISSION_OPEN);

/// Marks the cooperative result as emitted (stands the watchdog down). Keeps
/// an existing claim untouched.
fn mark_final_result_emitted() {
    let _ = FINAL_EMISSION_STATE.compare_exchange(
        EMISSION_OPEN,
        EMISSION_COOPERATIVE,
        Ordering::SeqCst,
        Ordering::SeqCst,
    );
}

/// True once any writer holds the emission claim (watchdog stand-down check).
fn final_result_emitted() -> bool {
    FINAL_EMISSION_STATE.load(Ordering::SeqCst) != EMISSION_OPEN
}

/// Cooperative-path claim. Returns `false` ONLY when the SIGTERM watchdog
/// owns stdout (its raw write is in flight and `process::exit` follows) —
/// the caller must then write nothing rather than splice into that emission.
fn claim_cooperative_emission() -> bool {
    match FINAL_EMISSION_STATE.compare_exchange(
        EMISSION_OPEN,
        EMISSION_COOPERATIVE,
        Ordering::SeqCst,
        Ordering::SeqCst,
    ) {
        Ok(_) => true,
        Err(current) => current == EMISSION_COOPERATIVE,
    }
}

/// Watchdog claim: wins only from OPEN; any cooperative claim beats it.
fn claim_watchdog_emission() -> bool {
    FINAL_EMISSION_STATE
        .compare_exchange(
            EMISSION_OPEN,
            EMISSION_WATCHDOG,
            Ordering::SeqCst,
            Ordering::SeqCst,
        )
        .is_ok()
}

/// Proof artifacts (temp proof file, sidecar) of the solve in flight, removed
/// by the SIGTERM force-flush watchdog before `process::exit`. Without this,
/// a kill mid-proof leaves `PROOFFILE.<ext>.tmp-<pid>-<nonce>` debris next to
/// the organizer-provided PROOFFILE — files the harness never asked for
/// (PB-COMP §4.3 confines writes to stdout/stderr/TMPDIR plus PROOFFILE).
/// The COMMITTED proof is never registered here: the atomic temp→PROOFFILE
/// rename happens before the answer is claimed, and claimed answers stand
/// down the watchdog via [`FINAL_EMISSION_STATE`].
static ACTIVE_PROOF_TEMP_PATHS: Mutex<Vec<PathBuf>> = Mutex::new(Vec::new());

fn register_proof_temp_for_sigterm_cleanup(path: &Path) {
    let mut paths = ACTIVE_PROOF_TEMP_PATHS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    paths.push(path.to_path_buf());
}

fn unregister_proof_temp_for_sigterm_cleanup(path: &Path) {
    let mut paths = ACTIVE_PROOF_TEMP_PATHS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    paths.retain(|registered| registered != path);
}

fn remove_registered_proof_temps() {
    let paths = ACTIVE_PROOF_TEMP_PATHS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for path in paths.iter() {
        let _ = fs::remove_file(path);
    }
}

/// Grace between observing SIGTERM and force-flushing. The competition sends
/// SIGKILL exactly ONE second after SIGTERM (requirements §4.3); the
/// cooperative wind-down (worker collection, epilogue gates) can take ~10s on
/// pathological instances, which forfeits the answer entirely. 800ms lets
/// fast wind-downs finish normally while the watchdog pre-renders its flush
/// buffer DURING the grace (see [`spawn_sigterm_flush_watchdog`]), so only
/// the raw `write_all` has to fit in the ~200ms left before SIGKILL.
const SIGTERM_FLUSH_GRACE: Duration = Duration::from_millis(800);

/// PAR-2 CONFORMANCE (campaign M0): guarantee an `s` line lands promptly after
/// SIGTERM even when the solve thread cannot wind down in time.
///
/// A dedicated watchdog thread (normal thread context — the actual signal
/// handler remains the async-signal-safe `signal_hook` flag) waits for the
/// SIGTERM flag, PRE-RENDERS the VIG-gated emergency incumbent (or fail-closed
/// `UNKNOWN`) while granting the cooperative path [`SIGTERM_FLUSH_GRACE`],
/// re-renders once if a fresher incumbent landed during the grace, CLAIMS the
/// emission slot ([`claim_watchdog_emission`] — losing the claim means the
/// cooperative path owns stdout and the watchdog stands down), and only then
/// writes to the RAW stdout fd — the solve thread may hold the `stdout` lock
/// mid-line, so locking would deadlock; a leading newline guards the output
/// against splicing into a partial line (the competition checker disregards
/// the truncated fragment). Exits the process immediately after: the flushed
/// result is final by construction (exactly one writer ever holds the claim,
/// and the process is gone before anything else could write).
fn spawn_sigterm_flush_watchdog(term_flag: Arc<AtomicBool>) {
    let _ = std::thread::Builder::new()
        .name("sigterm-flush".into())
        .spawn(move || {
            loop {
                if final_result_emitted() {
                    return;
                }
                if term_flag.load(Ordering::SeqCst) {
                    break;
                }
                std::thread::sleep(Duration::from_millis(25));
            }
            // Anchor the grace deadline at SIGTERM observation, BEFORE the
            // pre-render: the rules give exactly ONE second from SIGTERM to
            // SIGKILL, so render time must be absorbed BY the grace window,
            // never added to it (deadline-after-render pushed the flush to
            // grace + render on large instances, straight past the SIGKILL).
            let deadline = Instant::now() + SIGTERM_FLUSH_GRACE;
            // Pre-render NOW, concurrently with the cooperative grace window:
            // the boundary VIG plus the v-line render are O(instance) (hundreds
            // of milliseconds on multi-million-row inputs) and must not eat
            // into the ~200 ms left between grace expiry and the harness
            // SIGKILL.
            let generation = EMERGENCY_INCUMBENT_GENERATION.load(Ordering::SeqCst);
            let (mut rendered, mut status) = render_emergency_flush();
            while Instant::now() < deadline {
                if final_result_emitted() {
                    return;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            // A better incumbent may have been recorded during the grace
            // window; re-render once so the flushed `v` line never lags the
            // last streamed `o` improvement. Usually a no-op.
            if EMERGENCY_INCUMBENT_GENERATION.load(Ordering::SeqCst) != generation {
                (rendered, status) = render_emergency_flush();
            }
            // Claim the emission slot; if the cooperative path claimed first it
            // OWNS stdout — stand down. Its write is either complete or gets
            // SIGKILL-truncated mid-`v`-line, which the rules score as UNKNOWN;
            // writing here instead would splice bytes into that emission and
            // turn a fail-closed UNKNOWN into a wrong answer.
            if !claim_watchdog_emission() {
                return;
            }
            // stdout FIRST, cleanup after: a truncated flush degrades to
            // UNKNOWN, while a missing `s` line forfeits the answer outright —
            // and temp debris is unavoidable anyway whenever SIGKILL lands
            // before this thread runs at all.
            // SAFETY: fd 1 (stdout) is open for the lifetime of the process;
            // the File is immediately forgotten so the fd is not closed and
            // no other owner is disturbed. Raw-fd writing is required here
            // because the solve thread may hold the std stdout lock.
            #[cfg(unix)]
            unsafe {
                use std::os::unix::io::FromRawFd;
                let mut raw_stdout = File::from_raw_fd(1);
                let _ = raw_stdout.write_all(&rendered);
                let _ = raw_stdout.flush();
                std::mem::forget(raw_stdout);
            }
            #[cfg(not(unix))]
            let _ = &rendered;
            // The solve thread may be mid-proof-write; the process is about to
            // exit, so no committed proof exists for this run (commit precedes
            // the claim). Remove the in-flight temp artifacts so the harness
            // directory holds nothing but what it asked for.
            remove_registered_proof_temps();
            std::process::exit(pb_exit_code(status));
        });
}

/// Renders the emergency-flush buffer (leading splice-guard newline, comment,
/// VIG-gated `s`/`v` result) plus its status. O(instance) — the watchdog calls
/// it during the grace window, off the post-grace critical tail.
///
/// The `EMERGENCY_INCUMBENT` mutex is held only for a cheap snapshot (an
/// `Arc` refcount bump plus one assignment `Vec` clone). The O(instance) VIG
/// verify and v-line render run entirely OUTSIDE the lock: the solve thread's
/// wind-down calls `record_emergency_incumbent`/`disarm_emergency_incumbent`
/// on that same mutex, and blocking it for the VIG's duration would burn the
/// very grace window this pre-render exists to exploit (priority inversion).
fn render_emergency_flush() -> (Vec<u8>, PbStatus) {
    let snapshot: Option<(Arc<ParsedPbInstance>, Option<Vec<bool>>)> = {
        let guard = lock_emergency_incumbent();
        guard
            .as_ref()
            .map(|slot| (Arc::clone(&slot.instance), slot.assignment.clone()))
    };
    let emitted = match snapshot.as_ref().and_then(|(instance, assignment)| {
        instance
            .vig_constraints()
            .map(|constraints| (constraints, assignment.as_deref()))
    }) {
        Some((constraints, assignment)) => emergency_emit_solution(constraints, assignment),
        None => unknown_exact_solution(),
    };
    let mut rendered: Vec<u8> = Vec::with_capacity(4096);
    rendered.push(b'\n');
    {
        let mut out = PbOutputWriter::new(&mut rendered);
        let _ = out.write_comment("SIGTERM: cooperative wind-down overran; forced flush");
        let _ = out.write_full_result_exact(&emitted);
    }
    (rendered, emitted.status)
}

fn main() {
    let status = match std::panic::catch_unwind(run_main) {
        Ok(Ok(status)) => {
            mark_final_result_emitted();
            status
        }
        Ok(Err(err)) => {
            mark_final_result_emitted();
            eprintln!("ERROR: {err}");
            std::process::exit(2);
        }
        Err(_) => {
            // A panic unwinds past the solve pipelines' `result.is_err()`
            // cleanup, so any in-flight temp proof file survives the unwind —
            // drain the registry here for parity with the SIGTERM watchdog
            // (§4.3 write confinement: nothing but PROOFFILE may persist).
            remove_registered_proof_temps();
            // Claim the emission slot BEFORE writing so neither the SIGTERM
            // watchdog nor this flush can interleave with the other. If the
            // watchdog won, it owns stdout and is about to exit the process.
            if claim_cooperative_emission() {
                let mut out = PbOutputWriter::new(io::stdout().lock());
                let _ = out.write_comment("internal error: solver panicked");
                // PROOF-TO-SCORE: flush the best VIG-verified feasible incumbent
                // the solve thread found before it unwound, instead of discarding
                // it as UNKNOWN. Fails closed to UNKNOWN when no verified
                // incumbent exists.
                flush_emergency_incumbent_or_unknown(&mut out)
            } else {
                // The watchdog owns stdout and is about to exit the process;
                // cede completely rather than race its raw flush with a
                // different exit code.
                loop {
                    std::thread::park();
                }
            }
        }
    };
    std::process::exit(pb_exit_code(status));
}

fn run_main() -> Result<PbStatus, String> {
    let mut args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() {
        return Err(usage());
    }
    if args == ["--version"] || args == ["-V"] {
        let metadata = pb_stats_build_metadata();
        println!("ay-pb {}", metadata.stamp);
        println!("build.version={}", metadata.version);
        println!("build.commit={}", metadata.commit);
        println!("build.datetime_utc={}", metadata.datetime_utc);
        println!("build.stamp={}", metadata.stamp);
        return Ok(PbStatus::Unknown);
    }
    if args.len() < 2 || args[0] != "pb" {
        return Err(usage());
    }
    let sub = args[1].clone();
    args.drain(0..2);

    match sub.as_str() {
        "solve" => {
            apply_memory_limit();
            let cmd = parse_solve_args(args)?;
            run_solve(&cmd)
        }
        "verify" => run_verify(args),
        _ => Err(usage()),
    }
}

/// Activate process memory-limit protection.
///
/// PB-COMP supplies the per-instance memory budget in the `MEMLIMIT` (MiB)
/// environment variable. Until a limit is set, every `global_memory_exceeded()`
/// / `process_memory_interrupt` guard throughout the solver is dead code, so a
/// pathological allocation (e.g. a large-coefficient SAT encoding) OOMs the
/// process instead of returning UNKNOWN — and in the parallel portfolio an OOM
/// kills the whole process, losing instances other workers could still solve.
/// Honor `MEMLIMIT` when present (reserving ~10% headroom so the solver trips
/// its guard and flushes any incumbent BEFORE the harness's hard kill), and
/// otherwise fall back to the physical-RAM-derived default, mirroring the main
/// `ay` binary.
fn apply_memory_limit() {
    let bytes = match trimmed_env_value("MEMLIMIT").and_then(|v| v.parse::<usize>().ok()) {
        Some(mib) if mib > 0 => {
            let limit = mib.saturating_mul(1024 * 1024);
            // ~10% headroom below the hard external limit (RSS keeps growing for
            // a short lag after the guard observes the threshold).
            limit - limit / 10
        }
        _ => ay_sys::default_memory_limit(),
    };
    if bytes > 0 {
        ay_sys::set_process_memory_limit(bytes);
    }
}

fn usage() -> String {
    concat!(
        "usage:\n",
        "  ay-pb pb solve  [--timeout MS] [--proof FILE] [--stats] [--stats-json] FILE\n",
        "  ay-pb pb verify [--z3|--no-z3|--require-z3] [--z3-timeout SEC] INSTANCE.opb [SOLUTION]\n",
        "                  (SOLUTION is a solver-output file; omit to read it from stdin)"
    )
    .to_string()
}

#[derive(Debug)]
struct VerifyArgs {
    instance: PathBuf,
    solution: Option<PathBuf>,
    z3: ay_pb::Z3Mode,
    z3_timeout_secs: u64,
}

fn parse_verify_args(args: Vec<String>) -> Result<VerifyArgs, String> {
    let mut instance = None;
    let mut solution = None;
    // Default: use z3 if present, never fail merely because it is absent.
    let mut z3 = ay_pb::Z3Mode::Auto;
    let mut z3_timeout_secs = 120u64;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--z3" => z3 = ay_pb::Z3Mode::Auto,
            "--no-z3" => z3 = ay_pb::Z3Mode::Off,
            "--require-z3" => z3 = ay_pb::Z3Mode::Require,
            "--z3-timeout" => {
                i += 1;
                let v = args
                    .get(i)
                    .ok_or_else(|| "--z3-timeout requires a value (seconds)".to_string())?;
                z3_timeout_secs = v
                    .parse::<u64>()
                    .map_err(|_| format!("invalid --z3-timeout value: {v}"))?;
            }
            "--help" | "-h" => return Err(usage()),
            arg if arg.starts_with('-') => return Err(format!("unknown argument: {arg}")),
            path => {
                if instance.is_none() {
                    instance = Some(PathBuf::from(path));
                } else if solution.is_none() {
                    solution = Some(PathBuf::from(path));
                } else {
                    return Err(format!("unexpected extra path: {path}"));
                }
            }
        }
        i += 1;
    }
    Ok(VerifyArgs {
        instance: instance.ok_or_else(usage)?,
        solution,
        z3,
        z3_timeout_secs,
    })
}

/// Independently verify a solver output against an OPB instance. Prints a report
/// and exits 0 (verified) or 1 (a check failed); exits 2 on argument/IO errors.
fn run_verify(args: Vec<String>) -> Result<PbStatus, String> {
    let cmd = parse_verify_args(args)?;

    let instance_text = fs::read_to_string(&cmd.instance)
        .map_err(|e| format!("failed to read instance '{}': {e}", cmd.instance.display()))?;
    let instance = ay_pb::parse_opb(&instance_text).map_err(|e| {
        format!(
            "failed to parse OPB '{}': {e} (note: `verify` supports OPB; WBO is not yet supported)",
            cmd.instance.display()
        )
    })?;

    let solution_text = match &cmd.solution {
        Some(path) => fs::read_to_string(path)
            .map_err(|e| format!("failed to read solution '{}': {e}", path.display()))?,
        None => {
            let mut buf = String::new();
            Read::read_to_string(&mut io::stdin(), &mut buf)
                .map_err(|e| format!("failed to read solution from stdin: {e}"))?;
            buf
        }
    };

    let output = ay_pb::parse_solver_output(&solution_text, instance.num_vars);
    let report = ay_pb::verify(&instance, &output, cmd.z3, cmd.z3_timeout_secs);

    println!("c verify: {}", cmd.instance.display());
    println!("c status: {}", report.status.as_deref().unwrap_or("<none>"));
    for msg in &report.messages {
        println!("c   {msg}");
    }
    println!("s VERIFIED {}", if report.ok { "PASS" } else { "FAIL" });
    std::process::exit(if report.ok { 0 } else { 1 });
}

#[derive(Debug)]
struct SolveArgs {
    file: PathBuf,
    timeout: Option<u64>,
    proof: Option<PathBuf>,
    stats: bool,
    stats_json: bool,
    native: bool,
}

fn parse_solve_args(args: Vec<String>) -> Result<SolveArgs, String> {
    let mut file = None;
    let mut timeout = None;
    let mut proof = None;
    let mut stats = false;
    let mut stats_json = false;
    let mut native = false;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--timeout" | "-t" => {
                i += 1;
                let value = args
                    .get(i)
                    .ok_or_else(|| "--timeout requires a millisecond value".to_string())?;
                timeout = Some(
                    value
                        .parse::<u64>()
                        .map_err(|_| format!("invalid timeout value: {value}"))?,
                );
            }
            "--proof" => {
                i += 1;
                proof = Some(PathBuf::from(
                    args.get(i)
                        .ok_or_else(|| "--proof requires a path".to_string())?,
                ));
            }
            "--stats" => stats = true,
            "--stats-json" => stats_json = true,
            "--native" => native = true,
            "--help" | "-h" => return Err(usage()),
            arg if arg.starts_with('-') => return Err(format!("unknown argument: {arg}")),
            path => {
                if file.is_some() {
                    return Err(format!("unexpected extra input path: {path}"));
                }
                file = Some(PathBuf::from(path));
            }
        }
        i += 1;
    }

    Ok(SolveArgs {
        file: file.ok_or_else(usage)?,
        timeout,
        proof,
        stats,
        stats_json,
        native,
    })
}

fn run_solve(cmd: &SolveArgs) -> Result<PbStatus, String> {
    run_solve_with_writer(cmd, io::stdout().lock())
}

fn run_solve_with_writer<W: Write>(cmd: &SolveArgs, writer: W) -> Result<PbStatus, String> {
    let solve_start = Instant::now();
    let term_flag = install_sigterm_flag();
    spawn_sigterm_flush_watchdog(Arc::clone(&term_flag));
    let mut out = PbOutputWriter::new(writer);
    let timeout_dur = cmd.timeout.map(Duration::from_millis);
    if let Some(proof_path) = cmd.proof.as_deref() {
        clear_existing_proof(proof_path)?;
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
    }

    let input_bytes = match read_file_interruptible(&cmd.file, &mut || {
        term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, solve_start)
    }) {
        Ok(Some(input)) => input,
        Ok(None) => {
            out.write_comment("timeout or termination during PB parse")
                .map_err(|e| e.to_string())?;
            out.write_status(PbStatus::Unknown)
                .map_err(|e| e.to_string())?;
            emit_pb_json_stats(cmd.stats_json, solve_start, PbStatus::Unknown, None);
            return Ok(PbStatus::Unknown);
        }
        Err(err) => {
            // PAR-2 CONFORMANCE: every termination emits exactly one s line.
            // An unreadable input is a fail-closed UNKNOWN (with the error in
            // a comment + stderr), never a bare hard exit the harness scores
            // as silence.
            eprintln!("ERROR: failed to read '{}': {err}", cmd.file.display());
            out.write_comment(&format!("failed to read input: {err}"))
                .map_err(|e| e.to_string())?;
            out.write_status(PbStatus::Unknown)
                .map_err(|e| e.to_string())?;
            emit_pb_json_stats(cmd.stats_json, solve_start, PbStatus::Unknown, None);
            return Ok(PbStatus::Unknown);
        }
    };

    let input = match std::str::from_utf8(&input_bytes) {
        Ok(input) => input,
        Err(err) => {
            eprintln!("ERROR: failed to read '{}': {err}", cmd.file.display());
            out.write_comment(&format!("input is not valid UTF-8: {err}"))
                .map_err(|e| e.to_string())?;
            out.write_status(PbStatus::Unknown)
                .map_err(|e| e.to_string())?;
            emit_pb_json_stats(cmd.stats_json, solve_start, PbStatus::Unknown, None);
            return Ok(PbStatus::Unknown);
        }
    };
    let format = detect_pb_format(&cmd.file, input);
    let parse_should_stop = periodic_stop_check(
        term_flag.as_ref(),
        timeout_dur,
        solve_start,
        PARSE_STOP_POLL_INTERVAL,
    );
    let instance = match parse_instance_interruptible(format, input, parse_should_stop) {
        Ok(instance) => instance,
        Err(ay_pb::ParseError::Interrupted { .. }) => {
            out.write_comment("timeout or termination during PB parse")
                .map_err(|e| e.to_string())?;
            out.write_status(PbStatus::Unknown)
                .map_err(|e| e.to_string())?;
            emit_pb_json_stats(cmd.stats_json, solve_start, PbStatus::Unknown, None);
            return Ok(PbStatus::Unknown);
        }
        Err(err) if err.is_unsupported_input() => {
            out.write_comment(&format!("unsupported input at parse time: {err}"))
                .map_err(|e| e.to_string())?;
            out.write_status(PbStatus::Unsupported)
                .map_err(|e| e.to_string())?;
            emit_pb_json_stats(cmd.stats_json, solve_start, PbStatus::Unsupported, None);
            return Ok(PbStatus::Unsupported);
        }
        Err(err) => {
            // PAR-2 CONFORMANCE: a malformed (or mis-parsed) input is a
            // fail-closed UNKNOWN with a diagnostic comment — if the file was
            // actually valid and the parser is wrong, UNKNOWN is the sound
            // answer; if the file is garbage, UNKNOWN costs nothing.
            eprintln!("ERROR: failed to parse '{}': {err}", cmd.file.display());
            out.write_comment(&format!("failed to parse input: {err}"))
                .map_err(|e| e.to_string())?;
            out.write_status(PbStatus::Unknown)
                .map_err(|e| e.to_string())?;
            emit_pb_json_stats(cmd.stats_json, solve_start, PbStatus::Unknown, None);
            return Ok(PbStatus::Unknown);
        }
    };

    // Share the parsed instance by refcount: the emergency-flush store below
    // must own the rows past a solve-stack unwind, and `Arc` gives it that
    // ownership without duplicating millions of rows on the pre-search path.
    let instance = Arc::new(instance);

    // Arm the panic-time emergency incumbent flush for OPB solves (the incumbent
    // assignment lives in the original variable space; WBO is left disarmed).
    if instance.vig_constraints().is_some() {
        arm_emergency_incumbent(Arc::clone(&instance));
    } else {
        disarm_emergency_incumbent();
    }

    let best_solution = Mutex::new(None);
    let mut jit_telemetry = if cmd.stats || cmd.stats_json {
        Some(jit_candidate_telemetry(&instance, cmd.timeout))
    } else {
        None
    };

    out.write_comment("ay PB solver v0.1")
        .map_err(|e| e.to_string())?;
    if cmd.stats {
        write_stats(
            &mut out,
            &cmd.file,
            &instance,
            cmd.timeout,
            jit_telemetry
                .as_ref()
                .expect("PB stats requested telemetry above"),
        )
        .map_err(|e| e.to_string())?;
    }

    let mut result = solve_pb(
        &instance,
        cmd.proof.as_deref(),
        timeout_dur,
        solve_start,
        cmd.native,
        cmd.stats_json,
        term_flag.as_ref(),
        &mut out,
        &best_solution,
        Some(input),
    )?;
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
    // the incumbent VIG (`sanitize_optimization_incumbent`). WBO is always an
    // optimization instance, so it is skipped exactly as at the boundary VIG
    // (`vig_constraints` returns `None` for WBO).
    if let ParsedPbInstance::Opb(pb) = &*instance {
        if pb.objective.is_none() {
            result.solution = decision_sat_self_checked(result.solution, pb);
        }
    }
    // The normal output path now owns emission; the panic handler must not also
    // print a result, so disarm the emergency-flush store.
    disarm_emergency_incumbent();
    let final_status = write_result_or_best_known(
        &mut out,
        &result.solution,
        &best_solution,
        instance.vig_constraints(),
    )
    .map_err(|e| e.to_string())?;

    if cmd.stats {
        if let Some(timings) = &result.portfolio_timings {
            write_portfolio_timing_stats(&mut out, timings).map_err(|e| e.to_string())?;
        }
    }
    out.write_comment(&format!(
        "solve time: {:.3}s",
        solve_start.elapsed().as_secs_f64()
    ))
    .map_err(|e| e.to_string())?;
    emit_pb_json_stats_with_portfolio(
        cmd.stats_json,
        solve_start,
        final_status,
        jit_telemetry.as_ref(),
        result.portfolio_timings.as_ref(),
    );

    Ok(final_status)
}

fn solve_pb<W: Write>(
    instance: &ParsedPbInstance,
    proof: Option<&Path>,
    timeout_dur: Option<Duration>,
    start: Instant,
    native: bool,
    collect_native_helper_applications: bool,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
    source_text: Option<&str>,
) -> Result<PbSolveOutcome, String> {
    if let Some(proof_path) = proof {
        clear_existing_proof(proof_path)?;
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
    }

    if term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, start) {
        if proof.is_some() {
            let mut guard = best_solution
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            *guard = None;
        }
        return Ok(PbSolveOutcome::without_native_helpers(unknown_solution()));
    }

    // WBO-CERT: certify a WBO optimum via its faithful PBO projection (each paid soft
    // constraint -> a relaxation variable + `clause OR relax`; objective = Σ cost·relax).
    // The projection preserves the admissible-cost optimum (`optimize::wbo::wbo_to_pbo` /
    // `CertifiedWboProjection`), so a VeriPB `BOUNDS` proof of the PROJECTED PBO optimum
    // is a proof of the WBO optimum. Because the proof is over the projected PBO (which
    // adds relaxation variables), it is SELF-CONTAINED only alongside that OPB, so we
    // ALSO emit the projected OPB as `<proof>.opb` — the formula the proof is checked
    // against (`veripb <proof>.opb <proof>`). Verified end-to-end on the wcsp family
    // (real VeriPB 3.0.2). Replaces the prior fail-closed refusal (which scored nothing
    // on the WBO cert track); the reported optimum value is unchanged (faithful
    // projection) and now carries a checkable certificate.
    if let (Some(proof_path), ParsedPbInstance::Wbo(wbo)) = (proof, instance) {
        let pbo = Arc::new(ay_pb::wbo_to_pbo(wbo));
        let formula_path = proof_path.with_extension("opb");
        if let Err(e) = fs::write(&formula_path, ay_pb::instance_to_opb(&pbo)) {
            out.write_comment(&format!(
                "could not write projected OPB formula '{}': {e}; refusing WBO proof",
                formula_path.display()
            ))
            .map_err(|e| e.to_string())?;
            return Ok(PbSolveOutcome::without_native_helpers(
                unsupported_solution(),
            ));
        }
        out.write_comment(&format!(
            "WBO certified via PBO projection; formula written to {}",
            formula_path.display()
        ))
        .map_err(|e| e.to_string())?;
        return solve_opb(
            &pbo,
            proof,
            timeout_dur,
            start,
            native,
            collect_native_helper_applications,
            term_flag,
            out,
            best_solution,
            None,
            source_text,
        );
    }

    // OPT-NLC-CERT: an OPB with product (non-linear) terms cannot be certified by the
    // linear cert path (it declines products). Linearize it first (`ay_pb::linearize`
    // rewrites each product into an AND-auxiliary with linking rows; feasibility- and
    // objective-EQUIVALENT), emit the linear OPB as the `<proof>.opb` companion the
    // proof is checked against, and route the linear instance through `solve_opb`.
    // The linearized optimum == the NLC optimum, so a VeriPB `BOUNDS` proof of it
    // certifies the NLC optimum. Verified end-to-end on `mds_10_4_4` (real VeriPB).
    if let (Some(proof_path), ParsedPbInstance::Opb(pb)) = (proof, instance) {
        if !is_linear(pb) {
            let lin = Arc::new(linearize(pb));
            let formula_path = proof_path.with_extension("opb");
            if let Err(e) = fs::write(&formula_path, ay_pb::instance_to_opb(&lin)) {
                out.write_comment(&format!(
                    "could not write linearized OPB formula '{}': {e}; refusing NLC proof",
                    formula_path.display()
                ))
                .map_err(|e| e.to_string())?;
                return Ok(PbSolveOutcome::without_native_helpers(
                    unsupported_solution(),
                ));
            }
            out.write_comment(&format!(
                "OPT-NLC certified via linearization; formula written to {}",
                formula_path.display()
            ))
            .map_err(|e| e.to_string())?;
            return solve_opb(
                &lin,
                proof,
                timeout_dur,
                start,
                native,
                collect_native_helper_applications,
                term_flag,
                out,
                best_solution,
                None,
                source_text,
            );
        }
    }

    match instance {
        ParsedPbInstance::Opb(pb) => solve_opb(
            pb,
            proof,
            timeout_dur,
            start,
            native,
            collect_native_helper_applications,
            term_flag,
            out,
            best_solution,
            None,
            source_text,
        ),
        ParsedPbInstance::Wbo(wbo) => {
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
                out.write_comment("WBO top cost admits no model (every cost is >= 0)")
                    .map_err(|e| e.to_string())?;
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
                    ))
                    .map_err(|e| e.to_string())?;
                    if probe.c0 >= top {
                        out.write_comment(
                            "wcsp edac trail-checked floor reaches top cost: no admissible model",
                        )
                        .map_err(|e| e.to_string())?;
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
                    out.write_comment(&format!("unsupported WBO conversion: {err}"))
                        .map_err(|e| e.to_string())?;
                    return Ok(PbSolveOutcome::without_native_helpers(
                        unsupported_solution(),
                    ));
                }
            };
            let wbo_best_solution = Mutex::new(None);
            let solution = solve_opb(
                &Arc::new(pbo),
                None,
                timeout_dur,
                start,
                native,
                collect_native_helper_applications,
                term_flag,
                out,
                &wbo_best_solution,
                Some(wbo),
                None,
            )?;
            let wbo_best = wbo_best_solution
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .clone();
            if let Some(best) = wbo_best {
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

/// Run the cheap, size-capped, SELF-CHECKED structural-UNSAT recognizers over the
/// ORIGINAL instance rows (GF(2) parity, exact pigeonhole/Hall counting, bipartite
/// VC matching/cardinality, and the recovery-based parity variant). Returns `true`
/// ONLY when one of them reconstructs an explicit cutting-planes — or
/// summation-certified GF(2) — refutation that replays to `0 >= 1` against the
/// kernel-verified algebra (`proof::refutation_check`).
///
/// SOUNDNESS: every recognizer emits `true` exclusively via its own self-check, so
/// a feasible (SAT) instance can NEVER make this return `true` — it can never flip
/// SAT to UNSAT. ZERO-REGRESSION: each recognizer is O(n+m), size-capped and
/// fail-closed (declines fast on non-matching shapes); the whole pass is only a
/// few hundred milliseconds even on the largest decision instances. That is what
/// makes it safe to run EARLY — before the full-timeout native decision solve.
///
/// Ordering is decline-cost-first (the two near-constant-time scans run before the
/// linear-scan recognizers) and short-circuits on the first self-check, so a
/// non-matching instance pays the minimum and a matching one returns immediately.
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
    // ungated so that class keeps its instant kernel-checked refutation.
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

/// Row-count ceiling for the pre-search structural passes over the FULL original
/// rows: the structural-UNSAT recognizer pass and the clique-arm fingerprint
/// scan. Above this the scans are pure overhead by construction — the
/// recognizers' own success caps sit at or below 2M modeled rows
/// (`matching_cardinality::MAX_ROWS` = 2M is the largest; pigeonhole and the
/// parity-recovery variants cap at 200K modeled rows, plain GF(2) at 4096
/// equality rows), and every family these passes actually win (php, ECgrid,
/// VC grids, mgd-FRB) is orders of magnitude below it — while a full-row scan
/// with per-row normalization costs ~0.1-0.2s per pass on a 6.4M-row instance
/// (measured, lopes-172). Skipping is always sound (the recognizers are
/// fail-closed advisors: a decline just means "go search"), so the gate can
/// only trade a certificate that could not have been produced anyway for
/// pre-search time.
const STRUCTURAL_PRECHECK_MAX_ROWS: usize = 2_000_000;

/// The verdict returned when a structural recognizer self-checks: `s UNSATISFIABLE`
/// with an empty model (a refutation admits no satisfying assignment).
fn structural_unsat_outcome() -> PbSolveOutcome {
    PbSolveOutcome {
        solution: PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: Vec::new(),
            objective: None,
        },
        pb_native_code_helper_applications: 0,
        portfolio_timings: None,
    }
}

fn solve_opb<W: Write>(
    instance_arc: &Arc<PbInstance>,
    proof: Option<&Path>,
    timeout_dur: Option<Duration>,
    start: Instant,
    native: bool,
    collect_native_helper_applications: bool,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
    wbo_projection: Option<&WboInstance>,
    source_opb_text: Option<&str>,
) -> Result<PbSolveOutcome, String> {
    // Borrowed view for the body; the `Arc` itself is only needed by the
    // parallel portfolio and the NLC frontend-timeout watchdog (shared
    // ownership for their worker threads instead of a per-solve row copy).
    let instance: &PbInstance = instance_arc;
    if let Some(proof_path) = proof {
        clear_existing_proof(proof_path)?;
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
        if !is_linear(instance) {
            out.write_comment(
                "proof logging for non-linear PB is not supported; refusing uncertified solve",
            )
            .map_err(|e| e.to_string())?;
            return Ok(PbSolveOutcome::without_native_helpers(
                unsupported_solution(),
            ));
        }
        if let Some(objective) = instance.objective.as_ref() {
            maybe_write_clique_conflict_row_import_map_sidecar(
                instance,
                objective,
                source_opb_text,
                proof_path,
                timeout_dur,
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
        return solve_decision_with_proof(
            instance,
            proof_path,
            timeout_dur,
            start,
            term_flag,
            collect_native_helper_applications,
        );
    }

    // Optional sound symmetry breaking (off by default; see
    // `symmetry_breaking_enabled`). We compute the augmented instance once and
    // feed it to the search-driven branches below. Adding lex constraints is a
    // sound, satisfiability-preserving transformation handled by the real engine.
    // The augmented instance moves into a fresh `Arc` (no row copy) so the
    // parallel portfolio entries below can share whichever instance is searched.
    let symmetry_augmented = maybe_break_symmetries(instance).map(Arc::new);
    let search_arc: &Arc<PbInstance> = symmetry_augmented.as_ref().unwrap_or(instance_arc);
    let search_instance: &PbInstance = search_arc;

    // EARLY self-checked structural-UNSAT recognizers. These O(n+m), size-capped,
    // fail-closed recognizers emit UNSAT only when an explicit cutting-planes /
    // GF(2) refutation over the ORIGINAL rows replays to `0 >= 1` against the
    // kernel-verified algebra. They MUST run here — before the native decision
    // solve below — because a NATIVE LINEAR DECISION instance takes the
    // `solve_decision_native(.., timeout_dur, ..)` branch (full budget) and
    // `return`s straight out, so the identical in-place checks further down (on
    // the non-native decision path) were DEAD for that common path. The
    // consequence was that pure pigeonhole / parity UNSAT instances (php-original,
    // php-exit v1, even-colouring grids) ran the full budget and reported
    // `s UNKNOWN` even though the recognizer decides them in well under a second.
    // Running the recognizers here first hands those families an instant
    // certificate on BOTH the native and non-native paths.
    //
    // SOUND: a feasible (SAT) instance can never produce a self-checked `0 >= 1`,
    // so this can never flip SAT to UNSAT. ZERO-REGRESSION: the pass is cheap and
    // fail-closed, declining fast on every non-matching shape; the SAT / OPTIMUM
    // paths are untouched (the guard is `objective.is_none()`). `proof.is_none()`
    // holds unconditionally here (the proof path returned earlier in `solve_opb`),
    // matching the in-place checks' guard and keeping the certified-proof path on
    // its own dedicated emission route.
    if instance.objective.is_none() && proof.is_none() && structural_unsat_self_checked(instance) {
        if std::env::var_os("AY_CERT_DEBUG").is_some() {
            eprintln!(
                "c refutation self-checked EARLY: structural 0>=1 (kernel-algebra), \
                 emitting s UNSATISFIABLE"
            );
        }
        return Ok(structural_unsat_outcome());
    }

    // CLIQUE arm (default-on, tightly shape-gated to the mgd-FRB signature): runs BEFORE
    // the native / portfolio decision paths because Model RB / FRB instances are forced-
    // satisfiable but defeat complete resolution-style search (2^Ω(n) refutation width),
    // so those paths only ever time out on them. A witness is found by parallel clique
    // local search on the compatibility graph and VERIFIED against the original PB
    // constraints, so a returned SAT is sound by construction — the search can only fail
    // (fall through to the normal path) and never fabricate a model. The detector refuses
    // any instance lacking the one-hot + nogood + conjunction-aux + support fingerprint,
    // so non-FRB instances pay only a cheap scan and there is no regression.
    // The row-count gate leads: `is_linear` + the fingerprint scan walk every
    // row, and no mgd-FRB instance is remotely near the ceiling (see
    // `STRUCTURAL_PRECHECK_MAX_ROWS`), so huge instances skip both scans.
    let clique_gate = instance.objective.is_none()
        && instance.constraints.len() <= STRUCTURAL_PRECHECK_MAX_ROWS
        && clique_arm_enabled()
        && is_linear(instance)
        && clique_arm_matches(instance);
    if clique_gate {
        // PROBE-FIRST guard: give the normal solver a short slice before the arm takes the
        // budget. On selected-PB25 every gate-matcher is UNKNOWN either way, but this makes
        // no-regression hold BY CONSTRUCTION — any gate-matching instance the normal solver
        // can decide quickly is returned by the probe, never starved. The probe (<=3s) is far
        // below the FRB witness times (~2.7s / ~20s), so the FRB wins are preserved.
        let probe_dur = timeout_dur
            .map(|d| Duration::from_millis(((d.as_millis() as u64) / 10).clamp(1000, 3000)));
        let probe = solve_decision_native(search_instance, probe_dur, start, term_flag, false);
        if matches!(
            probe.solution.status,
            PbStatus::Satisfiable | PbStatus::Unsatisfiable
        ) {
            let mut outcome = probe;
            outcome.solution = project_solution_assignment(outcome.solution, instance.num_vars);
            return Ok(outcome);
        }
        // Probe inconclusive -> the clique witness arm gets the full remaining budget.
        let clique_deadline = timeout_dur.map(|d| start + d);
        if let Some(assignment) =
            try_clique_witness(instance, clique_deadline, term_flag, 0x00C1_19E5)
        {
            return Ok(PbSolveOutcome {
                solution: PbSolution {
                    status: PbStatus::Satisfiable,
                    assignment,
                    objective: None,
                },
                pb_native_code_helper_applications: 0,
                portfolio_timings: None,
            });
        }
        // Clique arm found nothing -> fall through to the normal native/portfolio path.
    }

    if native && instance.objective.is_none() {
        if is_linear(instance) {
            let mut outcome = solve_decision_native(
                search_instance,
                timeout_dur,
                start,
                term_flag,
                collect_native_helper_applications,
            );
            // The search instance may carry added lex rows but no new variables;
            // project back to the original variable count for output safety.
            outcome.solution = project_solution_assignment(outcome.solution, instance.num_vars);
            return Ok(outcome);
        }
        let linearized = linearize(instance);
        let mut outcome = solve_decision_native(
            &linearized,
            timeout_dur,
            start,
            term_flag,
            collect_native_helper_applications,
        );
        outcome.solution = project_solution_assignment(outcome.solution, instance.num_vars);
        return Ok(outcome);
    }

    if instance.objective.is_none() {
        // NOTE: the GF(2)-parity / recovery-parity / pigeonhole / VC-matching
        // structural-UNSAT recognizers used to run (again) right here on the
        // non-native decision path. They are exactly the four recognizers the
        // EARLY `structural_unsat_self_checked` pass above already ran under
        // the identical `objective.is_none() && proof.is_none()` guard on the
        // identical ORIGINAL rows, so this second pass could never fire when
        // the first declined — it only re-paid the full recognizer scan
        // (~0.12s at 6.4M rows, measured on lopes-172). The duplicate pass was
        // removed; the EARLY pass is the single emission point for all four
        // recognizers on both the native and non-native decision paths.

        // PARALLEL track (batteries-included default): with a memory-clamped
        // core budget of at least two workers, run the diverse-strategy
        // parallel portfolio and take the first proven verdict. `AY_PB_PARALLEL`
        // defaults to AUTO (`NBCORE`-sized, memory-clamped); `AY_PB_PARALLEL=0`
        // opts out. BELOW two workers (NBCORE=1 / tiny MEMLIMIT) this gate
        // keeps the ORIGINAL sequential path below — including its
        // probe-then-detect `try_symmetry_decision` arm — instead of a
        // degenerate one-worker "parallel" run whose concurrent symmetry arm
        // would open with a pure-sleep probe (no workers alongside to serve
        // the probe role). `search_instance` carries any sound lex-leader
        // symmetry rows (`AY_PB_SYMMETRY`); `break_symmetries` adds rows,
        // never variables, so a model needs no projection (output-safe).
        if portfolio::should_parallelize_decision(search_instance) {
            let solution = portfolio::solve_decision_portfolio_parallel(
                search_arc,
                timeout_dur,
                start,
                term_flag,
            );
            return Ok(PbSolveOutcome {
                solution,
                pb_native_code_helper_applications: 0,
                portfolio_timings: None,
            });
        }

        // SYMMETRY arm (default-on, shape-gated): for large, highly-symmetric
        // decision instances (the "mat" matrix family), first PROBE with the
        // normal portfolio for a short slice of the budget. Easy instances (e.g.
        // satisfiable mat siblings) are solved by the probe and pay NO symmetry
        // overhead. If the probe does not decide, detect a generating set of
        // verified automorphisms, augment with sound lex-leader rows, and solve
        // the augmented instance for the remaining time — which converts
        // otherwise-undecidable hard UNSAT mat instances. Soundness is by
        // construction (every added row comes from a verified generator).
        if symmetry_arm_enabled() && symmetry_augmented.is_none() {
            if let Some(solution) = try_symmetry_decision(instance, timeout_dur, start, term_flag) {
                return Ok(PbSolveOutcome {
                    solution,
                    pb_native_code_helper_applications: 0,
                    portfolio_timings: None,
                });
            }
        }

        let portfolio_result = portfolio::solve_decision_portfolio_with_timings(
            search_instance,
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

    let objective = instance.objective.as_ref().expect("checked above");

    // OBJECTIVE-RANGE OVERFLOW RECOVERY (proof-to-score). When the objective's
    // value range does not fit i128, the optimizer cannot soundly encode/bound it
    // (the totalizer / OLL / LP-relaxation paths all assume an i128-representable
    // objective), so the portfolio bails to `s UNSUPPORTED` and forfeits free
    // sound-correct credit. The CONSTRAINTS, however, are ordinary PB rows we can
    // still solve as a pure FEASIBILITY (decision) problem with the objective
    // ignored. We recover the answer here instead of withholding it. See
    // `solve_overflowing_objective_as_feasibility` for the soundness argument; it
    // NEVER claims OPTIMUM. Restricted to the direct OPB path: a WBO instance
    // reaches here as its PBO projection, whose witness must be mapped back to the
    // WBO variable space (handled only on the normal optimization path below), so
    // we leave WBO overflow on its existing fail-closed behavior.
    if wbo_projection.is_none() && !ay_pb::objective_range_fits_i64(objective) {
        return Ok(solve_overflowing_objective_as_feasibility(
            instance,
            objective,
            timeout_dur,
            start,
            term_flag,
        ));
    }

    // SMALL NON-LINEAR exact-exhaustion routing: when the instance's entire `{0,1}^n`
    // space is small enough to enumerate (`portfolio::small_nlc_exhaustible`), keep it
    // OFF this front-end-timeout wrapper. That wrapper opens with tiny-budget probes
    // (1ms / 1s solver timeouts) that short-circuit on the first SATISFIABLE incumbent,
    // which would starve the post-solve exact-exhaustion upgrade and leave a trivially
    // provable optimum unproven. These instances instead fall through to the normal
    // full-budget optimization path below, where the upgrade runs to completion and the
    // verdict still flows through `finalize_optimum_verdict`. Larger non-linear
    // constrained instances keep the front-end-timeout wrapper — UNLESS the parallel
    // portfolio takes them (`should_parallelize_optimization`, batteries-included
    // default on multi-core): the parallel route runs its own NLC-safe worker set
    // (P1 = this full sequential routing on a dedicated core, the internally
    // linearizing SAT-encoded arms, and the product-native `nlc-sls-opt` primal) and
    // enforces the wall clock itself via the coordinator's hard collection deadline.
    // With parallelism unavailable (`AY_PB_PARALLEL=0` / single core / memory clamp)
    // this sequential wrapper path is byte-identical to before.
    if wbo_projection.is_none()
        && !is_linear(instance)
        && timeout_dur.is_some()
        && !instance.constraints.is_empty()
        && !portfolio::small_nlc_exhaustible(instance, objective)
        && !portfolio::should_parallelize_optimization(search_instance)
    {
        return solve_nonlinear_optimization_with_frontend_timeout(
            instance_arc,
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
        if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
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
    // construction) — run the diverse-strategy parallel portfolio.
    // Soundness/quality invariants:
    // * The priority-1 worker IS the full sequential routing on a dedicated
    //   core, so the parallel path is never weaker than the baseline, and a
    //   definitive verdict is adopted ONLY from a complete baseline engine.
    // * Every incumbent streams through the coordinator's
    //   `sanitize_optimization_incumbent` gate into the SAME `on_improve` as
    //   the sequential path, whose strict-improvement filter keeps the `o`
    //   line stream monotone.
    // * The worker budget is memory-clamped inside the parallel entry
    //   (`clamp_parallel_workers_by_memory`), so huge instances degrade
    //   gracefully toward the sequential path instead of OOMing.
    // * Proof mode never reaches here (`solve_optimization_with_proof`
    //   returned above) — the certified pipeline stays sequential
    //   fail-closed.
    // * WBO: the parallel route only changes WHO searches the REDUCED PBO
    //   (`try_wbo_to_pbo` output, including its top-cost budget row). The
    //   projection-before-gate order is untouched: incumbents flow through
    //   this SAME `on_improve` closure (which re-projects + re-scores against
    //   the ORIGINAL WBO via `exact_incumbent_from_model` and suppresses
    //   intermediate `o` lines under `wbo_projection.is_some()`), and the
    //   final result takes the identical `project_wbo_solution` /
    //   `prefer_cheaper_cached_wbo_incumbent` /
    //   `exact_wbo_solution_from_assignment` top-cost fail-closed gates
    //   below.
    // The earlier DEC-ONLY gate (Charlotte-06-2: parallel o=6084 vs
    // sequential o=6009 under whole-core contention) predates the
    // priority-ordered core budgeting with the P1 sequential worker first and
    // the diversified primal arms dropped first; the parallel track is now
    // the default, with `AY_PB_PARALLEL=0` as the sequential opt-out.
    // `search_instance` carries any sound lex-leader symmetry rows (objective
    // identical to the original, so the optimum is preserved).
    let (portfolio_solution_raw, portfolio_timings) =
        if portfolio::should_parallelize_optimization(search_instance) {
            let parallel_solution = if wbo_projection.is_some() {
                portfolio::solve_wbo_reduced_optimization_portfolio_parallel(
                    search_arc,
                    objective,
                    timeout_dur,
                    start,
                    term_flag,
                    &mut on_improve,
                )
            } else {
                portfolio::solve_optimization_portfolio_parallel(
                    search_arc,
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
                search_instance,
                objective,
                timeout_dur,
                start,
                term_flag,
                &mut on_improve,
            );
            (portfolio_result.solution, Some(portfolio_result.timings))
        };
    // WBO primal-SLS fallback (opt-in, AY_PB_WBO_SLS, default OFF): when the
    // complete portfolio finished the reduced-PBO solve with NO incumbent (still
    // Unknown — the celar / uclid soft-heavy WBO families, where the standalone
    // SLS would otherwise DECLINE because the relaxation blow-up pushes the var
    // count past the default cap), run the primal SLS over the reduced PBO with
    // the higher WBO cap to land+descend a feasible incumbent in the remaining
    // budget. Every incumbent is streamed through the same `on_improve` (which
    // re-projects + re-scores against the ORIGINAL WBO) and re-verified by the
    // portfolio's `sanitize_optimization_incumbent`, so this cannot affect
    // soundness. Only fires on the WBO path and only when the portfolio produced
    // nothing, so the linear/non-WBO paths and the fast portfolio wins are
    // untouched.
    let portfolio_solution = if wbo_projection.is_some()
        && portfolio::wbo_sls_enabled()
        && portfolio_solution_raw.status == PbStatus::Unknown
    {
        portfolio::solve_wbo_reduced_sls(
            instance,
            objective,
            timeout_dur,
            start,
            term_flag,
            &mut on_improve,
        )
    } else {
        portfolio_solution_raw
    };
    let result = match wbo_projection {
        Some(wbo) => project_wbo_solution(portfolio_solution, wbo),
        None => portfolio_solution,
    };
    // TOP-LEVEL CHECKED OPTIMUM GATE (TASK O1): the single chokepoint covering
    // every OPTIMUM-emitting path. A self-checking cutting-planes dual-bound
    // certificate over the ORIGINAL constraints either promotes a certificate-
    // backed incumbent to OPTIMUM (additive, sound by construction) or — under the
    // opt-in strict policy — downgrades an uncertified OPTIMUM to SATISFIABLE.
    // Skipped for the WBO projection path (objective lives in the projected space).
    let result = if wbo_projection.is_none() {
        portfolio::finalize_optimum_verdict(result, instance, objective, &|| {
            term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, start)
        })
    } else {
        result
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
    Ok(PbSolveOutcome {
        solution: final_optimization_result_after_anytime_stream(result, streamed_best_obj),
        pb_native_code_helper_applications: 0,
        portfolio_timings,
    })
}

/// Recovery path for optimization instances whose objective value range does not
/// fit i128 (`!objective_range_fits_i64`). The optimizer would bail to
/// `s UNSUPPORTED`; we instead solve the pure FEASIBILITY problem (objective
/// ignored) and convert it to a sound-correct verdict:
///
/// * UNSATISFIABLE — no feasible point exists for the constraints, so there is no
///   feasible point for ANY objective; the OPT instance is UNSAT. Sound because
///   the decision solve runs on the ORIGINAL constraints (no symmetry rows added
///   on this path) and linearization is equisatisfiable.
/// * SATISFIABLE — the witness is projected to the original variable space and
///   re-verified against the ORIGINAL constraints (the VIG). On success we attach
///   the exact `o`-line iff the witness's own objective value fits i128 (a valid
///   upper bound); otherwise we emit `s SATISFIABLE` with no `o`-line. A witness
///   that fails the VIG falls closed to `s UNKNOWN`.
/// * anything else (UNKNOWN / inconclusive) — `s UNKNOWN`.
///
/// This NEVER claims OPTIMUM: the objective is not i128-representable, so we
/// cannot bound it. It can only upgrade a forfeited `UNSUPPORTED` into a
/// sound-correct SAT/UNSAT/UNKNOWN — never fabricate a verdict.
fn solve_overflowing_objective_as_feasibility(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
) -> PbSolveOutcome {
    // Build a pure decision instance from the ORIGINAL constraints (objective
    // stripped). Non-linear instances are linearized to an equisatisfiable linear
    // instance for the decision solver; the witness is projected back below.
    let mut decision_instance = if is_linear(instance) {
        instance.clone()
    } else {
        linearize(instance)
    };
    decision_instance.objective = None;

    let decision =
        portfolio::solve_decision_portfolio(&decision_instance, timeout_dur, start, term_flag);
    let solution = match decision.status {
        PbStatus::Unsatisfiable => PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: Vec::new(),
            objective: None,
        },
        PbStatus::Satisfiable | PbStatus::OptimumFound => {
            // Project off any linearization aux variables and re-verify the
            // witness against the ORIGINAL constraints at the emission boundary.
            let projected = project_solution_assignment(decision, instance.num_vars).assignment;
            if ay_pb::verify_all_constraints(&instance.constraints, &projected) {
                // Attach the exact objective value only when it itself fits i128
                // (this single model selects a subset of terms whose sum may still
                // overflow even though no individual coefficient does). A finite
                // value is a valid upper bound; an overflowing one is dropped so we
                // never emit a wrong/clamped `o`-line.
                let objective_value = eval_objective_exact(objective, &projected).ok();
                PbSolution {
                    status: PbStatus::Satisfiable,
                    assignment: projected,
                    objective: objective_value,
                }
            } else {
                unknown_solution()
            }
        }
        _ => unknown_solution(),
    };

    PbSolveOutcome::without_native_helpers(solution)
}

enum OptimizationWorkerEvent {
    Improvement(PbExactSolution),
    Done(portfolio::PbPortfolioOutcome),
}

fn solve_nonlinear_optimization_with_frontend_timeout<W: Write>(
    instance: &Arc<PbInstance>,
    objective: &ay_pb::PbObjective,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> Result<PbSolveOutcome, String> {
    let Some(timeout_dur) = timeout_dur else {
        unreachable!("caller only uses front-end timeout wrapper when timeout is present");
    };
    if objective_has_only_nonnegative_coefficients(objective) {
        if let Some(outcome) = try_nonlinear_optimization_probe(
            instance,
            objective,
            Duration::from_millis(1),
            Duration::from_millis(250),
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
                Duration::from_secs(1),
                Duration::from_millis(2_500),
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
    // Shared ownership for the detached worker (it may outlive this frame on
    // timeout): a refcount bump instead of the previous full-instance clone,
    // which re-copied every row on the pre-search path once per solve.
    let worker_instance = Arc::clone(instance);
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
        if term_flag.load(Ordering::SeqCst) || Instant::now() >= deadline {
            worker_stop.store(true, Ordering::SeqCst);
            let result = best_known_legacy_solution(best_solution);
            return Ok(PbSolveOutcome {
                solution: final_optimization_result_after_anytime_stream(result, streamed_best_obj),
                pb_native_code_helper_applications: 0,
                portfolio_timings: None,
            });
        }

        let wait = deadline
            .saturating_duration_since(Instant::now())
            .min(Duration::from_millis(10));
        match rx.recv_timeout(wait) {
            Ok(OptimizationWorkerEvent::Improvement(exact_solution)) => {
                let Some(exact_obj_value) = exact_solution.objective else {
                    continue;
                };
                if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                    continue;
                }
                best_obj = Some(exact_obj_value);
                out.write_objective_exact(exact_obj_value)
                    .map_err(|e| e.to_string())?;
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

fn nonlinear_frontend_deadline(start: Instant, timeout_dur: Duration) -> Instant {
    let deadline = start + timeout_dur;
    deadline
        .checked_sub(Duration::from_millis(
            NONLINEAR_OPT_FRONTEND_TIMEOUT_RESERVE_MS,
        ))
        .filter(|reserved| *reserved > start)
        .unwrap_or(start)
}

fn objective_has_only_nonnegative_coefficients(objective: &ay_pb::PbObjective) -> bool {
    objective.terms.iter().all(|term| term.coeff >= 0)
}

fn try_nonlinear_optimization_probe<W: Write>(
    instance: &Arc<PbInstance>,
    objective: &ay_pb::PbObjective,
    solver_timeout: Duration,
    wait_budget: Duration,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> Result<Option<PbSolveOutcome>, String> {
    let probe_start = Instant::now();
    let deadline = probe_start + wait_budget;
    let worker_stop = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();
    // Refcount bump instead of a full-instance row copy (see the frontend
    // watchdog above); the detached probe worker may outlive this frame.
    let worker_instance = Arc::clone(instance);
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
        if term_flag.load(Ordering::SeqCst) || Instant::now() >= deadline {
            worker_stop.store(true, Ordering::SeqCst);
            let result = best_known_legacy_solution(best_solution);
            if result.status == PbStatus::Satisfiable || result.status == PbStatus::OptimumFound {
                return Ok(Some(PbSolveOutcome {
                    solution: final_optimization_result_after_anytime_stream(
                        result,
                        streamed_best_obj,
                    ),
                    pb_native_code_helper_applications: 0,
                    portfolio_timings: None,
                }));
            }
            return Ok(None);
        }

        let wait = deadline
            .saturating_duration_since(Instant::now())
            .min(Duration::from_millis(10));
        match rx.recv_timeout(wait) {
            Ok(OptimizationWorkerEvent::Improvement(exact_solution)) => {
                let Some(exact_obj_value) = exact_solution.objective else {
                    continue;
                };
                if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
                    continue;
                }
                best_obj = Some(exact_obj_value);
                out.write_objective_exact(exact_obj_value)
                    .map_err(|e| e.to_string())?;
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
        objective: best.objective.and_then(|value| i128::try_from(value).ok()),
    }
}

#[allow(clippy::too_many_arguments)]
/// Whether the clique conflict-row/import-map CSV sidecar may be written.
/// OPT-IN via `AY_PB_CLIQUE_ROW_MAP_SIDECAR=1` and OFF by default: the sidecar
/// is a write-only diagnostic for offline tooling, and the competition
/// confines solver writes to stdout/stderr/TMPDIR plus the organizer-provided
/// PROOFFILE (requirements §4.3) — an extra PROOFFILE-adjacent CSV is a
/// compliance violation the organizer can see on every clique-shaped
/// OPT-LIN-CERT instance. No competition entry sets this variable.
fn clique_row_map_sidecar_enabled() -> bool {
    matches!(
        trimmed_env_value("AY_PB_CLIQUE_ROW_MAP_SIDECAR").as_deref(),
        Some("1")
    )
}

fn maybe_write_clique_conflict_row_import_map_sidecar<W: Write>(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    source_opb_text: Option<&str>,
    proof_path: &Path,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
    out: &mut PbOutputWriter<W>,
) -> Result<(), String> {
    if !clique_row_map_sidecar_enabled() {
        return Ok(());
    }
    let Some(source_opb_text) = source_opb_text else {
        return Ok(());
    };

    let sidecar_path = clique_conflict_row_import_map_sidecar_path(proof_path);
    let mut buffer = Vec::new();
    let mut should_stop =
        || term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, start);
    let Some(row_count) = write_max_clique_conflict_row_import_map_csv(
        instance,
        objective,
        source_opb_text,
        &mut buffer,
        &mut should_stop,
    )
    .map_err(|e| {
        format!(
            "failed to build clique conflict row/import map '{}': {e}",
            sidecar_path.display()
        )
    })?
    else {
        clear_existing_clique_conflict_row_import_map_sidecar(proof_path)?;
        return Ok(());
    };

    let temp_sidecar_path = proof_temp_path(&sidecar_path);
    register_proof_temp_for_sigterm_cleanup(&temp_sidecar_path);
    let result: Result<(), String> = (|| {
        {
            let sidecar_file = File::create(&temp_sidecar_path).map_err(|e| {
                format!(
                    "failed to create clique conflict row/import map '{}': {e}",
                    temp_sidecar_path.display()
                )
            })?;
            let mut writer = BufWriter::new(sidecar_file);
            writer.write_all(&buffer).map_err(|e| {
                format!(
                    "failed to write clique conflict row/import map '{}': {e}",
                    temp_sidecar_path.display()
                )
            })?;
            writer.flush().map_err(|e| {
                format!(
                    "failed to flush clique conflict row/import map '{}': {e}",
                    temp_sidecar_path.display()
                )
            })?;
        }
        fs::rename(&temp_sidecar_path, &sidecar_path).map_err(|e| {
            format!(
                "failed to rename '{}' to '{}': {e}",
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
    // Renamed away or removed either way; drop it from the SIGTERM registry.
    unregister_proof_temp_for_sigterm_cleanup(&temp_sidecar_path);
    result?;

    out.write_comment(&format!(
        "clique conflict row/import map sidecar: {} ({} rows)",
        sidecar_path.display(),
        row_count
    ))
    .map_err(|e| e.to_string())
}

fn solve_decision_native(
    instance: &PbInstance,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
    collect_native_helper_applications: bool,
) -> PbSolveOutcome {
    let mut solver = PbCdclSolver::new_interruptible(instance, || {
        term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, start)
    });
    solver.set_native_code_helper_validation_enabled(collect_native_helper_applications);
    let result = solver.solve_interruptible(|| {
        term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, start)
    });
    PbSolveOutcome {
        solution: pb_cdcl_result_to_solution(result, instance.num_vars),
        pb_native_code_helper_applications: solver.native_code_helper_applications(),
        portfolio_timings: None,
    }
}

/// Whether the certified-decision fallback pipeline (native slice -> plain
/// decision solve -> solution-only proof / native UNSAT tail) is enabled.
/// **ON by default**; set `AY_PB_DEC_CERT_PORTFOLIO=0|off|false|no` to restore
/// the native-only full-budget behavior.
fn dec_cert_portfolio_enabled() -> bool {
    !matches!(
        trimmed_env_value("AY_PB_DEC_CERT_PORTFOLIO")
            .map(|v| v.to_ascii_lowercase())
            .as_deref(),
        Some("0" | "off" | "false" | "no")
    )
}

/// Selects the asynchronous proof tap on the decision N1 phase
/// (the development design notes, PHASE 4 default flip): the DENSE
/// conflict path with micro-op capture is now the DEFAULT for proof-on. The
/// legacy synchronous CpConstraint proof path is the escape hatch, selected by
/// `AY_PB_PROOF_TAP=legacy` (or `=0`, kept for symmetry with the old opt-in).
/// `AY_PB_PROOF_TAP=1` and any other value (including unset) stay on the tap.
/// Fail-closed is identical on both paths: any tap failure surfaces via
/// conclude_proof and no proof commits.
fn proof_tap_enabled() -> bool {
    !matches!(
        trimmed_env_value("AY_PB_PROOF_TAP")
            .map(|v| v.to_ascii_lowercase())
            .as_deref(),
        Some("legacy" | "0")
    )
}

/// Writes and atomically commits a SOLUTION-ONLY VeriPB 3 proof for a decision
/// SAT verdict: `conclusion SAT : <literals>` — the checker itself validates
/// the model against the ORIGINAL problem, so no derivation is needed. The
/// proof text comes from the library writer ([`ay_pb::proof::
/// solution_only_sat_proof`]) so this binary cannot drift from the tested
/// proof-emission surface; the helper re-verifies the assignment and withholds
/// the certificate (fail closed) on any mismatch.
fn commit_decision_sat_solution_proof(
    instance: &PbInstance,
    assignment: &[bool],
    proof_path: &Path,
    temp_proof_path: &Path,
) -> Result<(), String> {
    let Some(text) = ay_pb::proof::solution_only_sat_proof(instance, assignment) else {
        // Withheld certificate (unreachable in practice: the caller VIG-verifies
        // first). Remove every proof artifact and emit the SAT answer without a
        // certificate — competition-valid, since certificates cover only
        // UNSAT/OPTIMUM claims and SAT models are checked from the `v` line.
        cleanup_proof_temp(proof_path, temp_proof_path);
        return Ok(());
    };
    fs::write(temp_proof_path, text.as_bytes())
        .map_err(|e| format!("failed to write proof '{}': {e}", temp_proof_path.display()))?;
    commit_or_remove_proof(proof_path, temp_proof_path, true)
}

/// Certified DECISION pipeline (campaign DEC-CERT recovery). Measured reality
/// on quickly-provable DEC instances: plain mode proves in 0.2-3.7s while the
/// proof-logging CDCL times out UNKNOWN at 60s (censored 16-285x overhead) —
/// including on SATISFIABLE instances, where a derivation is not even needed.
/// Pipeline: N1 native proof-logging CDCL on a budget slice (it keeps first
/// shot at a logged UNSAT refutation) -> plain-speed decision solve; a SAT
/// model becomes a checker-validated SOLUTION-ONLY proof; an uncertified
/// UNSAT routes to the native tail (the only compliant refutation source).
/// Every decline keeps the fail-closed UNKNOWN exit.
fn solve_decision_with_proof(
    instance: &PbInstance,
    proof_path: &Path,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
    collect_native_helper_applications: bool,
) -> Result<PbSolveOutcome, String> {
    let temp_proof_path = prepare_proof_temp(proof_path)?;
    let split_enabled = dec_cert_portfolio_enabled() && timeout_dur.is_some();
    let native_deadline: Option<Instant> = if split_enabled {
        let remaining = timeout_dur
            .map(|timeout| timeout.saturating_sub(start.elapsed()))
            .unwrap_or(Duration::ZERO);
        let slice = if let Some(cap_ms) = cert_native_cap_ms_override() {
            Duration::from_millis(cap_ms)
        } else {
            remaining / OPT_CERT_NATIVE_SLICE_DIV
        };
        Some(Instant::now() + slice)
    } else {
        None
    };
    let native_cap = |deadline: Option<Instant>| {
        move || {
            term_flag.load(Ordering::SeqCst)
                || timeout_expired(timeout_dur, start)
                || deadline.is_some_and(|dl| Instant::now() >= dl)
        }
    };

    let result = (|| {
        // PHASE N1: native proof-logging CDCL (capped when the pipeline is
        // eligible; today's full-budget behavior otherwise). By default
        // (proof-tap spec PHASE 4) N1 runs the DENSE conflict-analysis fast
        // path with async micro-op capture; AY_PB_PROOF_TAP=legacy|0 falls
        // back to the legacy synchronous CpConstraint proof path. Either way
        // any tap failure fails closed to UNKNOWN via conclude_proof, never an
        // uncheckable-but-claimed proof.
        let proof_file = File::create(&temp_proof_path)
            .map_err(|e| format!("failed to create '{}': {e}", temp_proof_path.display()))?;
        let mut solver = if proof_tap_enabled() {
            PbCdclSolver::with_proof_tap_interruptible(
                instance,
                BufWriter::with_capacity(1 << 20, proof_file),
                native_cap(native_deadline),
            )
        } else {
            PbCdclSolver::with_proof_writer_interruptible(
                instance,
                BufWriter::new(proof_file),
                native_cap(native_deadline),
            )
        }
        .map_err(|e| format!("failed to initialize proof writer: {e}"))?;
        solver.set_native_code_helper_validation_enabled(collect_native_helper_applications);

        let result = solver.solve_interruptible(native_cap(native_deadline));
        let solution = pb_cdcl_result_to_solution(result, instance.num_vars);
        let mut helper_applications = solver.native_code_helper_applications();
        if matches!(
            solution.status,
            PbStatus::Satisfiable | PbStatus::Unsatisfiable
        ) {
            match solver.conclude_proof() {
                Ok(()) => {
                    commit_or_remove_proof(proof_path, &temp_proof_path, true)?;
                    return Ok(PbSolveOutcome {
                        solution,
                        pb_native_code_helper_applications: helper_applications,
                        portfolio_timings: None,
                    });
                }
                Err(error) => {
                    // Voided certificate (tap soft cap, ring stall budget,
                    // serializer I/O, id desync, ...): the ANSWER is still
                    // valid — never abort the run over a withheld proof (a
                    // `?` here exits with no `s` line, forfeiting a solved
                    // instance). Discard the unusable partial proof and fall
                    // through: a SAT model is salvaged below without
                    // re-solving; an UNSAT re-derives via PHASE P + the N2
                    // legacy-writer tail; with the split disabled, the
                    // fail-closed UNKNOWN exit stands.
                    eprintln!(
                        "warning: proof finalization for '{}' failed ({error}); \
                         retrying via the fallback phases",
                        proof_path.display()
                    );
                    let _ = fs::remove_file(&temp_proof_path);
                }
            }
        }

        if split_enabled {
            // Release the native proof-writer handle so the fallback phases
            // can overwrite the temp file (the partial proof is unusable).
            drop(solver);

            // Salvage a voided-certificate N1 SAT answer without re-solving:
            // the model is already in hand; VIG-verify it and commit the
            // checker-validated solution-only proof.
            if solution.status == PbStatus::Satisfiable
                && ay_pb::verify_all_constraints(&instance.constraints, &solution.assignment)
            {
                commit_decision_sat_solution_proof(
                    instance,
                    &solution.assignment,
                    proof_path,
                    &temp_proof_path,
                )?;
                return Ok(PbSolveOutcome {
                    solution,
                    pb_native_code_helper_applications: helper_applications,
                    portfolio_timings: None,
                });
            }

            // PHASE P: plain-speed decision solve with the remaining budget.
            let plain = solve_decision_native(
                instance,
                timeout_dur,
                start,
                term_flag,
                collect_native_helper_applications,
            );
            helper_applications += plain.pb_native_code_helper_applications;
            match plain.solution.status {
                PbStatus::Satisfiable => {
                    // VIG first; the official checker re-validates the model
                    // from the conclusion line, so this proof cannot overclaim.
                    if ay_pb::verify_all_constraints(
                        &instance.constraints,
                        &plain.solution.assignment,
                    ) {
                        commit_decision_sat_solution_proof(
                            instance,
                            &plain.solution.assignment,
                            proof_path,
                            &temp_proof_path,
                        )?;
                        return Ok(PbSolveOutcome {
                            solution: plain.solution,
                            pb_native_code_helper_applications: helper_applications,
                            portfolio_timings: None,
                        });
                    }
                }
                PbStatus::Unsatisfiable => {
                    // Uncertified UNSAT is never emitted: PHASE N2, the native
                    // tail, is the only compliant refutation source.
                    let tail_remaining = timeout_dur
                        .map(|timeout| timeout.saturating_sub(start.elapsed()))
                        .unwrap_or(Duration::ZERO);
                    if tail_remaining >= Duration::from_millis(OPT_CERT_NATIVE_TAIL_MIN_MS) {
                        let proof_file = File::create(&temp_proof_path).map_err(|e| {
                            format!("failed to create '{}': {e}", temp_proof_path.display())
                        })?;
                        let mut tail_solver = PbCdclSolver::with_proof_writer_interruptible(
                            instance,
                            BufWriter::new(proof_file),
                            native_cap(None),
                        )
                        .map_err(|e| format!("failed to initialize proof writer: {e}"))?;
                        tail_solver.set_native_code_helper_validation_enabled(
                            collect_native_helper_applications,
                        );
                        let tail_result = tail_solver.solve_interruptible(native_cap(None));
                        let tail_solution =
                            pb_cdcl_result_to_solution(tail_result, instance.num_vars);
                        helper_applications += tail_solver.native_code_helper_applications();
                        if matches!(
                            tail_solution.status,
                            PbStatus::Satisfiable | PbStatus::Unsatisfiable
                        ) {
                            match tail_solver.conclude_proof() {
                                Ok(()) => {
                                    commit_or_remove_proof(proof_path, &temp_proof_path, true)?;
                                    return Ok(PbSolveOutcome {
                                        solution: tail_solution,
                                        pb_native_code_helper_applications: helper_applications,
                                        portfolio_timings: None,
                                    });
                                }
                                Err(error) => {
                                    // Last certification attempt failed: the
                                    // fail-closed UNKNOWN exit below stands —
                                    // never abort with no `s` line.
                                    eprintln!(
                                        "warning: N2 tail proof finalization for '{}' \
                                         failed ({error}); failing closed to UNKNOWN",
                                        proof_path.display()
                                    );
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        // Fail-closed: no committed proof, no claim.
        cleanup_proof_temp(proof_path, &temp_proof_path);
        Ok(PbSolveOutcome {
            solution: unknown_solution(),
            pb_native_code_helper_applications: helper_applications,
            portfolio_timings: None,
        })
    })();

    if result.is_err() {
        cleanup_proof_temp(proof_path, &temp_proof_path);
    }
    result
}

/// Budget split for the certified-optimization pipeline. `None` deadlines mean
/// the pipeline is ineligible and the native proof run is fully uncapped
/// (today's behavior).
struct CertOptBudgetSplit {
    native_deadline: Option<Instant>,
    native_hard_limit: Option<Instant>,
    improve_grace: Duration,
}

impl CertOptBudgetSplit {
    fn eligible(&self) -> bool {
        self.native_deadline.is_some()
    }
}

/// Decides whether the certified-optimization budget split applies and sizes
/// the native slice. Eligibility: the kill switch is on, a timeout exists (an
/// unbounded run keeps today's unbounded-native semantics), the objective is
/// single-literal linear (the certification helpers' domain), and the
/// objective range fits the optimizer (the portfolio bails Unsupported
/// instantly on overflow, which would discard the whole fallback budget).
fn compute_cert_opt_budget_split(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    timeout_dur: Option<Duration>,
    start: Instant,
) -> CertOptBudgetSplit {
    let uncapped = CertOptBudgetSplit {
        native_deadline: None,
        native_hard_limit: None,
        improve_grace: Duration::ZERO,
    };
    let Some(timeout) = timeout_dur else {
        return uncapped;
    };
    if !opt_cert_portfolio_enabled()
        || !objective.terms.iter().all(|term| term.lits.len() == 1)
        || !ay_pb::objective_range_fits_i64(objective)
    {
        return uncapped;
    }

    let now = Instant::now();
    let remaining = timeout.saturating_sub(start.elapsed());
    if let Some(cap_ms) = cert_native_cap_ms_override() {
        let cap = Duration::from_millis(cap_ms);
        return CertOptBudgetSplit {
            native_deadline: Some(now + cap),
            native_hard_limit: Some(now + cap),
            improve_grace: Duration::ZERO,
        };
    }

    let huge = instance.num_vars >= OPT_CERT_HUGE_MIN_VARS
        || instance.constraints.len() >= OPT_CERT_HUGE_MIN_CONSTRAINTS;
    let (slice_div, ceil_div) = if huge {
        (
            OPT_CERT_NATIVE_SLICE_DIV_HUGE,
            OPT_CERT_NATIVE_CEIL_DIV_HUGE,
        )
    } else {
        (OPT_CERT_NATIVE_SLICE_DIV, OPT_CERT_NATIVE_CEIL_DIV)
    };
    CertOptBudgetSplit {
        native_deadline: Some(now + remaining / slice_div),
        native_hard_limit: Some(now + remaining / ceil_div),
        improve_grace: (remaining / OPT_CERT_IMPROVE_GRACE_DIV)
            .min(Duration::from_millis(OPT_CERT_IMPROVE_GRACE_MAX_MS)),
    }
}

fn native_cap_expired(deadline: &Cell<Option<Instant>>) -> bool {
    deadline.get().is_some_and(|dl| Instant::now() >= dl)
}

/// Extends the native slice after a verified incumbent improvement: monotone,
/// clamped at the hard ceiling, no-op when uncapped or grace-free.
fn extend_native_deadline(deadline: &Cell<Option<Instant>>, split: &CertOptBudgetSplit) {
    let (Some(current), Some(hard)) = (deadline.get(), split.native_hard_limit) else {
        return;
    };
    if split.improve_grace.is_zero() {
        return;
    }
    let extended = (Instant::now() + split.improve_grace).min(hard);
    if extended > current {
        deadline.set(Some(extended));
    }
}

/// Reserve kept for the out-of-band certification re-solve after the fallback
/// portfolio: `remaining/8` clamped to `[10s, 300s]`, never more than half of
/// what is left.
fn certify_reserve(remaining: Duration) -> Duration {
    (remaining / OPT_CERT_CERTIFY_RESERVE_DIV)
        .max(Duration::from_millis(OPT_CERT_CERTIFY_RESERVE_MIN_MS))
        .min(Duration::from_millis(OPT_CERT_CERTIFY_RESERVE_MAX_MS))
        .min(remaining / 2)
}

/// Streams a verified strictly-improving incumbent (o line + cache) exactly
/// like the plain optimization path; shared by every phase of the certified
/// pipeline so the improvement bar is monotone across phase handoffs. Returns
/// `true` iff the bar advanced (a VERIFIED construction — the incumbent helper
/// fails closed to `objective: None` on an infeasible or dominated model).
/// This path never sees WBO (refused before dispatch), so the exact objective
/// needs no projection.
#[allow(clippy::too_many_arguments)]
fn stream_verified_improvement<W: Write>(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
    best_obj: &mut Option<i128>,
    streamed_best_obj: &mut Option<i128>,
    obj_value: i128,
    model: &[bool],
) -> bool {
    let exact_solution = exact_incumbent_from_model(
        instance,
        objective,
        None,
        PbStatus::Satisfiable,
        obj_value,
        *best_obj,
        model,
    );
    let Some(exact_obj_value) = exact_solution.objective else {
        return false;
    };
    if best_obj.is_some_and(|prev| exact_obj_value >= prev) {
        return false;
    }
    *best_obj = Some(exact_obj_value);
    let _ = out.write_objective_exact(exact_obj_value);
    *streamed_best_obj = Some(exact_obj_value);
    cache_exact_solution(best_solution, exact_solution);
    true
}

/// Outcome of the certified-optimization portfolio fallback.
enum OptCertFallbackOutcome {
    /// A committed VeriPB proof backs this OptimumFound outcome.
    Certified(Box<PbSolveOutcome>),
    /// No proof was produced; the portfolio's timings are kept for reporting.
    Declined(Option<portfolio::PbPortfolioPhaseTimings>),
}

/// OPT-LIN-CERT fallback (ported from the `ay` CLI): when the native
/// proof-logging CDCL does not reach `OptimumFound`, run the optimization
/// PORTFOLIO to obtain the exact optimum + a feasible incumbent achieving it,
/// then assemble a VeriPB OPT proof out-of-band (compact first, aux-free
/// second) and commit it atomically.
///
/// `OptimumFound` is claimed only after `commit_or_remove_proof(.., true)`
/// succeeds; every decline keeps the caller's fail-closed behavior. The
/// certification helpers independently re-verify the incumbent against the
/// ORIGINAL constraints and derive the lower bound from their own fresh
/// DRAT-logged UNSAT solve, so a wrong portfolio verdict cannot yield proof
/// text. The caller MUST have released the native proof-writer handle on
/// `temp_proof_path` before calling this (the fallback overwrites that file).
///
/// The portfolio runs to `timeout - certify_reserve(..)` so certification
/// keeps a slice; its incumbents stream through `on_improve` (the shared
/// monotone bar). A portfolio `Unsatisfiable` is never emitted from here —
/// the caller's native tail is the only compliant UNSAT-proof source.
#[allow(clippy::too_many_arguments)]
fn try_opt_lin_cert_fallback(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    proof_path: &Path,
    temp_proof_path: &Path,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
    best_solution: &Mutex<Option<PbExactSolution>>,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Result<OptCertFallbackOutcome, String> {
    // The OPT-LIN-CERT helpers only handle single-literal (linear) objective
    // terms (also enforced by the eligibility gate).
    if objective.terms.iter().any(|term| term.lits.len() != 1) {
        return Ok(OptCertFallbackOutcome::Declined(None));
    }

    // Portfolio deadline leaves the certification reserve; the certify stop
    // closure below runs to the FULL timeout (absolute deadlines, so unused
    // portfolio time rolls into certification).
    let portfolio_timeout = timeout_dur.map(|timeout| {
        let remaining = timeout.saturating_sub(start.elapsed());
        timeout.saturating_sub(certify_reserve(remaining))
    });
    let portfolio_result = portfolio::solve_optimization_portfolio_with_timings(
        instance,
        objective,
        portfolio_timeout,
        start,
        term_flag,
        on_improve,
    );
    let timings = Some(portfolio_result.timings);
    let portfolio_solution = portfolio_result.solution;

    // Only a proven optimum is certifiable. Candidate WIDENING: check the
    // portfolio's own OptimumFound first (so an opt-in strict policy can never
    // narrow the candidate set), then try the checked optimum-upgrade gate.
    // Either way the candidate is only a CANDIDATE — the certification
    // helpers re-derive both bounds themselves.
    let candidate = if portfolio_solution.status == PbStatus::OptimumFound {
        portfolio_solution
    } else {
        let upgraded =
            portfolio::finalize_optimum_verdict(portfolio_solution, instance, objective, &|| {
                term_flag.load(Ordering::SeqCst)
                    || timeout_expired(timeout_dur, start)
                    || ay_sys::process_memory_exceeded()
            });
        if upgraded.status != PbStatus::OptimumFound {
            return Ok(OptCertFallbackOutcome::Declined(timings));
        }
        upgraded
    };
    let Some(optimum) = candidate.objective else {
        return Ok(OptCertFallbackOutcome::Declined(timings));
    };
    let incumbent = candidate.assignment;
    if incumbent.len() != instance.num_vars as usize {
        return Ok(OptCertFallbackOutcome::Declined(timings));
    }

    let should_stop = || {
        term_flag.load(Ordering::SeqCst)
            || timeout_expired(timeout_dur, start)
            || ay_sys::process_memory_exceeded()
    };

    // Compact lower bound first (broad coverage: augmented refutations needing
    // Sinz aux registers); fall back to the aux-free lift. Both are re-checked
    // by the competition's VeriPB checker.
    // Try the FAST direct CG-aggregation floor first (instant, no SAT refutation):
    // it certifies covering-tight optima whose augmented refutation the two routes
    // below cannot find in budget. Falls through when it does not apply.
    let pbp = ay_pb::proof::certify_opt_lin_trivial_zero_floor(instance, &incumbent, optimum)
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_knapsack_cardinality(instance, &incumbent, optimum)
        })
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_direct_aggregation_floor(instance, &incumbent, optimum)
        })
        .or_else(|| ay_pb::proof::certify_opt_lin_lp_dual_floor(instance, &incumbent, optimum))
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_bounds_compact_interruptible(
                instance,
                &incumbent,
                optimum,
                &should_stop,
            )
        })
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_bounds_interruptible(
                instance,
                &incumbent,
                optimum,
                &should_stop,
            )
        })
        .or_else(|| {
            // PB-NATIVE lower bound (aux-heavy gap): refute the augmented
            // instance with the proof-logging PB CDCL — no CNF encoding, so no
            // Sinz aux budget and no adder/BDD aux in the refutation. Last so
            // it can only ADD certificates the CNF routes decline.
            ay_pb::proof::certify_opt_lin_bounds_pb_interruptible(
                instance,
                &incumbent,
                optimum,
                &should_stop,
            )
        });
    let Some(pbp) = pbp else {
        return Ok(OptCertFallbackOutcome::Declined(timings));
    };

    fs::write(temp_proof_path, pbp.as_bytes())
        .map_err(|e| format!("failed to write proof '{}': {e}", temp_proof_path.display()))?;
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

    Ok(OptCertFallbackOutcome::Certified(Box::new(
        PbSolveOutcome {
            solution,
            pb_native_code_helper_applications: 0,
            portfolio_timings: timings,
        },
    )))
}

/// Certify an ALREADY-PROVEN optimum out-of-band and commit its VeriPB proof.
///
/// Used when native CDCL proof logging reached `OptimumFound` but could not
/// close its lower bound with a structural cut (`opt_lower_bound_deferred`): the
/// native proof file holds an unverifiable `rup >= 1 ;` and must be discarded.
/// Unlike [`try_opt_lin_cert_fallback`] this does NOT re-run the portfolio — the
/// optimum and a feasible model achieving it are already in `solution` — so it
/// spends the remaining budget only on assembling the certificate (compact Sinz
/// lower bound first, then the aux-free lift). Both routes are re-checked by the
/// competition's VeriPB checker before any CERTIFIED claim.
///
/// Returns `Ok(true)` iff a proof was produced and atomically committed.
/// `Ok(false)` (certificate withheld) leaves the caller fail-closed: it discards
/// the proof and reports the feasible incumbent rather than an uncertified
/// optimum.
fn commit_certified_known_optimum(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    solution: &PbSolution,
    proof_path: &Path,
    temp_proof_path: &Path,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
) -> Result<bool, String> {
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

    let should_stop = || {
        term_flag.load(Ordering::SeqCst)
            || timeout_expired(timeout_dur, start)
            || ay_sys::process_memory_exceeded()
    };

    let pbp = ay_pb::proof::certify_opt_lin_trivial_zero_floor(instance, incumbent, optimum)
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_knapsack_cardinality(instance, incumbent, optimum)
        })
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_direct_aggregation_floor(instance, incumbent, optimum)
        })
        .or_else(|| ay_pb::proof::certify_opt_lin_lp_dual_floor(instance, incumbent, optimum))
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_bounds_compact_interruptible(
                instance,
                incumbent,
                optimum,
                &should_stop,
            )
        })
        .or_else(|| {
            ay_pb::proof::certify_opt_lin_bounds_interruptible(
                instance,
                incumbent,
                optimum,
                &should_stop,
            )
        })
        .or_else(|| {
            // PB-NATIVE lower bound (aux-heavy gap): refute the augmented
            // instance with the proof-logging PB CDCL — no CNF encoding, so no
            // Sinz aux budget and no adder/BDD aux in the refutation. Last so
            // it can only ADD certificates the CNF routes decline.
            ay_pb::proof::certify_opt_lin_bounds_pb_interruptible(
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
        .map_err(|e| format!("failed to write proof '{}': {e}", temp_proof_path.display()))?;
    commit_or_remove_proof(proof_path, temp_proof_path, true)?;
    Ok(true)
}

fn solve_optimization_with_proof<W: Write>(
    instance: &PbInstance,
    objective: &ay_pb::PbObjective,
    proof_path: &Path,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
    collect_native_helper_applications: bool,
    out: &mut PbOutputWriter<W>,
    best_solution: &Mutex<Option<PbExactSolution>>,
) -> Result<PbSolveOutcome, String> {
    let temp_proof_path = prepare_proof_temp(proof_path)?;
    let split = compute_cert_opt_budget_split(instance, objective, timeout_dur, start);
    let native_deadline = Cell::new(split.native_deadline);
    let result = (|| {
        // PHASE N1: native proof-logging CDCL, capped at the split's slice
        // when the certified pipeline is eligible (fully uncapped otherwise —
        // today's behavior). The cap is a pure extra disjunct in the interrupt
        // predicates: it can only convert a would-be proof into a feasible
        // exit, never fabricate one.
        let proof_file = File::create(&temp_proof_path)
            .map_err(|e| format!("failed to create '{}': {e}", temp_proof_path.display()))?;
        let mut solver = PbCdclSolver::with_proof_writer_interruptible(
            instance,
            BufWriter::new(proof_file),
            || {
                term_flag.load(Ordering::SeqCst)
                    || timeout_expired(timeout_dur, start)
                    || native_cap_expired(&native_deadline)
            },
        )
        .map_err(|e| format!("failed to initialize proof writer: {e}"))?;
        solver.set_native_code_helper_validation_enabled(collect_native_helper_applications);

        // PROOF-TO-SCORE: stream every improving incumbent to STDOUT (never
        // into the VeriPB proof) and cache it, exactly like the plain
        // optimization path. A verified improvement also extends the native
        // slice (bounded by the hard ceiling) — progress earns time.
        let mut best_obj: Option<i128> = None;
        let mut streamed_best_obj: Option<i128> = None;
        let mut on_improve = |obj_value: i128, model: &[bool]| {
            if stream_verified_improvement(
                instance,
                objective,
                out,
                best_solution,
                &mut best_obj,
                &mut streamed_best_obj,
                obj_value,
                model,
            ) {
                extend_native_deadline(&native_deadline, &split);
            }
        };
        let result = solver.solve_optimize_interruptible(objective, Some(&mut on_improve), || {
            term_flag.load(Ordering::SeqCst)
                || timeout_expired(timeout_dur, start)
                || native_cap_expired(&native_deadline)
        });
        let mut helper_applications = solver.native_code_helper_applications();
        let solution = pb_cdcl_optimization_result_to_solution(result, instance.num_vars);
        if matches!(
            solution.status,
            PbStatus::OptimumFound | PbStatus::Satisfiable
        ) {
            // Route the phase-final model through the SAME verified dominance
            // bar as the streamed improvements: an unconditional cache write
            // here could replace a strictly better incumbent streamed by a
            // later phase's engine (each phase starts fresh), making the
            // flushed v line disagree with the last streamed o line.
            let _ = stream_verified_improvement(
                instance,
                objective,
                out,
                best_solution,
                &mut best_obj,
                &mut streamed_best_obj,
                solution.objective.unwrap_or(i128::MAX),
                &solution.assignment,
            );
        }

        if !matches!(
            solution.status,
            PbStatus::Unsatisfiable | PbStatus::OptimumFound
        ) {
            // Release the native proof-writer handle on the temp file so the
            // fallback (or the native tail) can overwrite it; the partial
            // native proof is unusable (it has no conclusion).
            drop(solver);
            let mut portfolio_timings = None;

            if split.eligible() {
                // PHASE P + C: portfolio (streaming through the same monotone
                // bar) + out-of-band certification.
                let mut fallback_on_improve = |obj_value: i128, model: &[bool]| {
                    let _ = stream_verified_improvement(
                        instance,
                        objective,
                        out,
                        best_solution,
                        &mut best_obj,
                        &mut streamed_best_obj,
                        obj_value,
                        model,
                    );
                };
                match try_opt_lin_cert_fallback(
                    instance,
                    objective,
                    proof_path,
                    &temp_proof_path,
                    timeout_dur,
                    start,
                    term_flag,
                    best_solution,
                    &mut fallback_on_improve,
                )? {
                    OptCertFallbackOutcome::Certified(outcome) => {
                        return Ok(PbSolveOutcome {
                            solution: final_optimization_result_after_anytime_stream(
                                outcome.solution,
                                streamed_best_obj,
                            ),
                            pb_native_code_helper_applications: helper_applications,
                            portfolio_timings: outcome.portfolio_timings,
                        });
                    }
                    OptCertFallbackOutcome::Declined(timings) => {
                        portfolio_timings = timings;
                    }
                }

                // PHASE N2: native tail with everything that remains. Its
                // primary job is the OPT-with-UNSAT-constraints class (the
                // portfolio's uncertified UNSAT cannot be emitted; the
                // natively-logged BOUNDS INF INF conclusion is the only
                // compliant proof source) — and strictly-additive insurance
                // elsewhere, since this time would otherwise be discarded.
                let tail_remaining = timeout_dur
                    .map(|timeout| timeout.saturating_sub(start.elapsed()))
                    .unwrap_or(Duration::ZERO);
                if tail_remaining >= Duration::from_millis(OPT_CERT_NATIVE_TAIL_MIN_MS) {
                    let proof_file = File::create(&temp_proof_path).map_err(|e| {
                        format!("failed to create '{}': {e}", temp_proof_path.display())
                    })?;
                    let mut tail_solver = PbCdclSolver::with_proof_writer_interruptible(
                        instance,
                        BufWriter::new(proof_file),
                        || term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, start),
                    )
                    .map_err(|e| format!("failed to initialize proof writer: {e}"))?;
                    tail_solver.set_native_code_helper_validation_enabled(
                        collect_native_helper_applications,
                    );
                    let mut tail_on_improve = |obj_value: i128, model: &[bool]| {
                        let _ = stream_verified_improvement(
                            instance,
                            objective,
                            out,
                            best_solution,
                            &mut best_obj,
                            &mut streamed_best_obj,
                            obj_value,
                            model,
                        );
                    };
                    let tail_result = tail_solver.solve_optimize_interruptible(
                        objective,
                        Some(&mut tail_on_improve),
                        || term_flag.load(Ordering::SeqCst) || timeout_expired(timeout_dur, start),
                    );
                    helper_applications += tail_solver.native_code_helper_applications();
                    let tail_solution =
                        pb_cdcl_optimization_result_to_solution(tail_result, instance.num_vars);
                    if matches!(
                        tail_solution.status,
                        PbStatus::OptimumFound | PbStatus::Satisfiable
                    ) {
                        // Same verified dominance bar as everywhere else: the
                        // tail engine starts fresh, so its final incumbent may
                        // be strictly worse than the portfolio's cached best —
                        // an unconditional cache write would corrupt the flush.
                        let _ = stream_verified_improvement(
                            instance,
                            objective,
                            out,
                            best_solution,
                            &mut best_obj,
                            &mut streamed_best_obj,
                            tail_solution.objective.unwrap_or(i128::MAX),
                            &tail_solution.assignment,
                        );
                    }
                    if matches!(
                        tail_solution.status,
                        PbStatus::Unsatisfiable | PbStatus::OptimumFound
                    ) {
                        // Same deferral guard as the primary native path: if the
                        // tail reached OptimumFound but could not close its lower
                        // bound structurally, its proof holds an unverifiable
                        // `rup >= 1 ;`. Re-certify the known optimum out-of-band;
                        // fail closed to the feasible incumbent otherwise.
                        if tail_solution.status == PbStatus::OptimumFound
                            && tail_solver.opt_lower_bound_deferred()
                        {
                            drop(tail_solver);
                            if commit_certified_known_optimum(
                                instance,
                                objective,
                                &tail_solution,
                                proof_path,
                                &temp_proof_path,
                                timeout_dur,
                                start,
                                term_flag,
                            )? {
                                return Ok(PbSolveOutcome {
                                    solution: final_optimization_result_after_anytime_stream(
                                        tail_solution,
                                        streamed_best_obj,
                                    ),
                                    pb_native_code_helper_applications: helper_applications,
                                    portfolio_timings,
                                });
                            }
                            cleanup_proof_temp(proof_path, &temp_proof_path);
                            return Ok(PbSolveOutcome {
                                solution: unknown_solution(),
                                pb_native_code_helper_applications: helper_applications,
                                portfolio_timings,
                            });
                        }

                        match tail_solver.conclude_proof() {
                            Ok(()) => {
                                commit_or_remove_proof(proof_path, &temp_proof_path, true)?;
                                return Ok(PbSolveOutcome {
                                    solution: final_optimization_result_after_anytime_stream(
                                        tail_solution,
                                        streamed_best_obj,
                                    ),
                                    pb_native_code_helper_applications: helper_applications,
                                    portfolio_timings,
                                });
                            }
                            Err(error) => {
                                // Withheld certificate: fall to the fail-closed
                                // exit just below (incumbents flushed as
                                // s SATISFIABLE) — never abort with no `s` line.
                                eprintln!(
                                    "warning: OPT tail proof finalization for '{}' \
                                     failed ({error}); failing closed",
                                    proof_path.display()
                                );
                            }
                        }
                    }
                }
            }

            // No optimality/UNSAT proof: discard the (incomplete) proof file so
            // no certificate is claimed, but KEEP the cached feasible
            // incumbents — write_result_or_best_known re-verifies the best one
            // at the emission boundary and flushes it as s SATISFIABLE.
            cleanup_proof_temp(proof_path, &temp_proof_path);
            return Ok(PbSolveOutcome {
                solution: unknown_solution(),
                pb_native_code_helper_applications: helper_applications,
                portfolio_timings,
            });
        }

        // Native CDCL reached OptimumFound but could not close its optimality
        // proof's lower bound with a structural cut (opt_lower_bound_deferred):
        // the native proof file holds an unverifiable `rup >= 1 ;` and MUST NOT
        // be committed. The optimum is correct, so re-certify it out-of-band from
        // the KNOWN optimum (no portfolio re-solve) via the OPT-LIN-CERT helpers,
        // whose RUP steps VeriPB accepts.
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

            // Certification withheld (out of budget / non-liftable refutation):
            // fail closed. Discard the proof and keep the cached feasible
            // incumbent — re-verified & flushed as s SATISFIABLE — never an
            // uncertified s OPTIMUM claim without a checkable proof.
            cleanup_proof_temp(proof_path, &temp_proof_path);
            return Ok(PbSolveOutcome {
                solution: unknown_solution(),
                pb_native_code_helper_applications: helper_applications,
                portfolio_timings: None,
            });
        }

        match solver.conclude_proof() {
            Ok(()) => {
                commit_or_remove_proof(proof_path, &temp_proof_path, true)?;

                Ok(PbSolveOutcome {
                    solution: final_optimization_result_after_anytime_stream(
                        solution,
                        streamed_best_obj,
                    ),
                    pb_native_code_helper_applications: helper_applications,
                    portfolio_timings: None,
                })
            }
            Err(error) => {
                // Withheld certificate on the native OPT conclusion: fail
                // closed exactly like the deferred-certification path above —
                // discard the proof, keep the cached feasible incumbent
                // (flushed as s SATISFIABLE) — never abort with no `s` line.
                eprintln!(
                    "warning: native OPT proof finalization for '{}' failed ({error}); \
                     failing closed",
                    proof_path.display()
                );
                cleanup_proof_temp(proof_path, &temp_proof_path);
                Ok(PbSolveOutcome {
                    solution: unknown_solution(),
                    pb_native_code_helper_applications: helper_applications,
                    portfolio_timings: None,
                })
            }
        }
    })();

    if result.is_err() {
        cleanup_proof_temp(proof_path, &temp_proof_path);
    }
    result
}

fn prepare_proof_temp(proof_path: &Path) -> Result<PathBuf, String> {
    clear_existing_proof(proof_path)?;
    let temp_proof_path = proof_temp_path(proof_path);
    let _ = fs::remove_file(&temp_proof_path);
    register_proof_temp_for_sigterm_cleanup(&temp_proof_path);
    Ok(temp_proof_path)
}

fn clear_existing_clique_conflict_row_import_map_sidecar(proof_path: &Path) -> Result<(), String> {
    clear_existing_proof(&clique_conflict_row_import_map_sidecar_path(proof_path))
}

fn clear_existing_proof(proof_path: &Path) -> Result<(), String> {
    match fs::remove_file(proof_path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "failed to remove '{}': {error}",
            proof_path.display()
        )),
    }
}

fn commit_or_remove_proof(
    proof_path: &Path,
    temp_proof_path: &Path,
    proof_complete: bool,
) -> Result<(), String> {
    if proof_complete {
        fs::rename(temp_proof_path, proof_path).map_err(|e| {
            format!(
                "failed to rename '{}' to '{}': {e}",
                temp_proof_path.display(),
                proof_path.display()
            )
        })?;
        unregister_proof_temp_for_sigterm_cleanup(temp_proof_path);
    } else {
        cleanup_proof_temp(proof_path, temp_proof_path);
    }
    Ok(())
}

fn cleanup_proof_temp(proof_path: &Path, temp_proof_path: &Path) {
    let _ = fs::remove_file(temp_proof_path);
    let _ = fs::remove_file(proof_path);
    let _ = fs::remove_file(clique_conflict_row_import_map_sidecar_path(proof_path));
    unregister_proof_temp_for_sigterm_cleanup(temp_proof_path);
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

/// DECISION-SAT Verified-SAT-Gate (VSG) — the decision-track analogue of the
/// optimization incumbent VIG (`sanitize_optimization_incumbent`,
/// crates/ay-pb/src/portfolio.rs), ported verbatim from `crates/ay/src/cmd_pb.rs`
/// so the competition binary carries the same fail-closed gate. The core CDCL
/// solver's model reaches `pb_cdcl_result_to_solution` and is mapped DIRECTLY to
/// `PbStatus::Satisfiable` with no re-check, so a would-be `s SATISFIABLE`
/// verdict otherwise TRUSTS the core solver's model. This gate re-verifies that
/// model against the ORIGINAL `instance.constraints` with the proven
/// `ay_pb::verify_all_constraints` before the verdict can be emitted.
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
    if let Ok(target_len) = usize::try_from(num_pb_vars) {
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

/// FAIL-CLOSED exact objective recompute (design §3.2): the producer's claimed
/// value is always discarded and the objective is recomputed exactly in i128
/// from the model. Returns `None` on true i128 term-sum overflow, in which case
/// the caller must SKIP/withhold the objective (and any incumbent keyed on it)
/// rather than fall back to a legacy or saturated value.
fn exact_objective_fail_closed(objective: &ay_pb::PbObjective, model: &[bool]) -> Option<i128> {
    eval_objective_exact(objective, model).ok()
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
    // Mirror every streamed feasible incumbent into the process-global
    // emergency-flush store so a later panic can still emit it (see
    // `EmergencyIncumbent`). The store is armed only for OPB, so this is a no-op
    // for WBO; the assignment is in the original variable space at every call
    // site, matching the constraints recorded at arm time.
    if matches!(
        solution.status,
        PbStatus::Satisfiable | PbStatus::OptimumFound
    ) {
        record_emergency_incumbent(&solution.assignment);
        // Diagnostic-only: inject a panic right after recording an incumbent to
        // exercise the panic-time emergency flush end-to-end. Compiled OUT of
        // release builds (zero production cost) and inert unless the env var is
        // set; used by the proof-to-score verification harness.
        #[cfg(debug_assertions)]
        assert!(
            std::env::var_os("AY_PB_DEBUG_PANIC_ON_INCUMBENT").is_none(),
            "AY_PB_DEBUG_PANIC_ON_INCUMBENT: injected panic after recording incumbent"
        );
    }
    let mut guard = best_solution
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *guard = Some(solution);
}

fn write_result_or_best_known<W: Write>(
    out: &mut PbOutputWriter<W>,
    result: &PbSolution,
    best_solution: &Mutex<Option<PbExactSolution>>,
    vig_constraints: Option<&[ay_pb::PbConstraint]>,
) -> io::Result<PbStatus> {
    // Test-only fault injection: stall before the final write so the SIGTERM
    // flush watchdog's forced-flush path can be exercised end-to-end.
    // Compiled OUT of release builds (zero production cost).
    #[cfg(debug_assertions)]
    if let Some(ms) = trimmed_env_value("AY_PB_TEST_STALL_BEFORE_RESULT_MS")
        .and_then(|value| value.parse::<u64>().ok())
    {
        std::thread::sleep(Duration::from_millis(ms));
    }
    // PROOF-TO-SCORE: whenever the final result is UNKNOWN — a timeout, a SIGTERM,
    // or any path that found a feasible model via the anytime callback but could
    // not prove a verdict — flush the best feasible incumbent instead of
    // withholding it. The incumbent is feasible by construction (every cache site
    // re-checks it with `verify_all_constraints`), and below we re-check it once
    // more at the emission boundary against the ORIGINAL constraints, so this is
    // SOUND: it reports `SATISFIABLE` for a model the VIG accepts and NEVER claims
    // OPTIMUM. The `o` line for this incumbent was already streamed during the
    // anytime search, so we drop the objective here to avoid a duplicate `o` line;
    // the checker recomputes the cost from the witness regardless. If no incumbent
    // exists (or it fails the boundary VIG), `best_known_or_unknown` /
    // `unknown_exact_solution` yields a plain `s UNKNOWN`.
    //
    // Previously the flush was gated on a SIGTERM being requested, so a plain
    // timeout (the common competition case) discarded a perfectly good feasible
    // incumbent and emitted `s UNKNOWN`, leaving sound-correct credit on the table.
    let emitted = if result.status == PbStatus::Unknown {
        let best_known = best_known_or_unknown(best_solution);
        match best_known.status {
            // Flush a feasible anytime incumbent as SATISFIABLE. We are NOT
            // re-deriving the optimum gate here, so a cached `OptimumFound` is
            // downgraded to `Satisfiable` for emission — this path never claims
            // OPTIMUM. Re-check the witness at the emission boundary against the
            // ORIGINAL constraints (belt-and-suspenders over the producing-layer
            // VIG); fail closed to UNKNOWN if it does not verify.
            PbStatus::Satisfiable | PbStatus::OptimumFound => {
                let feasible = vig_constraints.is_none_or(|constraints| {
                    ay_pb::verify_all_constraints(constraints, &best_known.assignment)
                });
                if feasible {
                    PbExactSolution {
                        status: PbStatus::Satisfiable,
                        assignment: best_known.assignment,
                        objective: None,
                    }
                } else {
                    unknown_exact_solution()
                }
            }
            _ => unknown_exact_solution(),
        }
    } else {
        result.to_exact_solution()
    }
    .normalized_for_competition();
    let status = emitted.status;
    // Claim the emission slot BEFORE the first byte (see
    // [`claim_cooperative_emission`]): if the SIGTERM watchdog won the claim
    // it owns stdout and this process is exiting imminently — cede to it
    // completely. Returning would let the caller keep emitting (c-lines,
    // stats) into the watchdog's raw flush and race it to `process::exit`
    // with a different exit code; parking guarantees the watchdog's emission
    // is the process's last words.
    if !claim_cooperative_emission() {
        loop {
            std::thread::park();
        }
    }
    out.write_full_result_exact(&emitted)?;
    Ok(status)
}

fn best_known_or_unknown(best_solution: &Mutex<Option<PbExactSolution>>) -> PbExactSolution {
    best_solution
        .lock()
        .map(|guard| guard.clone())
        .unwrap_or_else(|poisoned| poisoned.into_inner().clone())
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

fn timeout_expired(timeout: Option<Duration>, start: Instant) -> bool {
    timeout.is_some_and(|dur| start.elapsed() >= dur) || cpu_budget_expired()
}

/// Optional process-CPU budget from `AY_PB_CPU_BUDGET_MS`.
///
/// PB-COMP's TIMELIMIT is TOTAL CPU time across all threads (enforced by
/// runsolver), while `--timeout` is wall time. Whenever an auxiliary thread is
/// busy (the proof-tap serializer at ~1.3x total CPU on DEC-CERT, helper
/// workers elsewhere), CPU accrues faster than wall, and runsolver's SIGTERM
/// lands BEFORE the solver's own wall deadline — past the point of an orderly
/// fail-closed wind-down (worst case: mid-proof). With this budget set (the
/// generated competition run.sh derives it from TIMELIMIT minus a flush
/// margin), every deadline poll also consults the process CPU clock, so the
/// solver stands down on whichever clock — wall or CPU — runs out first.
fn cpu_budget() -> Option<Duration> {
    static BUDGET: std::sync::OnceLock<Option<Duration>> = std::sync::OnceLock::new();
    *BUDGET.get_or_init(|| {
        trimmed_env_value("AY_PB_CPU_BUDGET_MS")
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|&ms| ms > 0)
            .map(Duration::from_millis)
    })
}

fn cpu_budget_expired() -> bool {
    // Sample the (syscall-priced) CPU clock on every 32nd poll: deadline polls
    // can sit on per-conflict paths, and a budget miss of 31 polls is well
    // inside the flush margin the budget already reserves.
    static POLL_TICK: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    let Some(budget) = cpu_budget() else {
        return false;
    };
    if !POLL_TICK.fetch_add(1, Ordering::Relaxed).is_multiple_of(32) {
        return false;
    }
    process_cpu_time().is_some_and(|cpu| cpu >= budget)
}

/// Total process CPU time (user + system, all threads) via `getrusage`.
#[cfg(unix)]
fn process_cpu_time() -> Option<Duration> {
    // SAFETY: `getrusage(RUSAGE_SELF, ..)` fills the zeroed out-param and
    // returns non-zero on failure; no pointer outlives the call.
    let usage = unsafe {
        let mut usage: libc::rusage = std::mem::zeroed();
        if libc::getrusage(libc::RUSAGE_SELF, &raw mut usage) != 0 {
            return None;
        }
        usage
    };
    let seconds = u64::try_from(usage.ru_utime.tv_sec)
        .ok()?
        .checked_add(u64::try_from(usage.ru_stime.tv_sec).ok()?)?;
    let micros = u64::try_from(usage.ru_utime.tv_usec)
        .ok()?
        .checked_add(u64::try_from(usage.ru_stime.tv_usec).ok()?)?;
    Some(Duration::from_secs(seconds) + Duration::from_micros(micros))
}

/// Non-Unix (dev-only) build: no CPU accounting; the wall deadline stands.
#[cfg(not(unix))]
fn process_cpu_time() -> Option<Duration> {
    None
}

fn periodic_stop_check(
    term_flag: &AtomicBool,
    timeout_dur: Option<Duration>,
    start: Instant,
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
        // Memory is part of the stop signal: parsing/loading a huge input past
        // the competition MEMLIMIT would end in a SIGKILL with no s line, so
        // bail to the clean Interrupted -> s UNKNOWN path instead. No-op when
        // no limit is configured.
        term_flag.load(Ordering::SeqCst)
            || timeout_expired(timeout_dur, start)
            || ay_sys::process_memory_exceeded()
    }
}

fn read_file_interruptible<F>(path: &Path, should_stop: &mut F) -> io::Result<Option<Vec<u8>>>
where
    F: FnMut() -> bool,
{
    let mut file = File::open(path)?;
    let capacity_hint = file
        .metadata()
        .ok()
        .and_then(|metadata| usize::try_from(metadata.len()).ok())
        .unwrap_or(0);
    let mut bytes = Vec::with_capacity(capacity_hint);
    let mut chunk = vec![0_u8; 64 * 1024];
    loop {
        if should_stop() {
            return Ok(None);
        }
        let read = file.read(&mut chunk)?;
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
) -> Result<ParsedPbInstance, ay_pb::ParseError>
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
    /// OPB instances are held behind an `Arc` (mirroring the main `ay` CLI's
    /// `cmd_pb` shape) so the parallel portfolio and the NLC frontend-timeout
    /// watchdog can hand worker threads shared ownership of the rows instead
    /// of deep-copying them (~0.3s per copy at 6.4M rows, measured on
    /// lopes-172). The rows are immutable after parse (every solve path takes
    /// `&PbInstance`), so sharing cannot change any verdict.
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

    fn declared_or_actual_constraint_count(&self) -> usize {
        match self {
            Self::Opb(instance) => usize::try_from(instance.num_constraints)
                .unwrap_or(usize::MAX)
                .max(instance.constraints.len()),
            Self::Wbo(_) => self.constraint_count(),
        }
    }

    fn is_optimization(&self) -> bool {
        match self {
            Self::Opb(instance) => instance.objective.is_some(),
            Self::Wbo(_) => true,
        }
    }

    /// The ORIGINAL PB constraints a recovered incumbent must satisfy, for the
    /// emission-boundary Verified Incumbent Gate (VIG) re-check.
    ///
    /// For OPB the cached incumbent assignment is in the original variable space
    /// (every producing layer projects to `instance.num_vars` and verifies with
    /// `verify_all_constraints`), so these are exactly the rows to re-check.
    /// For WBO the incumbent objective/feasibility is defined over the
    /// soft/hard-split projection rather than a single `Vec<PbConstraint>`, so we
    /// return `None` and rely on the producing-layer verification that already
    /// re-checks every WBO incumbent before it is cached.
    fn vig_constraints(&self) -> Option<&[ay_pb::PbConstraint]> {
        match self {
            Self::Opb(instance) => Some(&instance.constraints),
            Self::Wbo(_) => None,
        }
    }
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
    should_skip_startup_jit_telemetry_shape(
        instance.num_vars(),
        instance.declared_or_actual_constraint_count(),
        instance.is_optimization(),
        timeout_ms,
    )
}

fn should_skip_startup_jit_telemetry_shape(
    num_vars: u32,
    constraint_count: usize,
    is_optimization: bool,
    timeout_ms: Option<u64>,
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

fn emit_pb_json_stats(
    stats_json: bool,
    solve_start: Instant,
    status: PbStatus,
    telemetry: Option<&PbJitCandidateTelemetry>,
) {
    emit_pb_json_stats_with_portfolio(stats_json, solve_start, status, telemetry, None);
}

fn emit_pb_json_stats_with_portfolio(
    stats_json: bool,
    solve_start: Instant,
    status: PbStatus,
    telemetry: Option<&PbJitCandidateTelemetry>,
    portfolio_timings: Option<&portfolio::PbPortfolioPhaseTimings>,
) {
    if !stats_json {
        return;
    }
    let build = pb_stats_build_metadata();
    let pb_pbo_candidate_applications =
        telemetry.map_or(0, |telemetry| telemetry.pb_pbo_candidate_applications);
    let pb_native_code_helper_applications =
        telemetry.map_or(0, |telemetry| telemetry.pb_native_code_helper_applications);
    let competition_jit = pb_competition_jit_metadata(
        pb_pbo_candidate_applications,
        pb_native_code_helper_applications,
    );
    let mut json = format!(
        "{{\"mode\":\"pb\",\"result\":{},\"wall_time_ms\":{},\"ay_build\":{},\"competition_jit\":{},\"pb_pbo_candidate_applications\":{},\"pb_native_code_helper_applications\":{}",
        json_string(pb_status_stats_result(status)),
        elapsed_wall_time_ms(solve_start),
        build.json_object(),
        competition_jit.json_object(),
        pb_pbo_candidate_applications,
        pb_native_code_helper_applications
    );
    if let Some(timings) = portfolio_timings {
        for (key, value) in timings.stats_fields() {
            json.push_str(&format!(",\"{key}\":{value}"));
        }
    }
    json.push('}');
    eprintln!("{json}");
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

/// Returns whether the *unconditional* instance-level symmetry-breaking pass
/// (augment `search_instance` up front, regardless of instance shape) is enabled.
///
/// This eager mode is **off by default** — it can mildly slow easy SAT instances
/// (extra propagation overhead with no payoff). It is opt-in via `AY_PB_SYMMETRY`
/// (truthy: `1`, `on`, `true`, `lex`, `yes`) for differential harnesses and
/// experiments. The default-on, no-regression path is the *shape-gated symmetry
/// arm* (`symmetry_arm_enabled`), which only acts on large highly-symmetric
/// instances and only AFTER a normal-solve probe fails to decide them.
fn symmetry_breaking_enabled() -> bool {
    matches!(
        trimmed_env_value("AY_PB_SYMMETRY")
            .map(|v| v.to_ascii_lowercase())
            .as_deref(),
        Some("1" | "on" | "true" | "lex" | "yes")
    )
}

/// Returns whether the shape-gated symmetry *arm* (probe-then-augment for large
/// highly-symmetric decision instances) is enabled. **On by default**; set
/// `AY_PB_SYMMETRY_ARM=0|off|false|no` to disable. It never touches an instance
/// that fails the cheap structural gate, and never adds overhead to an instance
/// the normal probe already decides, so it is no-regression on the broad corpus.
fn symmetry_arm_enabled() -> bool {
    !matches!(
        trimmed_env_value("AY_PB_SYMMETRY_ARM")
            .map(|v| v.to_ascii_lowercase())
            .as_deref(),
        Some("0" | "off" | "false" | "no")
    )
}

/// Returns whether the shape-gated clique witness *arm* (parallel clique local search
/// for mgd-FRB / Model RB decision instances) is enabled. **On by default**; set
/// `AY_PB_CLIQUE_ARM=0|off|false|no` to disable. It refuses (no-op) any instance lacking
/// the mgd-FRB fingerprint, and only ever emits a SAT witness verified against the
/// original PB constraints, so it is sound and no-regression on the broad corpus.
fn clique_arm_enabled() -> bool {
    !matches!(
        trimmed_env_value("AY_PB_CLIQUE_ARM")
            .map(|v| v.to_ascii_lowercase())
            .as_deref(),
        Some("0" | "off" | "false" | "no")
    )
}

/// Returns whether the certified-optimization portfolio fallback (budget-split
/// native slice -> portfolio -> out-of-band certification -> native tail) is
/// enabled in proof mode. **On by default**; set
/// `AY_PB_OPT_CERT_PORTFOLIO=0|off|false|no` to restore the native-only
/// full-budget behavior.
fn opt_cert_portfolio_enabled() -> bool {
    !matches!(
        trimmed_env_value("AY_PB_OPT_CERT_PORTFOLIO")
            .map(|v| v.to_ascii_lowercase())
            .as_deref(),
        Some("0" | "off" | "false" | "no")
    )
}

/// Test/tuning override for the certified-optimization native slice: pins the
/// initial slice AND the hard ceiling to this many milliseconds with no
/// improvement grace. Soundness-free — it only moves the interrupt point.
fn cert_native_cap_ms_override() -> Option<u64> {
    trimmed_env_value("AY_PB_CERT_NATIVE_CAP_MS")?.parse().ok()
}

/// Probe budget (fraction of the total decision timeout) given to the NORMAL
/// solver before the symmetry arm engages. Easy instances decide well within
/// this; hard symmetric ones spend the remainder on the augmented solve.
const SYMMETRY_PROBE_TIMEOUT_NUM: u32 = 1;
const SYMMETRY_PROBE_TIMEOUT_DEN: u32 = 6;

/// Minimum probe time (ms) so a tiny overall timeout still gives the normal arm a
/// fair shot before symmetry detection.
const SYMMETRY_PROBE_MIN_MS: u64 = 2_000;

/// Maximum probe time (ms). The probe is `total/6` but capped here so a long
/// budget does not waste a large absolute slice probing instances the normal
/// portfolio cannot decide (the highly-symmetric "mat" family); detection + the
/// augmented solve get the rest. Easy instances decide far inside this cap.
const SYMMETRY_PROBE_MAX_MS: u64 = 10_000;

/// Cap (ms) on the symmetry *detection* pass so it cannot consume the whole
/// remaining budget; the augmented solve gets the rest. Detection time scales
/// with the verified generators it harvests; on the long competition timeouts
/// this generous cap lets it gather a strong generating set for the largest
/// matrix instances, while the reservation below still guarantees the augmented
/// solve a solid slice of what is left.
const SYMMETRY_DETECT_MAX_MS: u64 = 600_000;

/// Fraction (NUM/DEN) of the remaining budget given to symmetry DETECTION (the
/// augmented solve gets the rest). Detection — individualise-refine over hundreds
/// of thousands of constraints — is the slow part on the largest matrices, while
/// the augmented solve is fast once a strong generating set is found, so detection
/// gets the larger share.
const SYMMETRY_DETECT_NUM: u64 = 3;
const SYMMETRY_DETECT_DEN: u64 = 5;

/// Conditionally augments a *linear* PB instance with sound lex-leader symmetry
/// breaking constraints for fully interchangeable variables.
///
/// Returns the augmented instance only when (1) the trigger is enabled, (2) the
/// instance is linear, and (3) at least one lex constraint was added. Otherwise
/// returns `None` and the caller solves the original instance. The augmented
/// instance is equisatisfiable with the input and has the same optimum (see the
/// `ay_pb::symmetry` module soundness argument), so no verdict can change.
///
/// This is only ever called on the non-proof solve path; certified proofs are
/// produced from the original constraints and never see added rows.
fn maybe_break_symmetries(instance: &PbInstance) -> Option<PbInstance> {
    if !symmetry_breaking_enabled() || !is_linear(instance) {
        return None;
    }
    let (augmented, result) = break_symmetries(instance);
    if result.changed_instance() {
        Some(augmented)
    } else {
        None
    }
}

/// Shape-gated symmetry arm for decision instances (no objective).
///
/// Sequence (no regression by construction):
///   1. Cheap structural gate: only large, highly-symmetric (templated/matrix)
///      instances proceed. Everything else returns `None` immediately (the
///      caller runs the normal portfolio).
///   2. PROBE: run the normal decision portfolio for a short slice of the budget.
///      Easy instances (e.g. satisfiable mat siblings) decide here and are
///      returned with NO symmetry overhead.
///   3. DETECT + AUGMENT: if the probe did not decide, detect a generating set of
///      EXACTLY-VERIFIED automorphisms (bounded by a detection deadline), append
///      sound lex-leader rows, and solve the augmented instance for the remaining
///      time. This converts otherwise-undecidable hard symmetric instances.
///
/// Returns `Some(solution)` when this arm produces a verdict (or a best effort on
/// timeout); `None` to defer to the normal portfolio (gate failed, or detection
/// found nothing). Soundness: every emitted row comes from a verified generator,
/// so the augmented instance is equisatisfiable with the original.
fn try_symmetry_decision(
    instance: &PbInstance,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
) -> Option<PbSolution> {
    if !is_linear(instance) || !is_highly_symmetric_candidate(instance) {
        return None;
    }

    // (2) Probe with the normal portfolio for a short slice of the budget.
    let probe_deadline = timeout_dur.map(|total| {
        let total_ms = total.as_millis() as u64;
        // The MAX cap keeps the probe at a modest absolute time: easy
        // symmetric-looking instances decide well within this, while the
        // highly-symmetric "mat" family (which the normal portfolio never
        // decides in the probe) reaches symmetry detection + the augmented
        // solve sooner instead of burning a large fraction of a long budget
        // on a probe that cannot succeed.
        let slice = (total_ms * u64::from(SYMMETRY_PROBE_TIMEOUT_NUM)
            / u64::from(SYMMETRY_PROBE_TIMEOUT_DEN))
        .clamp(SYMMETRY_PROBE_MIN_MS, SYMMETRY_PROBE_MAX_MS)
        .min(total_ms);
        start + Duration::from_millis(slice)
    });
    let probe_timeout = probe_deadline.map(|d| d.saturating_duration_since(start));
    let probe =
        portfolio::solve_decision_portfolio_with_timings(instance, probe_timeout, start, term_flag);
    if matches!(
        probe.solution.status,
        PbStatus::Satisfiable | PbStatus::Unsatisfiable
    ) {
        return Some(probe.solution);
    }
    if term_flag.load(Ordering::Relaxed) {
        return Some(probe.solution);
    }

    // (3) Detect symmetry with a bounded detection deadline, then solve augmented.
    let now = Instant::now();
    let remaining = timeout_dur.map(|total| (start + total).saturating_duration_since(now));
    // Split the remaining budget between detection and the augmented solve. The
    // augmented solve on the highly-symmetric matrix family is FAST once a strong
    // generating set is in hand (seconds), while gathering that set (individualise-
    // refine on hundreds of thousands of constraints) is the slow part on the
    // largest instances (mat20). So bias the split toward detection (NUM/DEN of
    // what is left) while still reserving the rest for the solve.
    let detect_budget_ms = remaining
        .map(|r| {
            let r = r.as_millis() as u64;
            (r * SYMMETRY_DETECT_NUM / SYMMETRY_DETECT_DEN).min(SYMMETRY_DETECT_MAX_MS)
        })
        .unwrap_or(SYMMETRY_DETECT_MAX_MS);
    let detect_deadline = Some(now + Duration::from_millis(detect_budget_ms));
    let (augmented, result) = break_symmetries_with_deadline(instance, detect_deadline);
    if !result.changed_instance() {
        return None; // no generators found -> defer to the normal portfolio
    }

    // Solve the augmented instance for the remaining time. The augmented instance
    // has the SAME variables (only added rows), so any model projects directly.
    let aug_result =
        portfolio::solve_decision_portfolio_with_timings(&augmented, timeout_dur, start, term_flag);
    // The augmented instance adds no variables; project the assignment back to the
    // original variable count for output safety.
    Some(project_solution_assignment(
        aug_result.solution,
        instance.num_vars,
    ))
}

fn pb_competition_jit_metadata(
    pb_pbo_candidate_applications: u64,
    pb_native_code_helper_applications: u64,
) -> PbCompetitionJitMetadata {
    let requested = trimmed_env_value("AY_COMPETITION_JIT_MODE");
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

    match requested.as_deref() {
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
    fn json_object(&self) -> String {
        format!(
            "{{\"schema_version\":1,\"track\":\"pb\",\"artifact\":{},\"application_counter\":{},\"requested_mode\":{},\"candidate_mode\":{},\"native_dispatch\":{},\"fail_closed\":{}}}",
            json_string(self.artifact),
            json_string(self.application_counter),
            json_string(&self.requested_mode),
            json_string(self.candidate_mode),
            self.native_dispatch,
            self.fail_closed
        )
    }
}

#[derive(Debug, Clone, Copy)]
struct PbStatsBuildMetadata {
    version: &'static str,
    commit: &'static str,
    datetime_utc: &'static str,
    stamp: &'static str,
}

impl PbStatsBuildMetadata {
    fn json_object(self) -> String {
        format!(
            "{{\"version\":{},\"commit\":{},\"datetime_utc\":{},\"stamp\":{}}}",
            json_string(self.version),
            json_string(self.commit),
            json_string(self.datetime_utc),
            json_string(self.stamp)
        )
    }
}

fn pb_stats_build_metadata() -> PbStatsBuildMetadata {
    PbStatsBuildMetadata {
        version: env!("CARGO_PKG_VERSION"),
        commit: option_env!("AY_BUILD_COMMIT").unwrap_or("unknown"),
        datetime_utc: option_env!("AY_BUILD_DATETIME_UTC").unwrap_or("unknown"),
        stamp: option_env!("AY_BUILD_STAMP")
            .unwrap_or(concat!(env!("CARGO_PKG_VERSION"), "+pb-static")),
    }
}

fn elapsed_wall_time_ms(solve_start: Instant) -> u64 {
    u64::try_from(solve_start.elapsed().as_millis()).unwrap_or(u64::MAX)
}

fn json_string(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len() + 2);
    escaped.push('"');
    for ch in value.chars() {
        match ch {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            ch if ch.is_control() => {
                use std::fmt::Write as _;

                let _ = write!(escaped, "\\u{:04x}", ch as u32);
            }
            ch => escaped.push(ch),
        }
    }
    escaped.push('"');
    escaped
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

fn pb_exit_code(status: PbStatus) -> i32 {
    match status {
        PbStatus::Satisfiable => 10,
        PbStatus::Unsatisfiable => 20,
        PbStatus::OptimumFound => 30,
        PbStatus::Unknown | PbStatus::Unsupported => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // The one workspace env choke point: serialized, restore-on-exit env
    // mutation (unifies the former CERT_ENV_LOCK onto it).
    use ay_test_support::env::{lock_env, ScopedEnvVar};
    use std::fs;

    #[test]
    fn test_stats_telemetry_skip_includes_testscheduling_t030_scale() {
        assert!(should_skip_startup_jit_telemetry_shape(
            993_048,
            1_964_067,
            true,
            Some(5_000)
        ));
        assert!(!should_skip_startup_jit_telemetry_shape(
            899_999,
            1_964_067,
            true,
            Some(5_000)
        ));
        assert!(!should_skip_startup_jit_telemetry_shape(
            993_048,
            999_999,
            true,
            Some(5_000)
        ));
        assert!(!should_skip_startup_jit_telemetry_shape(
            993_048,
            1_964_067,
            true,
            Some(5_001)
        ));
        assert!(!should_skip_startup_jit_telemetry_shape(
            993_048,
            1_964_067,
            false,
            Some(5_000)
        ));
    }

    #[test]
    fn test_stats_telemetry_skip_uses_declared_opb_scale() {
        let instance = ParsedPbInstance::Opb(Arc::new(PbInstance {
            num_vars: 2_530_390,
            num_constraints: 5_076_483,
            constraints: Vec::new(),
            objective: Some(ay_pb::PbObjective { terms: Vec::new() }),
        }));

        assert_eq!(instance.constraint_count(), 0);
        assert_eq!(instance.declared_or_actual_constraint_count(), 5_076_483);
        assert!(should_skip_startup_jit_telemetry(&instance, Some(5_000)));
    }

    fn unique_temp_path(stem: &str, ext: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after Unix epoch")
            .as_nanos();
        std::env::temp_dir().join(format!("ay-pb-{stem}-{}-{nanos}.{ext}", std::process::id()))
    }

    fn write_temp_pb(stem: &str, ext: &str, input: &str) -> PathBuf {
        let path = unique_temp_path(stem, ext);
        fs::write(&path, input).expect("temporary PB fixture should be writable");
        path
    }

    fn remove_temp_files(paths: &[&Path]) {
        for path in paths {
            let _ = fs::remove_file(path);
        }
    }

    #[test]
    fn test_read_file_interruptible_stops_after_eof_poll() {
        let path = write_temp_pb("interruptible-eof-window", "opb", "");
        let mut polls = 0;

        let result = read_file_interruptible(&path, &mut || {
            polls += 1;
            polls >= 2
        })
        .expect("file read should not fail");
        remove_temp_files(&[&path]);

        assert!(
            result.is_none(),
            "EOF-window stop poll should interrupt before returning bytes"
        );
        assert_eq!(polls, 2, "expected pre-read and post-EOF stop polls");
    }

    #[test]
    fn test_proof_mode_less_equal_opb_optimization_without_native_certifies_bounds() {
        let file_path = write_temp_pb(
            "proof-mode-less-equal-opb-opt",
            "opb",
            concat!(
                "* #variable= 2 #constraint= 2\n",
                "min: +1 x1 +2 x2 ;\n",
                "+1 x1 +1 x2 <= 1 ;\n",
                "+1 x1 +1 x2 >= 1 ;\n",
            ),
        );
        let proof_path = unique_temp_path("proof-mode-less-equal-opb-opt", "pbp");
        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: Some(proof_path.clone()),
            stats: false,
            stats_json: false,
            native: false,
        };

        let status = run_solve(&cmd).expect("linear OPB optimization proof should solve");
        let proof = fs::read_to_string(&proof_path)
            .expect("linear OPB optimization proof should be committed");
        remove_temp_files(&[&file_path, &proof_path]);

        assert_eq!(status, PbStatus::OptimumFound);
        assert!(
            proof.lines().any(|line| line == "output NONE;"),
            "optimization proof should contain VeriPB output marker: {proof}"
        );
        // Hinted conclusion form (`conclusion BOUNDS 1 : <id> 1 : <witness>;`):
        // the hints keep the conclusion verifiable in unchecked-deletion mode,
        // where soli-logged solutions are discounted by the checker.
        assert!(
            proof
                .lines()
                .any(|line| line.starts_with("conclusion BOUNDS 1 : ")
                    && line.contains(" 1 : ")
                    && line.ends_with(';')),
            "optimization proof should conclude hinted certified optimum bounds: {proof}"
        );
        assert_eq!(
            proof.lines().last(),
            Some("end pseudo-Boolean proof;"),
            "optimization proof should end with VeriPB terminator: {proof}"
        );
    }

    #[test]
    fn proof_mode_optimization_interruption_fails_closed_without_sidecar() {
        let instance = ay_pb::parse_opb(concat!(
            "* #variable= 2 #constraint= 1\n",
            "min: +1 x1 +1 x2 ;\n",
            "+1 x1 +1 x2 >= 1 ;\n",
        ))
        .expect("optimization fixture should parse");
        let proof_path = unique_temp_path("proof-mode-opt-interrupt", "pbp");
        let sidecar_path = clique_conflict_row_import_map_sidecar_path(&proof_path);
        fs::write(&proof_path, "stale proof").expect("stale proof path should be writable");
        fs::write(&sidecar_path, "stale conflict row map")
            .expect("stale conflict-row sidecar should be writable");
        let term_flag = AtomicBool::new(true);
        let best_solution = Mutex::new(Some(PbExactSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(1),
        }));
        let mut output = Vec::new();

        let outcome = {
            let mut out = PbOutputWriter::new(&mut output);
            solve_pb(
                &ParsedPbInstance::Opb(Arc::new(instance)),
                Some(&proof_path),
                Some(Duration::from_secs(5)),
                Instant::now(),
                false,
                false,
                &term_flag,
                &mut out,
                &best_solution,
                None,
            )
            .expect("proof-mode interrupted optimization should fail closed cleanly")
        };

        assert_eq!(outcome.solution.status, PbStatus::Unknown);
        assert!(outcome.solution.assignment.is_empty());
        assert!(outcome.solution.objective.is_none());
        assert!(
            !proof_path.exists(),
            "incomplete proof sidecar must be removed"
        );
        assert!(
            !sidecar_path.exists(),
            "incomplete proof cleanup must remove stale conflict-row sidecars"
        );
        assert!(
            output.is_empty(),
            "solve_pb should not emit stale incumbent output directly"
        );
        assert!(
            best_solution
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .is_none(),
            "incomplete proof-mode optimization must clear cached incumbents"
        );

        let mut out = PbOutputWriter::new(&mut output);
        let status = write_result_or_best_known(&mut out, &outcome.solution, &best_solution, None)
            .expect("unknown result should render");
        let rendered = String::from_utf8(output).expect("output should be utf-8");
        remove_temp_files(&[&proof_path, &sidecar_path]);

        assert_eq!(status, PbStatus::Unknown);
        assert_eq!(rendered, "s UNKNOWN\n");
        assert!(!rendered.contains("o "));
        assert!(!rendered.contains("v "));
    }

    #[test]
    fn proof_mode_expired_start_wbo_returns_unknown_before_unsupported() {
        let input = concat!("soft: 10 ;\n", "+1 x1 +1 x2 <= 1 ;\n", "[4] +1 x1 <= 0 ;\n",);
        let ParsedPbInstance::Wbo(wbo) =
            parse_instance_interruptible(PbInputFormat::Wbo, input, || false)
                .expect("WBO fixture should parse")
        else {
            panic!("expected WBO fixture");
        };
        let proof_path = unique_temp_path("proof-mode-expired-start-wbo", "pbp");
        let sidecar_path = clique_conflict_row_import_map_sidecar_path(&proof_path);
        fs::write(&proof_path, "stale proof").expect("stale proof path should be writable");
        fs::write(&sidecar_path, "stale sidecar").expect("stale proof sidecar should be writable");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(Some(PbExactSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(4),
        }));
        let mut output = Vec::new();

        let outcome = {
            let mut out = PbOutputWriter::new(&mut output);
            solve_pb(
                &ParsedPbInstance::Wbo(wbo),
                Some(&proof_path),
                Some(Duration::ZERO),
                Instant::now(),
                false,
                false,
                &term_flag,
                &mut out,
                &best_solution,
                None,
            )
            .expect("expired WBO proof route should stop cleanly")
        };

        assert_eq!(outcome.solution.status, PbStatus::Unknown);
        assert!(outcome.solution.assignment.is_empty());
        assert!(outcome.solution.objective.is_none());
        assert!(
            !proof_path.exists(),
            "expired WBO proof route must clear stale proof sidecars"
        );
        assert!(
            !sidecar_path.exists(),
            "expired WBO proof route must clear stale conflict-row sidecars"
        );
        assert!(
            output.is_empty(),
            "solve_pb should not emit WBO unsupported comments after timeout"
        );
        assert!(
            best_solution
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .is_none(),
            "expired proof route must clear cached incumbents before final output"
        );

        let mut out = PbOutputWriter::new(&mut output);
        let status = write_result_or_best_known(&mut out, &outcome.solution, &best_solution, None)
            .expect("unknown result should render");
        let rendered = String::from_utf8(output).expect("output should be utf-8");
        remove_temp_files(&[&proof_path, &sidecar_path]);

        assert_eq!(status, PbStatus::Unknown);
        assert_eq!(rendered, "s UNKNOWN\n");
    }

    // PROOF-TO-SCORE regression: an UNKNOWN result with a cached feasible
    // incumbent must be flushed as SATISFIABLE on a plain timeout (no SIGTERM),
    // not withheld. The incumbent satisfies the original constraints, so the
    // emission-boundary VIG accepts it. No `o` line is re-emitted (it was streamed
    // during the anytime search); the witness `v` line is present.
    #[test]
    fn unknown_result_flushes_verified_incumbent_without_sigterm() {
        let instance = ay_pb::parse_opb(concat!(
            "* #variable= 3 #constraint= 1\n",
            "min: +1 x1 +1 x2 +1 x3 ;\n",
            "+1 x1 +1 x2 +1 x3 >= 1 ;\n",
        ))
        .expect("optimization fixture should parse");
        let best_solution = Mutex::new(Some(PbExactSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false, false],
            objective: Some(1),
        }));
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);
        let status = write_result_or_best_known(
            &mut out,
            &unknown_solution(),
            &best_solution,
            Some(&instance.constraints),
        )
        .expect("recovered incumbent should render");
        let rendered = String::from_utf8(output).expect("output should be utf-8");

        assert_eq!(status, PbStatus::Satisfiable);
        assert_eq!(rendered, "s SATISFIABLE\nv x1 -x2 -x3\n");
    }

    // The emission-boundary VIG must fail closed: an UNKNOWN result whose cached
    // "incumbent" violates the original constraints is downgraded to UNKNOWN
    // rather than emitted as a wrong SATISFIABLE.
    #[test]
    fn unknown_result_with_infeasible_incumbent_fails_closed_to_unknown() {
        let instance = ay_pb::parse_opb(concat!(
            "* #variable= 3 #constraint= 1\n",
            "min: +1 x1 +1 x2 +1 x3 ;\n",
            "+1 x1 +1 x2 +1 x3 >= 1 ;\n",
        ))
        .expect("optimization fixture should parse");
        // All-false violates `x1+x2+x3 >= 1`.
        let best_solution = Mutex::new(Some(PbExactSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, false, false],
            objective: Some(0),
        }));
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);
        let status = write_result_or_best_known(
            &mut out,
            &unknown_solution(),
            &best_solution,
            Some(&instance.constraints),
        )
        .expect("infeasible incumbent should fail closed");
        let rendered = String::from_utf8(output).expect("output should be utf-8");

        assert_eq!(status, PbStatus::Unknown);
        assert_eq!(rendered, "s UNKNOWN\n");
    }

    // A cached `OptimumFound` must NOT be re-claimed as OPTIMUM on an UNKNOWN
    // result (the optimum gate is not re-derived at this boundary); it is flushed
    // as a sound SATISFIABLE incumbent.
    #[test]
    fn unknown_result_downgrades_cached_optimum_to_satisfiable() {
        let instance = ay_pb::parse_opb(concat!(
            "* #variable= 2 #constraint= 1\n",
            "min: +1 x1 +1 x2 ;\n",
            "+1 x1 +1 x2 >= 1 ;\n",
        ))
        .expect("optimization fixture should parse");
        let best_solution = Mutex::new(Some(PbExactSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true, false],
            objective: Some(1),
        }));
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);
        let status = write_result_or_best_known(
            &mut out,
            &unknown_solution(),
            &best_solution,
            Some(&instance.constraints),
        )
        .expect("recovered incumbent should render");
        let rendered = String::from_utf8(output).expect("output should be utf-8");

        assert_eq!(status, PbStatus::Satisfiable);
        assert!(!rendered.contains("OPTIMUM"));
        assert_eq!(rendered, "s SATISFIABLE\nv x1 -x2\n");
    }

    // OBJECTIVE-RANGE OVERFLOW RECOVERY: an OPT instance whose objective range
    // overflows i128 used to forfeit credit with `s UNSUPPORTED`. It must now be
    // recovered to a VIG-verified `s SATISFIABLE` (or `s UNSATISFIABLE`), never
    // OPTIMUM. A 1e38-per-term objective fits each coefficient in i128 but the
    // range (sum) overflows, so `objective_range_fits_i64` is false.
    #[test]
    fn objective_range_overflow_recovers_satisfiable_not_unsupported() {
        let file_path = write_temp_pb(
            "objective-overflow-sat",
            "opb",
            concat!(
                "* #variable= 3 #constraint= 2\n",
                "min: +100000000000000000000000000000000000000 x1 ",
                "+100000000000000000000000000000000000000 x2 ",
                "+100000000000000000000000000000000000000 x3 ;\n",
                "+1 x1 +1 x2 >= 1 ;\n",
                "+1 x3 >= 1 ;\n",
            ),
        );
        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: None,
            stats: false,
            stats_json: false,
            native: false,
        };
        let mut output = Vec::new();
        let status =
            run_solve_with_writer(&cmd, &mut output).expect("overflow OPT instance should solve");
        let rendered = String::from_utf8(output).expect("output should be utf-8");
        remove_temp_files(&[&file_path]);

        assert_eq!(status, PbStatus::Satisfiable);
        assert!(rendered.contains("s SATISFIABLE"), "rendered: {rendered}");
        assert!(!rendered.contains("UNSUPPORTED"), "rendered: {rendered}");
        assert!(!rendered.contains("OPTIMUM"), "rendered: {rendered}");
        assert!(
            rendered.contains("\nv "),
            "expected a witness line: {rendered}"
        );
    }

    // The recovery must keep UNSAT soundness: an infeasible overflow instance is
    // reported `s UNSATISFIABLE` (no feasible point exists for any objective).
    #[test]
    fn objective_range_overflow_reports_unsatisfiable_when_infeasible() {
        let file_path = write_temp_pb(
            "objective-overflow-unsat",
            "opb",
            concat!(
                "* #variable= 2 #constraint= 2\n",
                "min: +100000000000000000000000000000000000000 x1 ",
                "+100000000000000000000000000000000000000 x2 ;\n",
                "+1 x1 >= 1 ;\n",
                "+1 ~x1 >= 1 ;\n",
            ),
        );
        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: None,
            stats: false,
            stats_json: false,
            native: false,
        };
        let mut output = Vec::new();
        let status = run_solve_with_writer(&cmd, &mut output)
            .expect("infeasible overflow OPT instance should solve");
        let rendered = String::from_utf8(output).expect("output should be utf-8");
        remove_temp_files(&[&file_path]);

        assert_eq!(status, PbStatus::Unsatisfiable);
        assert!(rendered.contains("s UNSATISFIABLE"), "rendered: {rendered}");
        assert!(!rendered.contains("UNSUPPORTED"), "rendered: {rendered}");
    }

    // The recovery emits the exact `o`-line when the witness's own objective value
    // fits i128 (a valid upper bound), proving the value path is wired up.
    #[test]
    fn objective_range_overflow_emits_oline_when_witness_value_fits() {
        // Range overflows (two 1e38 terms sum to 2e38 > i128::MAX), but the unique
        // feasible witness sets exactly one of them, so its value 1e38 fits i128.
        let file_path = write_temp_pb(
            "objective-overflow-oline",
            "opb",
            concat!(
                "* #variable= 2 #constraint= 2\n",
                "min: +100000000000000000000000000000000000000 x1 ",
                "+100000000000000000000000000000000000000 x2 ;\n",
                "+1 x1 >= 1 ;\n",
                "+1 ~x2 >= 1 ;\n",
            ),
        );
        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: None,
            stats: false,
            stats_json: false,
            native: false,
        };
        let mut output = Vec::new();
        let status =
            run_solve_with_writer(&cmd, &mut output).expect("overflow OPT instance should solve");
        let rendered = String::from_utf8(output).expect("output should be utf-8");
        remove_temp_files(&[&file_path]);

        assert_eq!(status, PbStatus::Satisfiable);
        assert!(
            rendered.contains("o 100000000000000000000000000000000000000"),
            "expected exact o-line for the in-range witness value: {rendered}"
        );
    }

    // Emergency-flush (gap c) core: a feasible incumbent is emitted as
    // SATISFIABLE; an infeasible one or a missing one fails closed to UNKNOWN.
    #[test]
    fn emergency_emit_solution_is_vig_gated() {
        let instance = ay_pb::parse_opb(concat!(
            "* #variable= 3 #constraint= 1\n",
            "min: +1 x1 +1 x2 +1 x3 ;\n",
            "+1 x1 +1 x2 +1 x3 >= 1 ;\n",
        ))
        .expect("fixture should parse");
        let c = &instance.constraints;

        // Feasible witness -> SATISFIABLE, no objective re-emitted.
        let sat = emergency_emit_solution(c, Some(&[true, false, false]));
        assert_eq!(sat.status, PbStatus::Satisfiable);
        assert_eq!(sat.assignment, vec![true, false, false]);
        assert!(sat.objective.is_none());

        // Infeasible witness (all-false violates >= 1) -> UNKNOWN.
        let bad = emergency_emit_solution(c, Some(&[false, false, false]));
        assert_eq!(bad.status, PbStatus::Unknown);
        assert!(bad.assignment.is_empty());

        // No witness -> UNKNOWN.
        let none = emergency_emit_solution(c, None);
        assert_eq!(none.status, PbStatus::Unknown);
    }

    // Emergency-flush plumbing: arming the store and recording a feasible
    // incumbent makes the panic-time flush emit SATISFIABLE; the produced output
    // is a complete competition result. Serialized against any other global test.
    #[test]
    fn emergency_flush_emits_recorded_incumbent() {
        static EMERGENCY_TEST_LOCK: Mutex<()> = Mutex::new(());
        let _serial = EMERGENCY_TEST_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        let instance = ay_pb::parse_opb(concat!(
            "* #variable= 2 #constraint= 1\n",
            "min: +1 x1 +1 x2 ;\n",
            "+1 x1 +1 x2 >= 1 ;\n",
        ))
        .expect("fixture should parse");

        // Disarmed: flush yields UNKNOWN.
        disarm_emergency_incumbent();
        let mut output = Vec::new();
        {
            let mut out = PbOutputWriter::new(&mut output);
            assert_eq!(
                flush_emergency_incumbent_or_unknown(&mut out),
                PbStatus::Unknown
            );
        }
        assert_eq!(String::from_utf8(output).expect("utf-8"), "s UNKNOWN\n");

        // Armed + recorded feasible incumbent: flush yields SATISFIABLE witness.
        arm_emergency_incumbent(Arc::new(ParsedPbInstance::Opb(Arc::new(instance))));
        record_emergency_incumbent(&[true, false]);
        let mut output = Vec::new();
        {
            let mut out = PbOutputWriter::new(&mut output);
            assert_eq!(
                flush_emergency_incumbent_or_unknown(&mut out),
                PbStatus::Satisfiable
            );
        }
        assert_eq!(
            String::from_utf8(output).expect("utf-8"),
            "s SATISFIABLE\nv x1 -x2\n"
        );
        disarm_emergency_incumbent();
    }

    #[test]
    fn proof_mode_expired_start_nonlinear_returns_unknown_before_unsupported() {
        let input = concat!(
            "* #variable= 2 #constraint= 1\n",
            "min: +1 x1 x2 ;\n",
            "+1 x1 +1 x2 <= 1 ;\n",
        );
        let ParsedPbInstance::Opb(pb) =
            parse_instance_interruptible(PbInputFormat::Opb, input, || false)
                .expect("non-linear OPB fixture should parse")
        else {
            panic!("expected OPB fixture");
        };
        let proof_path = unique_temp_path("proof-mode-expired-start-nonlinear", "pbp");
        fs::write(&proof_path, "stale proof").expect("stale proof path should be writable");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();

        let outcome = {
            let mut out = PbOutputWriter::new(&mut output);
            solve_pb(
                &ParsedPbInstance::Opb(pb),
                Some(&proof_path),
                Some(Duration::ZERO),
                Instant::now(),
                false,
                false,
                &term_flag,
                &mut out,
                &best_solution,
                Some(input),
            )
            .expect("expired non-linear proof route should stop cleanly")
        };

        assert_eq!(outcome.solution.status, PbStatus::Unknown);
        assert!(outcome.solution.assignment.is_empty());
        assert!(outcome.solution.objective.is_none());
        assert!(
            !proof_path.exists(),
            "expired non-linear proof route must clear stale proof sidecars"
        );
        assert!(
            output.is_empty(),
            "solve_pb should not emit non-linear unsupported comments after timeout"
        );

        let mut out = PbOutputWriter::new(&mut output);
        let status = write_result_or_best_known(&mut out, &outcome.solution, &best_solution, None)
            .expect("unknown result should render");
        let rendered = String::from_utf8(output).expect("output should be utf-8");
        remove_temp_files(&[&proof_path]);

        assert_eq!(status, PbStatus::Unknown);
        assert_eq!(rendered, "s UNKNOWN\n");
    }

    #[test]
    fn proof_mode_clique_writes_solver_owned_conflict_row_map_sidecar() {
        // The sidecar is a §4.3-sensitive extra file, OFF by default in
        // competition runs; this test opts in explicitly. Serialized with the
        // off-by-default test below via the shared process-environment lock.
        let _serial = lock_env();
        let _sidecar_env = ScopedEnvVar::set("AY_PB_CLIQUE_ROW_MAP_SIDECAR", "1");
        let file_path = write_temp_pb(
            "proof-mode-clique-row-map",
            "opb",
            concat!(
                "* #variable= 3 #constraint= 2\n",
                "min: -1 x2 -1 x3 ;\n",
                "+1 x1 >= 1 ;\n",
                "-1 x2 -1 x3 >= -1 ;\n",
            ),
        );
        let proof_path = unique_temp_path("proof-mode-clique-row-map", "pbp");
        let sidecar_path = clique_conflict_row_import_map_sidecar_path(&proof_path);
        let _ = fs::remove_file(&sidecar_path);

        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: Some(proof_path.clone()),
            stats: false,
            stats_json: false,
            native: false,
        };
        let status = run_solve(&cmd).expect("proof-mode clique fixture should solve");
        let sidecar = fs::read_to_string(&sidecar_path)
            .expect("clique conflict row/import sidecar should be committed");

        assert_eq!(status, PbStatus::OptimumFound);
        assert!(proof_path.exists(), "completed proof should be committed");
        assert!(sidecar.contains(
            "2,4,2,2,3,0,1,c15e224da5943ff11a3c8ea9524d4b2bf6c456d7b8a63e3ab6c795409be2bc25,-1 x2 -1 x3 >= -1 ;"
        ));

        remove_temp_files(&[&file_path, &proof_path, &sidecar_path]);
    }

    #[test]
    fn proof_mode_clique_row_map_sidecar_is_off_by_default() {
        // Competition compliance (requirements §4.3): without the explicit
        // opt-in, a clique-shaped certified solve must write NOTHING next to
        // PROOFFILE except the proof itself. Serialized with the opt-in test
        // above via the shared process-environment lock.
        let _serial = lock_env();
        let _sidecar_env = ScopedEnvVar::unset("AY_PB_CLIQUE_ROW_MAP_SIDECAR");
        let file_path = write_temp_pb(
            "proof-mode-clique-row-map-off",
            "opb",
            concat!(
                "* #variable= 3 #constraint= 2\n",
                "min: -1 x2 -1 x3 ;\n",
                "+1 x1 >= 1 ;\n",
                "-1 x2 -1 x3 >= -1 ;\n",
            ),
        );
        let proof_path = unique_temp_path("proof-mode-clique-row-map-off", "pbp");
        let sidecar_path = clique_conflict_row_import_map_sidecar_path(&proof_path);
        let _ = fs::remove_file(&sidecar_path);

        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: Some(proof_path.clone()),
            stats: false,
            stats_json: false,
            native: false,
        };
        let status = run_solve(&cmd).expect("proof-mode clique fixture should solve");
        let sidecar_exists = sidecar_path.exists();

        assert_eq!(status, PbStatus::OptimumFound);
        assert!(proof_path.exists(), "completed proof should be committed");
        assert!(
            !sidecar_exists,
            "sidecar must not be written without AY_PB_CLIQUE_ROW_MAP_SIDECAR=1"
        );

        remove_temp_files(&[&file_path, &proof_path, &sidecar_path]);
    }

    /// OPT-NLC-CERT (commit 596f99fb) replaced the earlier fail-closed refusal:
    /// a non-linear OPB `--proof` request is linearized (objective-equivalent),
    /// the linear companion formula is committed to `<proof>.opb`, and the proof
    /// certifies the (equal) optimum over that companion.
    #[test]
    fn test_proof_mode_less_equal_nonlinear_opb_certifies_via_linearization() {
        let file_path = write_temp_pb(
            "proof-mode-less-equal-nonlinear-opb",
            "opb",
            concat!(
                "* #variable= 2 #constraint= 1\n",
                "min: +1 x1 x2 ;\n",
                "+1 x1 +1 x2 <= 1 ;\n",
            ),
        );
        let proof_path = unique_temp_path("proof-mode-less-equal-nonlinear-opb", "pbp");
        let formula_path = proof_path.with_extension("opb");
        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: Some(proof_path.clone()),
            stats: false,
            stats_json: false,
            native: false,
        };

        let status = run_solve(&cmd).expect("non-linear OPB proof route should solve");
        let proof = fs::read_to_string(&proof_path)
            .expect("linearized non-linear OPB proof should be committed");
        let formula = fs::read_to_string(&formula_path)
            .expect("linearized companion OPB formula should be committed");
        remove_temp_files(&[&file_path, &proof_path, &formula_path]);

        assert_eq!(status, PbStatus::OptimumFound);
        let companion =
            ay_pb::parse_opb(&formula).expect("companion formula should be a parseable linear OPB");
        assert!(
            companion
                .constraints
                .iter()
                .all(|c| c.terms.iter().all(|t| t.lits.len() == 1)),
            "companion formula must be fully linearized: {formula}"
        );
        // Bare (`conclusion BOUNDS 0 0;`) or hinted (`conclusion BOUNDS 0 : <id>
        // 0 : <witness>;`) conclusion form; the hints keep the conclusion
        // verifiable in unchecked-deletion mode.
        assert!(
            proof.lines().any(|line| line == "conclusion BOUNDS 0 0;"
                || (line.starts_with("conclusion BOUNDS 0 : ")
                    && line.contains(" 0 : ")
                    && line.ends_with(';'))),
            "linearized proof should certify the NLC optimum 0: {proof}"
        );
        assert_eq!(
            proof.lines().last(),
            Some("end pseudo-Boolean proof;"),
            "linearized proof should end with VeriPB terminator: {proof}"
        );
    }

    /// WBO-CERT (commit f42f5988) replaced the earlier fail-closed refusal: a WBO
    /// `--proof` request is projected to a faithful PBO (paid soft -> relaxation
    /// var; optimum preserved), the projected formula is committed to
    /// `<proof>.opb`, and the proof certifies the WBO optimum over that companion.
    #[test]
    fn test_proof_mode_less_equal_wbo_certifies_via_projection() {
        let file_path = write_temp_pb(
            "proof-mode-less-equal-wbo",
            "wbo",
            concat!("soft: 10 ;\n", "+1 x1 +1 x2 <= 1 ;\n", "[4] +1 x1 <= 0 ;\n",),
        );
        let proof_path = unique_temp_path("proof-mode-less-equal-wbo", "pbp");
        let formula_path = proof_path.with_extension("opb");
        let cmd = SolveArgs {
            file: file_path.clone(),
            timeout: Some(5_000),
            proof: Some(proof_path.clone()),
            stats: false,
            stats_json: false,
            native: false,
        };

        let status = run_solve(&cmd).expect("WBO proof route should solve");
        let proof =
            fs::read_to_string(&proof_path).expect("projected WBO proof should be committed");
        let formula = fs::read_to_string(&formula_path)
            .expect("projected companion OPB formula should be committed");
        remove_temp_files(&[&file_path, &proof_path, &formula_path]);

        assert_eq!(status, PbStatus::OptimumFound);
        ay_pb::parse_opb(&formula).expect("companion formula should be a parseable OPB");
        // Optimum 0: x1 = 0 satisfies the soft `[4] +1 x1 <= 0` at zero cost.
        // Bare or hinted conclusion form (see the linearization test above).
        assert!(
            proof.lines().any(|line| line == "conclusion BOUNDS 0 0;"
                || (line.starts_with("conclusion BOUNDS 0 : ")
                    && line.contains(" 0 : ")
                    && line.ends_with(';'))),
            "projected proof should certify the WBO optimum 0: {proof}"
        );
        assert_eq!(
            proof.lines().last(),
            Some("end pseudo-Boolean proof;"),
            "projected proof should end with VeriPB terminator: {proof}"
        );
    }

    fn decompressed_repo_xz_to_temp(relative_path: &str) -> Option<PathBuf> {
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let path = repo_root.join(relative_path);
        if !path.exists() {
            return None;
        }
        let output = std::process::Command::new("xz")
            .arg("-dc")
            .arg(&path)
            .output()
            .ok()?;
        if !output.status.success() {
            return None;
        }
        let temp_path = unique_temp_path("repo-xz-fixture", "opb");
        fs::write(&temp_path, output.stdout).ok()?;
        Some(temp_path)
    }

    #[test]
    fn test_final_result_keeps_objective_when_not_streamed() {
        let result = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true],
            objective: Some(0),
        };

        assert_eq!(
            final_optimization_result_after_anytime_stream(result, None).objective,
            Some(0)
        );
    }

    #[test]
    fn test_final_result_suppresses_duplicate_streamed_objective() {
        let result = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true],
            objective: Some(7),
        };

        assert_eq!(
            final_optimization_result_after_anytime_stream(result, Some(7)).objective,
            None
        );
    }

    #[test]
    fn test_project_wbo_solution_recomputes_original_soft_cost() {
        let wbo = WboInstance {
            top_cost: Some(10),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                7,
                ay_pb::PbConstraint {
                    terms: vec![ay_pb::PbTerm {
                        coeff: 1,
                        lits: vec![ay_pb::PbLit {
                            var: 1,
                            negated: false,
                        }],
                    }],
                    rel: ay_pb::PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: None,
        };
        let transformed_solution = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(123),
        };

        let projected = project_wbo_solution(transformed_solution, &wbo);

        assert_eq!(projected.assignment, vec![false]);
        assert_eq!(projected.objective, Some(7));
    }

    #[test]
    fn test_project_wbo_solution_fails_closed_on_short_solved_witness() {
        let wbo = WboInstance {
            top_cost: Some(10),
            num_vars: 2,
            hard_constraints: vec![],
            soft_constraints: vec![],
            objective: None,
        };
        let transformed_solution = PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true],
            objective: Some(0),
        };

        let projected = project_wbo_solution(transformed_solution, &wbo);

        assert_eq!(projected.status, PbStatus::Unknown);
        assert!(projected.assignment.is_empty());
        assert_eq!(projected.objective, None);
    }

    #[test]
    fn test_exact_wbo_solution_fails_closed_on_short_solved_witness() {
        let wbo = WboInstance {
            top_cost: Some(10),
            num_vars: 2,
            hard_constraints: vec![],
            soft_constraints: vec![],
            objective: None,
        };

        let exact =
            exact_wbo_solution_from_assignment(&wbo, PbStatus::Satisfiable, &[true], Some(4));

        assert_eq!(exact.status, PbStatus::Unknown);
        assert!(exact.assignment.is_empty());
        assert_eq!(exact.objective, None);
    }

    /// A single-variable WBO whose soft `[cost] +1 x1 >= 1` is falsified by
    /// `x1 = false`, with the given top cost.
    fn single_soft_wbo(top_cost: Option<i128>, cost: i128) -> WboInstance {
        WboInstance {
            top_cost,
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                cost,
                ay_pb::PbConstraint {
                    terms: vec![ay_pb::PbTerm {
                        coeff: 1,
                        lits: vec![ay_pb::PbLit {
                            var: 1,
                            negated: false,
                        }],
                    }],
                    rel: ay_pb::PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: None,
        }
    }

    #[test]
    fn test_project_wbo_solution_downgrades_model_at_or_above_top_cost() {
        // Cost of the falsified soft (7) reaches the top cost (7): the model
        // is inadmissible under the strictly-less-than rule and must not be
        // emitted as SATISFIABLE.
        let wbo = single_soft_wbo(Some(7), 7);
        let solution = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false],
            objective: Some(7),
        };

        let projected = project_wbo_solution(solution, &wbo);

        assert_eq!(projected.status, PbStatus::Unknown);
        assert!(projected.assignment.is_empty());
        assert_eq!(projected.objective, None);
    }

    #[test]
    fn test_project_wbo_solution_keeps_model_strictly_below_top_cost() {
        let wbo = single_soft_wbo(Some(8), 7);
        let solution = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false],
            objective: Some(123),
        };

        let projected = project_wbo_solution(solution, &wbo);

        assert_eq!(projected.status, PbStatus::Satisfiable);
        assert_eq!(projected.objective, Some(7));
    }

    #[test]
    fn test_exact_wbo_solution_downgrades_model_at_or_above_top_cost() {
        let wbo = single_soft_wbo(Some(7), 7);

        let exact =
            exact_wbo_solution_from_assignment(&wbo, PbStatus::Satisfiable, &[false], Some(7));

        assert_eq!(exact.status, PbStatus::Unknown);
        assert!(exact.assignment.is_empty());
        assert_eq!(exact.objective, None);
    }

    #[test]
    fn test_prefer_cheaper_cached_wbo_incumbent_swaps_in_cheaper_model() {
        let cached = Mutex::new(Some(PbExactSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(3),
        }));
        let result = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(8),
        };

        let reconciled = prefer_cheaper_cached_wbo_incumbent(result, &cached);

        assert_eq!(reconciled.status, PbStatus::Satisfiable);
        assert_eq!(reconciled.assignment, vec![true, false]);
        assert_eq!(reconciled.objective, Some(3));
    }

    #[test]
    fn test_prefer_cheaper_cached_wbo_incumbent_keeps_result_when_not_cheaper() {
        let cached = Mutex::new(Some(PbExactSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(8),
        }));
        let result = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(8),
        };

        let reconciled = prefer_cheaper_cached_wbo_incumbent(result, &cached);

        assert_eq!(reconciled.assignment, vec![false, true]);
        assert_eq!(reconciled.objective, Some(8));
    }

    fn solve_wbo_text(input: &str) -> PbSolution {
        let instance = parse_instance_interruptible(PbInputFormat::Wbo, input, || false)
            .expect("WBO text should parse");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);
        solve_pb(
            &instance,
            None,
            Some(Duration::from_secs(10)),
            Instant::now(),
            false,
            false,
            &term_flag,
            &mut out,
            &best_solution,
            None,
        )
        .expect("WBO solve should succeed")
        .solution
    }

    #[test]
    fn test_decision_sat_solution_proof_text_shape() {
        let instance = ay_pb::parse_opb(
            "* #variable= 3 #constraint= 2\n+1 x1 +1 x2 >= 1 ;\n+1 x2 +1 x3 >= 1 ;\n",
        )
        .expect("parse");
        let dir = std::env::temp_dir().join(format!("ay-decsat-proof-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("dir");
        let final_path = dir.join("p.veripb");
        let temp_path = dir.join("p.veripb.tmp");
        commit_decision_sat_solution_proof(
            &instance,
            &[true, true, false],
            &final_path,
            &temp_path,
        )
        .expect("commit proof");
        let text = std::fs::read_to_string(&final_path).expect("read");
        assert!(text.starts_with("pseudo-Boolean proof version 3.0\n"));
        assert!(text.contains("f 2 ;"));
        // Library-writer format (no space before the semicolon): the binary
        // delegates to ay_pb::proof::solution_only_sat_proof, so this shape is
        // pinned by the writer's own tests and must match here byte-for-byte.
        assert!(text.contains("conclusion SAT : x1 x2 ~x3;"));
        assert!(text.trim_end().ends_with("end pseudo-Boolean proof;"));
        assert!(!temp_path.exists(), "temp must be renamed away");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_dec_cert_pipeline_certifies_sat_via_solution_proof() {
        let _serial = lock_env();
        let _cert = clear_cert_env();
        // Kill N1: the plain-speed phase must produce the model and the
        // solution-only proof must be committed.
        let _cap = ScopedEnvVar::set("AY_PB_CERT_NATIVE_CAP_MS", "0");
        let instance = parse_instance_interruptible(
            PbInputFormat::Opb,
            "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n",
            || false,
        )
        .expect("parse");
        let dir = std::env::temp_dir().join(format!("ay-deccert-sat-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("dir");
        let proof_path = dir.join("dec.veripb");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);
        let outcome = solve_pb(
            &instance,
            Some(&proof_path),
            Some(Duration::from_secs(10)),
            Instant::now(),
            false,
            false,
            &term_flag,
            &mut out,
            &best_solution,
            None,
        )
        .expect("solve");
        assert_eq!(outcome.solution.status, PbStatus::Satisfiable);
        let text = std::fs::read_to_string(&proof_path).expect("proof committed");
        assert!(
            text.contains("conclusion SAT :"),
            "solution-only conclusion expected: {text}"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_dec_cert_pipeline_unsat_via_native_tail() {
        let _serial = lock_env();
        let _cert = clear_cert_env();
        let _cap = ScopedEnvVar::set("AY_PB_CERT_NATIVE_CAP_MS", "0");
        let instance = parse_instance_interruptible(
            PbInputFormat::Opb,
            "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n",
            || false,
        )
        .expect("parse");
        let dir = std::env::temp_dir().join(format!("ay-deccert-unsat-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("dir");
        let proof_path = dir.join("dec.veripb");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);
        let outcome = solve_pb(
            &instance,
            Some(&proof_path),
            Some(Duration::from_secs(10)),
            Instant::now(),
            false,
            false,
            &term_flag,
            &mut out,
            &best_solution,
            None,
        )
        .expect("solve");
        assert_eq!(outcome.solution.status, PbStatus::Unsatisfiable);
        assert!(
            proof_path.exists(),
            "UNSAT must carry a committed native proof"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_wbo_binding_top_cost_answers_unsatisfiable() {
        // The hard row forbids x1 and x2 together, so every model falsifies a
        // cost-2 soft: the minimum cost is 2, which is not strictly less than
        // the top cost 2 — the correct answer is UNSATISFIABLE.
        let solution = solve_wbo_text(
            "* #variable= 2 #constraint= 3\n\
             soft: 2 ;\n\
             -1 x1 -1 x2 >= -1 ;\n\
             [2] +1 x1 >= 1 ;\n\
             [2] +1 x2 >= 1 ;\n",
        );
        assert_eq!(solution.status, PbStatus::Unsatisfiable);
    }

    #[test]
    fn test_wbo_top_cost_above_optimum_answers_optimum() {
        // Same instance with top cost 3: the optimum 2 is admissible.
        let solution = solve_wbo_text(
            "* #variable= 2 #constraint= 3\n\
             soft: 3 ;\n\
             -1 x1 -1 x2 >= -1 ;\n\
             [2] +1 x1 >= 1 ;\n\
             [2] +1 x2 >= 1 ;\n",
        );
        assert_eq!(solution.status, PbStatus::OptimumFound);
        assert_eq!(solution.objective, Some(2));
    }

    #[test]
    fn test_wbo_nonpositive_top_cost_answers_unsatisfiable() {
        // Costs are non-negative, so a zero top cost admits no model at all.
        let solution = solve_wbo_text("soft: 0 ;\n+1 x1 >= 1 ;\n[1] +1 x1 >= 1 ;\n");
        assert_eq!(solution.status, PbStatus::Unsatisfiable);
    }

    #[test]
    fn test_wbo_negative_cost_with_nonpositive_top_fails_closed_to_unsupported() {
        // The top <= 0 short-circuit's premise (costs are non-negative) is
        // validated by the converter; a parser-accepted negative weight must
        // fall through to its fail-closed UNSUPPORTED, not assert a verdict.
        let solution = solve_wbo_text("soft: 0 ;\n+1 x1 >= 1 ;\n[-5] +1 x1 >= 1 ;\n");
        assert_eq!(solution.status, PbStatus::Unsupported);
    }

    #[test]
    fn test_wbo_huge_soft_cost_with_small_top_answers_unsatisfiable() {
        // Regression: the budget row used to carry the raw cost as a
        // coefficient, panicking preprocessing (caught -> UNKNOWN). With the
        // top-capped coefficient the decidable verdict is recovered: the hard
        // row forces x1 = 0, the falsified soft costs i128::MAX >= top 1.
        let solution = solve_wbo_text(
            "soft: 1 ;\n\
             -1 x1 >= 0 ;\n\
             [170141183460469231731687303715884105727] +1 x1 >= 1 ;\n",
        );
        assert_eq!(solution.status, PbStatus::Unsatisfiable);
    }

    #[test]
    fn test_proof_mode_flushes_feasible_incumbent_when_optimum_unproven() {
        // PROOF-TO-SCORE regression: certified mode used to clear the incumbent
        // cache and answer s UNKNOWN whenever the optimality proof outlasted
        // the budget, forfeiting feasible answers the engine already found.
        // Build a 70-var random-coefficient knapsack minimization (xorshift,
        // deterministic) that yields incumbents immediately but is not provable
        // in the short budget on any realistic machine.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            100_000 + (state % 900_000) as i128
        };
        let n = 70;
        let coeffs: Vec<i128> = (0..n).map(|_| next()).collect();
        let total: i128 = coeffs.iter().sum();
        let obj: String = coeffs
            .iter()
            .enumerate()
            .map(|(i, c)| format!("+{c} x{}", i + 1))
            .collect::<Vec<_>>()
            .join(" ");
        let input = format!(
            "* #variable= {n} #constraint= 2\nmin: {obj} ;\n{obj} >= {} ;\n{} >= 10 ;\n",
            total / 3,
            (1..=n)
                .map(|i| format!("+1 x{i}"))
                .collect::<Vec<_>>()
                .join(" "),
        );

        let instance = parse_instance_interruptible(PbInputFormat::Opb, &input, || false)
            .expect("knapsack OPB should parse");
        let proof_dir =
            std::env::temp_dir().join(format!("ay-proof-flush-test-{}", std::process::id()));
        std::fs::create_dir_all(&proof_dir).expect("proof dir should create");
        let proof_path = proof_dir.join("unproven.veripb");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);

        let outcome = solve_pb(
            &instance,
            Some(&proof_path),
            Some(Duration::from_millis(1500)),
            Instant::now(),
            false,
            false,
            &term_flag,
            &mut out,
            &best_solution,
            None,
        )
        .expect("proof-mode solve should succeed");

        match outcome.solution.status {
            // The regression: a feasible incumbent existed but UNKNOWN was
            // returned with the cache cleared. Now the incumbent must survive
            // in the cache for the boundary flush.
            PbStatus::Unknown => {
                let cached = best_solution
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .clone()
                    .expect("feasible incumbent must remain cached for the flush");
                assert_eq!(cached.status, PbStatus::Satisfiable);
                assert!(cached.objective.is_some());
                assert!(
                    !proof_path.exists(),
                    "no certificate may be claimed without an optimality proof"
                );
                let rendered = String::from_utf8_lossy(&output);
                assert!(
                    rendered.contains("o "),
                    "improving incumbents should stream o lines, got: {rendered}"
                );
            }
            // Acceptable alternate outcome on an implausibly fast prover.
            PbStatus::OptimumFound => {
                assert!(proof_path.exists(), "OPTIMUM claim requires the proof");
            }
            other => panic!("unexpected proof-mode status: {other:?}"),
        }
        let _ = std::fs::remove_dir_all(&proof_dir);
    }

    #[test]
    fn test_wbo_omitted_top_cost_solves_unbounded() {
        // "soft: ;" (no integer) is legal and means no cost bound; previously
        // this failed to parse and produced no `s` line at all.
        let solution = solve_wbo_text(
            "soft: ;\n\
             -1 x1 -1 x2 >= -1 ;\n\
             [2] +1 x1 >= 1 ;\n\
             [2] +1 x2 >= 1 ;\n",
        );
        assert_eq!(solution.status, PbStatus::OptimumFound);
        assert_eq!(solution.objective, Some(2));
    }

    /// Clears the AY_PB_OPT_CERT_PORTFOLIO / AY_PB_CERT_NATIVE_CAP_MS
    /// process-global env vars for the lifetime of the returned guards
    /// (restored on scope exit, also on panic). Bind at the start of each cert
    /// test — held under the `lock_env()` serialization guard. Tests serialize
    /// on the one workspace env lock (`lock_env`).
    #[must_use]
    fn clear_cert_env() -> [ScopedEnvVar; 2] {
        [
            ScopedEnvVar::unset("AY_PB_OPT_CERT_PORTFOLIO"),
            ScopedEnvVar::unset("AY_PB_CERT_NATIVE_CAP_MS"),
        ]
    }

    fn solve_opb_text_with_proof(input: &str, proof_path: &Path) -> (PbSolution, String) {
        let instance = parse_instance_interruptible(PbInputFormat::Opb, input, || false)
            .expect("OPB text should parse");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);
        let outcome = solve_pb(
            &instance,
            Some(proof_path),
            Some(Duration::from_secs(10)),
            Instant::now(),
            false,
            false,
            &term_flag,
            &mut out,
            &best_solution,
            None,
        )
        .expect("proof-mode solve should succeed");
        (
            outcome.solution,
            String::from_utf8_lossy(&output).into_owned(),
        )
    }

    #[test]
    fn test_cert_opt_budget_split_tiers_and_gates() {
        let _serial = lock_env();
        let _cert = clear_cert_env();

        let small = ay_pb::parse_opb(
            "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
        )
        .expect("fixture should parse");
        let objective = small.objective.clone().expect("objective present");

        // Eligible: capped slice strictly inside the budget, grace bounded.
        let split = compute_cert_opt_budget_split(
            &small,
            &objective,
            Some(Duration::from_mins(10)),
            Instant::now(),
        );
        assert!(split.eligible());
        let now = Instant::now();
        let slice = split.native_deadline.unwrap() - now;
        let ceiling = split.native_hard_limit.unwrap() - now;
        assert!(
            slice <= Duration::from_secs(101),
            "slice ~R/6, got {slice:?}"
        );
        assert!(
            ceiling <= Duration::from_secs(201),
            "ceiling ~R/3, got {ceiling:?}"
        );
        assert!(slice < ceiling);
        assert_eq!(split.improve_grace, Duration::from_secs(30)); // min(R/12, 30s)

        // No timeout => fully uncapped (unbounded-native semantics preserved).
        let unbounded = compute_cert_opt_budget_split(&small, &objective, None, Instant::now());
        assert!(!unbounded.eligible());
        assert!(unbounded.native_hard_limit.is_none());

        // Multi-literal (non-linear) objective term => ineligible.
        let product_objective = ay_pb::PbObjective {
            terms: vec![ay_pb::PbTerm {
                coeff: 1,
                lits: vec![
                    ay_pb::PbLit {
                        var: 1,
                        negated: false,
                    },
                    ay_pb::PbLit {
                        var: 2,
                        negated: false,
                    },
                ],
            }],
        };
        let nonlinear = compute_cert_opt_budget_split(
            &small,
            &product_objective,
            Some(Duration::from_mins(10)),
            Instant::now(),
        );
        assert!(!nonlinear.eligible());
    }

    #[test]
    fn test_certify_reserve_clamps() {
        // remaining/8 clamped to [10s, 300s], never more than remaining/2.
        assert_eq!(
            certify_reserve(Duration::from_secs(10)),
            Duration::from_secs(5)
        );
        assert_eq!(
            certify_reserve(Duration::from_secs(800)),
            Duration::from_secs(100)
        );
        assert_eq!(
            certify_reserve(Duration::from_mins(50)),
            Duration::from_mins(5)
        );
    }

    #[test]
    fn test_extend_native_deadline_monotone_and_clamped() {
        let now = Instant::now();
        let split = CertOptBudgetSplit {
            native_deadline: Some(now + Duration::from_secs(10)),
            native_hard_limit: Some(now + Duration::from_secs(20)),
            improve_grace: Duration::from_mins(1),
        };
        let cell = Cell::new(split.native_deadline);
        extend_native_deadline(&cell, &split);
        // Grace (60s) clamps at the 20s hard ceiling.
        assert_eq!(cell.get(), split.native_hard_limit);
        // Monotone: a second extension cannot move it backwards or past.
        extend_native_deadline(&cell, &split);
        assert_eq!(cell.get(), split.native_hard_limit);

        // Uncapped split: extension is a no-op.
        let uncapped = CertOptBudgetSplit {
            native_deadline: None,
            native_hard_limit: None,
            improve_grace: Duration::from_mins(1),
        };
        let free = Cell::new(None);
        extend_native_deadline(&free, &uncapped);
        assert_eq!(free.get(), None);
    }

    #[test]
    fn test_cert_fallback_certifies_portfolio_optimum() {
        let _serial = lock_env();
        let _cert = clear_cert_env();
        // Kill N1 outright: the portfolio must prove the optimum and the
        // out-of-band helpers must certify it.
        let _cap = ScopedEnvVar::set("AY_PB_CERT_NATIVE_CAP_MS", "0");
        let proof_dir =
            std::env::temp_dir().join(format!("ay-cert-fallback-test-{}", std::process::id()));
        std::fs::create_dir_all(&proof_dir).expect("proof dir should create");
        let proof_path = proof_dir.join("fallback.veripb");

        let (solution, rendered) = solve_opb_text_with_proof(
            "* #variable= 2 #constraint= 2\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n-1 x1 -1 x2 >= -2 ;\n",
            &proof_path,
        );

        assert_eq!(solution.status, PbStatus::OptimumFound);
        let proof = std::fs::read_to_string(&proof_path).expect("proof must be committed");
        assert!(
            proof.contains("conclusion BOUNDS"),
            "OPT conclusion required"
        );
        assert!(
            !proof_temp_path(&proof_path).exists(),
            "no temp sibling may remain"
        );
        assert!(
            rendered.contains("o 1"),
            "optimum o line expected: {rendered}"
        );
        let _ = std::fs::remove_dir_all(&proof_dir);
    }

    #[test]
    fn test_cert_kill_switch_restores_native_only() {
        let _serial = lock_env();
        let _cert = clear_cert_env();
        // Kill switch off => the CAP override must be ignored and the native
        // full-budget path must still prove + commit.
        let _portfolio = ScopedEnvVar::set("AY_PB_OPT_CERT_PORTFOLIO", "0");
        let _cap = ScopedEnvVar::set("AY_PB_CERT_NATIVE_CAP_MS", "0");
        let proof_dir =
            std::env::temp_dir().join(format!("ay-cert-killswitch-test-{}", std::process::id()));
        std::fs::create_dir_all(&proof_dir).expect("proof dir should create");
        let proof_path = proof_dir.join("native.veripb");

        let (solution, _) = solve_opb_text_with_proof(
            "* #variable= 2 #constraint= 2\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n-1 x1 -1 x2 >= -2 ;\n",
            &proof_path,
        );

        assert_eq!(solution.status, PbStatus::OptimumFound);
        assert!(proof_path.exists(), "native proof must be committed");
        let _ = std::fs::remove_dir_all(&proof_dir);
    }

    #[test]
    fn test_cert_opt_unsat_proved_by_native_tail() {
        let _serial = lock_env();
        let _cert = clear_cert_env();
        // N1 disabled; the portfolio's UNSAT is uncertified and must NOT be
        // emitted — the native tail is the only compliant INF INF source.
        let _cap = ScopedEnvVar::set("AY_PB_CERT_NATIVE_CAP_MS", "0");
        let proof_dir =
            std::env::temp_dir().join(format!("ay-cert-tail-test-{}", std::process::id()));
        std::fs::create_dir_all(&proof_dir).expect("proof dir should create");
        let proof_path = proof_dir.join("tail.veripb");

        let (solution, _) = solve_opb_text_with_proof(
            "* #variable= 2 #constraint= 2\nmin: +1 x1 +1 x2 ;\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n",
            &proof_path,
        );

        assert_eq!(solution.status, PbStatus::Unsatisfiable);
        let proof = std::fs::read_to_string(&proof_path).expect("proof must be committed");
        assert!(
            proof.contains("conclusion BOUNDS INF INF"),
            "OPT-UNSAT conclusion required, got: {proof}"
        );
        let _ = std::fs::remove_dir_all(&proof_dir);
    }

    #[test]
    fn test_native_optimization_projection_fails_closed_on_short_model() {
        let result =
            pb_cdcl_optimization_result_to_solution(PbCdclResult::Optimal(vec![true], 3), 2);

        assert_eq!(result.status, PbStatus::Unknown);
        assert!(result.assignment.is_empty());
        assert_eq!(result.objective, None);
    }

    #[test]
    fn test_exact_optimization_incumbent_fails_closed_on_short_model() {
        let exact = exact_optimization_incumbent(&[], 2, PbStatus::Satisfiable, 9, &[true]);

        assert_eq!(exact.status, PbStatus::Unknown);
        assert!(exact.assignment.is_empty());
        assert_eq!(exact.objective, None);
    }

    /// `x1 + x2 >= 1` over 2 vars: the fixture for the binary-entry-point
    /// Verified Incumbent Gate (feasibility re-check) tests.
    fn vig_gate_constraints() -> Vec<ay_pb::PbConstraint> {
        vec![ay_pb::PbConstraint {
            terms: vec![
                ay_pb::PbTerm {
                    coeff: 1,
                    lits: vec![ay_pb::PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                ay_pb::PbTerm {
                    coeff: 1,
                    lits: vec![ay_pb::PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
            rel: ay_pb::PbRel::Ge,
            rhs: 1,
        }]
    }

    #[test]
    fn test_exact_optimization_incumbent_fails_closed_on_infeasible_model() {
        // SOUNDNESS (design §3.2): a model violating the ORIGINAL constraints
        // presented at this gate must yield NO incumbent — fail-closed to
        // UNKNOWN, never a cached/emitted witness with an objective.
        let constraints = vig_gate_constraints();

        let exact = exact_optimization_incumbent(
            &constraints,
            2,
            PbStatus::Satisfiable,
            0,
            &[false, false],
        );

        assert_eq!(exact.status, PbStatus::Unknown);
        assert!(exact.assignment.is_empty());
        assert_eq!(exact.objective, None);
    }

    #[test]
    fn test_exact_optimization_incumbent_keeps_feasible_model() {
        // 0-REGRESSION: a model that satisfies every constraint passes the gate
        // unchanged (witness + objective stored).
        let constraints = vig_gate_constraints();

        let exact =
            exact_optimization_incumbent(&constraints, 2, PbStatus::Satisfiable, 1, &[true, false]);

        assert_eq!(exact.status, PbStatus::Satisfiable);
        assert_eq!(exact.assignment, vec![true, false]);
        assert_eq!(exact.objective, Some(1));
    }

    /// Instance + objective fixture over the VIG gate constraints (`x1 + x2 >= 1`,
    /// minimize `x1 + x2`) for the streaming-gate dominance-filter tests.
    fn vig_gate_instance() -> (PbInstance, ay_pb::PbObjective) {
        let constraints = vig_gate_constraints();
        let objective = ay_pb::PbObjective {
            terms: vec![
                ay_pb::PbTerm {
                    coeff: 1,
                    lits: vec![ay_pb::PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                ay_pb::PbTerm {
                    coeff: 1,
                    lits: vec![ay_pb::PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
        };
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    #[test]
    fn test_exact_incumbent_from_model_drops_dominated_before_verification() {
        // Streaming-gate reorder: a FEASIBLE model whose exactly-recomputed
        // objective does not STRICTLY improve on the caller's bar yields NO
        // incumbent — dropped before the O(total-terms) verification scan,
        // exactly as the caller's own strict-improvement filter would have
        // dropped it afterwards.
        let (instance, objective) = vig_gate_instance();

        // Model {x1} has exact objective 1; a bar of 1 (equal) or 0 (better
        // than the model) dominates it.
        for bar in [Some(1), Some(0)] {
            let exact = exact_incumbent_from_model(
                &instance,
                &objective,
                None,
                PbStatus::Satisfiable,
                1,
                bar,
                &[true, false],
            );
            assert_eq!(exact.status, PbStatus::Unknown);
            assert!(exact.assignment.is_empty());
            assert_eq!(exact.objective, None);
        }

        // Non-vacuity control: the same model strictly under the bar (or with
        // no bar yet) passes the gate with witness + exact objective.
        for bar in [None, Some(2)] {
            let exact = exact_incumbent_from_model(
                &instance,
                &objective,
                None,
                PbStatus::Satisfiable,
                1,
                bar,
                &[true, false],
            );
            assert_eq!(exact.status, PbStatus::Satisfiable);
            assert_eq!(exact.assignment, vec![true, false]);
            assert_eq!(exact.objective, Some(1));
        }
    }

    #[test]
    fn test_exact_incumbent_from_model_infeasible_cannot_advance_filter() {
        // SOUNDNESS: an INFEASIBLE model — even one whose objective is
        // strictly under the caller's bar, so it survives the dominance
        // filter — still fails closed to `objective: None` at the VIG, and
        // the caller advances its `best_obj` bar only on `Some`. An
        // infeasible model can therefore never move the strict-improvement
        // filter.
        let (instance, objective) = vig_gate_instance();

        let exact = exact_incumbent_from_model(
            &instance,
            &objective,
            None,
            PbStatus::Satisfiable,
            0,
            Some(5),
            &[false, false],
        );

        assert_eq!(exact.status, PbStatus::Unknown);
        assert!(exact.assignment.is_empty());
        assert_eq!(exact.objective, None);
    }

    #[test]
    fn test_exact_objective_fail_closed_recomputes_wide_output_value() {
        let objective = ay_pb::PbObjective {
            terms: vec![
                ay_pb::PbTerm {
                    coeff: i128::from(i64::MAX),
                    lits: vec![ay_pb::PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                ay_pb::PbTerm {
                    coeff: 1,
                    lits: vec![ay_pb::PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
        };

        assert_eq!(
            exact_objective_fail_closed(&objective, &[true, true]),
            Some(i128::from(i64::MAX) + 1)
        );
    }

    #[test]
    fn test_exact_objective_fail_closed_rejects_i128_overflow() {
        // FAIL-CLOSED (design §3.2): when the exact i128 recompute overflows,
        // NO objective is produced — the caller must skip the incumbent, never
        // fall back to a legacy/saturated value.
        let objective = ay_pb::PbObjective {
            terms: vec![
                ay_pb::PbTerm {
                    coeff: i128::MAX,
                    lits: vec![ay_pb::PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                ay_pb::PbTerm {
                    coeff: i128::MAX,
                    lits: vec![ay_pb::PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
        };

        assert_eq!(exact_objective_fail_closed(&objective, &[true, true]), None);

        // Non-vacuity control: one wide term stays in range and is recomputed.
        assert_eq!(
            exact_objective_fail_closed(&objective, &[true, false]),
            Some(i128::MAX)
        );
    }

    // =====================================================================
    // DECISION-SAT Verified-SAT-Gate (`decision_sat_self_checked`) — the
    // decision-track analogue of the optimization incumbent VIG, ported from
    // `crates/ay/src/cmd_pb.rs`. SOUNDNESS: a SAT model that fails
    // re-verification against the ORIGINAL constraints is downgraded to
    // UNKNOWN (fail-closed), never a wrong `s SATISFIABLE`.
    // 0-REGRESSION: a model that DOES verify is returned unchanged.
    // =====================================================================

    /// `x1 + x2 >= 1` over 2 vars, no objective (a decision instance).
    fn decision_sat_gate_instance() -> PbInstance {
        PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vig_gate_constraints(),
            objective: None,
        }
    }

    #[test]
    fn decision_sat_gate_keeps_feasible_model_satisfiable() {
        // 0-REGRESSION: x1=true satisfies `x1 + x2 >= 1`, so the gate must pass
        // the verdict through UNCHANGED (no false UNKNOWN on a valid model).
        let instance = decision_sat_gate_instance();
        let solution = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: None,
        };

        let gated = decision_sat_self_checked(solution.clone(), &instance);

        assert_eq!(gated.status, PbStatus::Satisfiable);
        assert_eq!(gated.assignment, vec![true, false]);
    }

    #[test]
    fn decision_sat_gate_fails_closed_on_infeasible_model() {
        // SOUNDNESS: x1=false, x2=false violates `x1 + x2 >= 1`. A core-solver
        // bug that returned this model as SAT must be caught — the gate
        // downgrades it to UNKNOWN, never emitting a wrong `s SATISFIABLE`.
        let instance = decision_sat_gate_instance();
        let wrong = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, false],
            objective: None,
        };

        let gated = decision_sat_self_checked(wrong, &instance);

        assert_eq!(
            gated.status,
            PbStatus::Unknown,
            "an infeasible model claimed SAT must fail-closed to UNKNOWN"
        );
        assert!(gated.assignment.is_empty());
        assert_eq!(gated.objective, None);
    }

    #[test]
    fn decision_sat_gate_fails_closed_on_short_model() {
        // A truncated/empty model cannot satisfy the constraint (out-of-range
        // vars evaluate to false): fail-closed to UNKNOWN rather than a wrong
        // SAT.
        let instance = decision_sat_gate_instance();
        let wrong = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: Vec::new(),
            objective: None,
        };

        let gated = decision_sat_self_checked(wrong, &instance);

        assert_eq!(gated.status, PbStatus::Unknown);
    }

    #[test]
    fn decision_sat_gate_passes_through_non_sat_verdicts() {
        // The gate ONLY guards `Satisfiable`. UNSAT/UNKNOWN must pass through
        // untouched — a refutation admits no model to re-verify, and
        // downgrading it would be a regression, not a soundness gain.
        let instance = decision_sat_gate_instance();

        let unsat = PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: Vec::new(),
            objective: None,
        };
        assert_eq!(
            decision_sat_self_checked(unsat, &instance).status,
            PbStatus::Unsatisfiable
        );

        let unknown = PbSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: None,
        };
        assert_eq!(
            decision_sat_self_checked(unknown, &instance).status,
            PbStatus::Unknown
        );
    }

    #[test]
    fn test_wbo_wcsp_output_emits_only_final_projected_objective() {
        let Some(file_path) = decompressed_repo_xz_to_temp(
            "benchmarks/pb-comp/PB24/WBO/PARTIAL-LIN/wcsp/academics/normalized-4queens_wcsp.wbo.xz",
        ) else {
            eprintln!("skipping WBO WCSP objective projection test; fixture unavailable");
            return;
        };
        let input = fs::read_to_string(&file_path).expect("fixture should be readable");
        let ParsedPbInstance::Wbo(wbo) =
            parse_instance_interruptible(PbInputFormat::Wbo, &input, || false)
                .expect("WBO fixture should parse")
        else {
            panic!("expected WBO instance");
        };
        let instance = ParsedPbInstance::Wbo(wbo);
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let mut out = PbOutputWriter::new(&mut output);

        let result = solve_pb(
            &instance,
            None,
            Some(Duration::from_secs(5)),
            Instant::now(),
            false,
            false,
            &term_flag,
            &mut out,
            &best_solution,
            None,
        )
        .expect("WBO solve should succeed");
        write_result_or_best_known(&mut out, &result.solution, &best_solution, None)
            .expect("result should render");
        remove_temp_files(&[&file_path]);

        let rendered = String::from_utf8(output).expect("output should be utf-8");
        assert!(
            rendered.contains("s OPTIMUM FOUND"),
            "Expected OPTIMUM FOUND, got: {rendered}"
        );
        let objective_lines = rendered
            .lines()
            .filter(|line| line.starts_with("o "))
            .collect::<Vec<_>>();
        assert_eq!(
            objective_lines,
            vec!["o 0"],
            "WBO output must only emit the final source-cost objective matching the witness, got: {rendered}"
        );
    }

    /// Build the OPB text for the pure pigeonhole instance PHP(p, p-1): `p`
    /// pigeons, `p-1` holes, variable `x[(pig-1)*holes + hole]`. Every pigeon
    /// occupies some hole (`sum_hole x >= 1`) and every hole holds at most one
    /// pigeon (`-sum_pig x >= -1`). It is UNSAT by the counting argument, but
    /// resolution/CDCL refutations are exponential, so the native decision solver
    /// cannot crack it inside a short timeout — only the self-checked structural
    /// recognizer decides it quickly.
    fn pigeonhole_opb(pigeons: usize) -> String {
        let holes = pigeons - 1;
        let var = |pig: usize, hole: usize| (pig - 1) * holes + hole; // 1-based
        let mut rows = Vec::new();
        for pig in 1..=pigeons {
            let lits: Vec<String> = (1..=holes)
                .map(|h| format!("+1 x{}", var(pig, h)))
                .collect();
            rows.push(format!("{} >= 1 ;", lits.join(" ")));
        }
        for hole in 1..=holes {
            let lits: Vec<String> = (1..=pigeons)
                .map(|p| format!("-1 x{}", var(p, hole)))
                .collect();
            rows.push(format!("{} >= -1 ;", lits.join(" ")));
        }
        let header = format!(
            "* #variable= {} #constraint= {}\n",
            pigeons * holes,
            rows.len()
        );
        format!("{header}{}\n", rows.join("\n"))
    }

    /// REGRESSION (the wf-early-structural fix): a NATIVE LINEAR DECISION
    /// pigeonhole instance must be decided `UNSATISFIABLE` by the EARLY
    /// self-checked structural recognizer — *before* the full-timeout
    /// `solve_decision_native` call. Without the early check this instance times
    /// out to `s UNKNOWN` (the native CDCL path has no short refutation for PHP),
    /// so this test fails closed if the early check is ever removed or moved back
    /// after the native solve. The tiny 750ms timeout makes the point: the verdict
    /// is reached far inside it because the recognizer fires immediately, whereas
    /// the native solve would consume the whole budget and return `Unknown`.
    #[test]
    fn early_structural_check_decides_pigeonhole_unsat_on_native_path() {
        let instance =
            ay_pb::parse_opb(&pigeonhole_opb(20)).expect("pigeonhole fixture should parse");
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let outcome = {
            let mut out = PbOutputWriter::new(&mut output);
            solve_pb(
                &ParsedPbInstance::Opb(Arc::new(instance)),
                None,
                Some(Duration::from_millis(750)),
                Instant::now(),
                /* native = */ true,
                false,
                &term_flag,
                &mut out,
                &best_solution,
                None,
            )
            .expect("native pigeonhole decision should solve")
        };
        assert_eq!(
            outcome.solution.status,
            PbStatus::Unsatisfiable,
            "PHP(20,19) on the native decision path must be decided UNSAT by the early \
             self-checked structural recognizer, not time out to UNKNOWN"
        );
        assert!(
            outcome.solution.assignment.is_empty(),
            "a refutation has no satisfying assignment"
        );
        assert!(outcome.solution.objective.is_none());
    }

    /// SOUNDNESS pin: the early recognizer set must DECLINE (return `false`) on a
    /// satisfiable instance, so a SAT instance can never be flipped to UNSAT.
    /// Also asserts it ACCEPTS a genuine pigeonhole refutation, and that the
    /// satisfiable instance still solves to `Satisfiable` through the native path.
    #[test]
    fn structural_unsat_self_checked_declines_satisfiable_and_accepts_pigeonhole() {
        // Trivially satisfiable decision instance (x1 + x2 >= 1).
        let sat = ay_pb::parse_opb(concat!(
            "* #variable= 2 #constraint= 1\n",
            "+1 x1 +1 x2 >= 1 ;\n",
        ))
        .expect("sat fixture should parse");
        assert!(
            !structural_unsat_self_checked(&sat),
            "structural recognizers must DECLINE a satisfiable instance (no SAT->UNSAT flip)"
        );

        // Genuine pigeonhole UNSAT is accepted (self-checked 0>=1).
        let unsat = ay_pb::parse_opb(&pigeonhole_opb(6)).expect("pigeonhole fixture should parse");
        assert!(
            structural_unsat_self_checked(&unsat),
            "structural recognizers must accept a self-checkable pigeonhole refutation"
        );

        // End-to-end: the satisfiable instance is still reported Satisfiable on
        // the native path (the early check did not steal the verdict).
        let term_flag = AtomicBool::new(false);
        let best_solution = Mutex::new(None);
        let mut output = Vec::new();
        let outcome = {
            let mut out = PbOutputWriter::new(&mut output);
            solve_pb(
                &ParsedPbInstance::Opb(Arc::new(sat)),
                None,
                Some(Duration::from_secs(2)),
                Instant::now(),
                /* native = */ true,
                false,
                &term_flag,
                &mut out,
                &best_solution,
                None,
            )
            .expect("native sat decision should solve")
        };
        assert_eq!(
            outcome.solution.status,
            PbStatus::Satisfiable,
            "a satisfiable instance must remain SATISFIABLE through the early-check path"
        );
    }

    #[test]
    fn structural_precheck_row_gate_is_fail_closed() {
        // A self-checkable pigeonhole refutation is accepted under the default
        // cap but DECLINED (fail-closed to "go search", never a wrong verdict)
        // when the instance exceeds the row-count gate.
        let unsat = ay_pb::parse_opb(&pigeonhole_opb(6)).expect("pigeonhole fixture should parse");
        assert!(
            structural_unsat_self_checked_with_cap(&unsat, STRUCTURAL_PRECHECK_MAX_ROWS),
            "below the cap the recognizer pass must still certify pigeonhole UNSAT"
        );
        let rows = unsat.constraints.len();
        assert!(
            rows > 1,
            "fixture must have enough rows to exceed a tiny cap"
        );
        assert!(
            !structural_unsat_self_checked_with_cap(&unsat, rows - 1),
            "above the cap the pass must decline (skip straight to search)"
        );
    }

    #[test]
    fn gf2_parity_certifies_above_the_row_gate() {
        // Review finding (wave 8): the GF(2) parity recognizer self-caps on
        // EQUALITY rows only, so a tiny parity-contradiction core padded with
        // arbitrarily many inequality rows must STILL certify UNSAT above the
        // structural row gate (the parity pass runs ungated by design).
        let mut opb = String::from("* #variable= 3 #constraint= 6\n");
        // Parity contradiction: x1 + x2 = 1, x1 + x2 = 2 (over GF(2): 1 vs 0).
        opb.push_str("+1 x1 +1 x2 = 1 ;\n+1 x1 +1 x2 = 2 ;\n");
        // Inequality padding past a tiny gate.
        for _ in 0..4 {
            opb.push_str("+1 x1 +1 x2 +1 x3 >= 0 ;\n");
        }
        let unsat = ay_pb::parse_opb(&opb).expect("parity fixture should parse");
        let rows = unsat.constraints.len();
        assert!(
            structural_unsat_self_checked_with_cap(&unsat, rows - 1),
            "a parity core must certify even when total rows exceed the gate"
        );
    }
}
