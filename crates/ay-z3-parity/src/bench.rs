// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bench` subcommand — a skeptic-proof differential benchmark campaign.
//!
//! Runs every `.smt2` file under one or more corpus roots through BOTH
//! libraries and reports, per division (= `<root-name>/<top-level-subdir>`):
//! agreement counts, unknown/timeout/crash counts, the sat-vs-unsat DISAGREE
//! count (must be 0; nonzero exit otherwise), and wall-clock ratio statistics
//! (median + geometric mean of AY/z3, decided-by-both files only) with >2x
//! win/loss counts.
//!
//! Isolation model: each (file, solver) pair is evaluated in a stopped-exec
//! child process group (the hidden `bench-one` mode). The campaign planner
//! caps parallel jobs, a zero-grace RSS watchdog is armed before exec, and
//! residual descendants are killed before the leader is reaped. This gives
//! crash/resource isolation, bounded hard timeouts, and honest eval-only wall
//! timing around `Z3_eval_smtlib2_string`.
//!
//! Outputs: a stdout table, a JSON certificate, and a markdown report with an
//! auto-populated "where z3 wins" section. Nothing is sampled or filtered:
//! every `.smt2` under every given root is run and accounted for.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime};

use ay_bench::{
    effective_execution_envelope, PlannedResources, ResourcePlan, ENFORCEMENT_AY_MEMORY_RSS_V1,
    ENFORCEMENT_RSS_WATCHDOG_V1,
};

use crate::diff::{has_error_response, verdicts_of, Verdict};
use crate::loader;

/// Minimum wall time (seconds) used when forming AY/z3 ratios, to keep timer
/// granularity on trivially fast files from fabricating huge ratios.
pub(crate) const RATIO_FLOOR_SECS: f64 = 0.0001; // 0.1 ms

/// A >2x speed win/loss is only counted when the SLOWER side took at least
/// this long; below it, both solvers are effectively instant and the ratio is
/// scheduling noise, so the file counts as a tie.
pub(crate) const WIN_LOSS_MIN_SECS: f64 = 0.010; // 10 ms

/// Grace period past the timeout before the child is SIGKILLed. The child
/// self-reports eval-only wall time; any result whose eval time exceeds the
/// budget is recorded as a timeout regardless of the grace.
pub(crate) const KILL_GRACE: Duration = Duration::from_secs(2);

pub(crate) fn hard_timeout(timeout: Duration) -> Result<Duration, String> {
    timeout
        .checked_add(KILL_GRACE)
        .ok_or_else(|| "child hard-timeout overflow".to_string())
}

pub(crate) fn resource_evidence(
    plan: &ResourcePlan,
    solver_timeout: Duration,
    include_selfcheck: bool,
) -> Result<serde_json::Value, String> {
    let hard_timeout = hard_timeout(solver_timeout)?;
    let hard_timeout_secs = hard_timeout.as_secs_f64();
    let ffi_envelope =
        effective_execution_envelope(plan, ENFORCEMENT_RSS_WATCHDOG_V1, hard_timeout_secs)
            .map_err(|error| error.to_string())?;
    let selfcheck = if include_selfcheck {
        let envelope =
            effective_execution_envelope(plan, ENFORCEMENT_AY_MEMORY_RSS_V1, hard_timeout_secs)
                .map_err(|error| error.to_string())?;
        Some(serde_json::json!({
            "enforcement": ENFORCEMENT_AY_MEMORY_RSS_V1,
            "execution_envelope": envelope,
        }))
    } else {
        None
    };
    Ok(serde_json::json!({
        "requested_jobs": plan.requested_jobs,
        "effective_jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb_per_child,
        "nbcore_per_child": plan.nbcore_per_child,
        "headroom_mb": plan.headroom_mb,
        "planner": plan.planner,
        "solver_timeout_secs": solver_timeout.as_secs_f64(),
        "hard_timeout_secs": hard_timeout_secs,
        "external_ffi": {
            "enforcement": ENFORCEMENT_RSS_WATCHDOG_V1,
            "execution_envelope": ffi_envelope,
        },
        "ay_selfcheck": selfcheck,
    }))
}

// ---------------------------------------------------------------------------
// Child mode: `bench-one <lib> <file>`
// ---------------------------------------------------------------------------

#[cfg(unix)]
fn process_peak_rss_bytes() -> Option<u64> {
    let mut usage = std::mem::MaybeUninit::<libc::rusage>::uninit();
    // SAFETY: `usage` points to writable storage for one `rusage`, and
    // `RUSAGE_SELF` asks the kernel to initialize it for this process.
    if unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) } != 0 {
        return None;
    }
    // SAFETY: a successful `getrusage` call initialized the complete value.
    let usage = unsafe { usage.assume_init() };
    let raw = u64::try_from(usage.ru_maxrss).ok()?;
    #[cfg(target_os = "macos")]
    {
        Some(raw)
    }
    #[cfg(not(target_os = "macos"))]
    {
        Some(raw.saturating_mul(1024))
    }
}

#[cfg(not(unix))]
fn process_peak_rss_bytes() -> Option<u64> {
    None
}

/// Child-process entry point. Loads ONE library, evaluates ONE script, and
/// prints strict wall-time and peak-RSS protocol headers followed by the
/// solver's raw output. The wall time covers exactly the
/// `Z3_eval_smtlib2_string` call.
///
/// Exit codes: 0 ok, 3 unreadable input, 4 library load failure, 5 solver
/// parser/API rejection. Any other termination (signal, abort) is observed by
/// the parent as a solver crash.
pub(crate) fn run_child(lib_path: &Path, file: &Path) -> i32 {
    let lib = match loader::open_local(lib_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("bench-one: {e}");
            return 4;
        }
    };
    let api = match loader::load_api(&lib) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("bench-one: {e}");
            return 4;
        }
    };
    let script = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("bench-one: read {}: {e}", file.display());
            return 3;
        }
    };
    let Ok(cscript) = std::ffi::CString::new(script) else {
        eprintln!(
            "bench-one: {} contains an interior NUL byte",
            file.display()
        );
        return 3;
    };

    // SAFETY: `api` holds valid function pointers into the library opened
    // above; each is called at its declared signature. The output string is
    // owned by the context and copied out before teardown.
    let (wall, out, error_code) = unsafe {
        let cfg = (api.mk_config)();
        let ctx = (api.mk_context)(cfg);
        // Keep unsupported syntax local to this child. libz3's default error
        // handler exits the process before we can distinguish a solver error
        // from a crash or reject any partial verdict text.
        (api.set_error_handler)(ctx, None);
        let t0 = Instant::now();
        let out_ptr = (api.eval)(ctx, cscript.as_ptr());
        let wall = t0.elapsed();
        let out = if out_ptr.is_null() {
            String::new()
        } else {
            std::ffi::CStr::from_ptr(out_ptr)
                .to_string_lossy()
                .into_owned()
        };
        let error_code = (api.get_error_code)(ctx);
        (api.del_context)(ctx);
        (api.del_config)(cfg);
        (wall, out, error_code)
    };
    if error_code != 0 || has_error_response(&out) {
        eprintln!("bench-one: solver rejected {}", file.display());
        return 5;
    }
    let peak_rss = process_peak_rss_bytes();
    let mut stdout = std::io::stdout();
    let _ = writeln!(stdout, "AYZ3_WALL_NS {}", wall.as_nanos());
    match peak_rss {
        Some(bytes) => {
            let _ = writeln!(stdout, "AYZ3_RSS_BYTES {bytes}");
        }
        None => {
            let _ = writeln!(stdout, "AYZ3_RSS_BYTES -");
        }
    }
    let _ = stdout.write_all(out.as_bytes());
    let _ = stdout.flush();
    0
}

// ---------------------------------------------------------------------------
// Parent-side outcome model
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub(crate) enum OutcomeKind {
    /// Ordered verdict tokens, one per `(check-sat)`.
    Verdicts(Vec<Verdict>),
    /// Exceeded the wall-clock budget (killed, or self-reported over budget).
    Timeout,
    /// Exceeded the campaign's enforced per-process-group RSS envelope.
    MemoryLimit,
    /// The solver process died (signal / abort / nonzero exit).
    Crash(String),
    /// The harness could not feed the file (unreadable / interior NUL).
    InputError(String),
}

#[derive(Clone, Debug)]
pub(crate) struct BenchOutcome {
    pub(crate) kind: OutcomeKind,
    /// Eval-only wall time as self-reported by the child; for timeouts this
    /// is clamped to the budget, for crashes it is the parent-observed span.
    pub(crate) wall: Duration,
    /// Peak resident set size of the child process (BYTES), self-reported from
    /// `getrusage(RUSAGE_SELF)` after successful solver teardown. `None` for a
    /// killed/failed child or a host without per-process `rusage`.
    pub(crate) peak_rss: Option<u64>,
}

impl BenchOutcome {
    pub(crate) fn label(&self) -> String {
        match &self.kind {
            OutcomeKind::Verdicts(v) if v.is_empty() => "-".to_string(),
            OutcomeKind::Verdicts(v) => v.iter().map(|x| x.as_str()).collect::<Vec<_>>().join(","),
            OutcomeKind::Timeout => "timeout".to_string(),
            OutcomeKind::MemoryLimit => "memout".to_string(),
            OutcomeKind::Crash(_) => "crash".to_string(),
            OutcomeKind::InputError(_) => "input-error".to_string(),
        }
    }

    /// Failure detail (crash signal / harness error), `None` for normal runs.
    pub(crate) fn detail(&self) -> Option<&str> {
        match &self.kind {
            OutcomeKind::Crash(d) | OutcomeKind::InputError(d) => Some(d.as_str()),
            _ => None,
        }
    }

    /// Decisive = produced at least one verdict and no `unknown`.
    pub(crate) fn decided(&self) -> bool {
        matches!(&self.kind, OutcomeKind::Verdicts(v)
            if !v.is_empty() && v.iter().all(|x| *x != Verdict::Unknown))
    }

    /// The single decisive verdict list, if decided. Used by the scoreboard to
    /// compare AY's self-check answer against AY's own eval answer.
    pub(crate) fn verdicts(&self) -> Option<&[Verdict]> {
        match &self.kind {
            OutcomeKind::Verdicts(v) if !v.is_empty() => Some(v),
            _ => None,
        }
    }

    /// Ran to completion but produced no verdict at all (typically an
    /// `(error ...)`-only output, e.g. an unsupported logic or command).
    pub(crate) fn no_verdict(&self) -> bool {
        matches!(&self.kind, OutcomeKind::Verdicts(v) if v.is_empty())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Category {
    AgreeSat,
    AgreeUnsat,
    /// Both produced the identical multi-check verdict list mixing sat+unsat.
    AgreeMixed,
    /// Verdict lists identical but contain at least one `unknown`.
    BothUnknown,
    /// AY answered `unknown` where z3 decided — AY incompleteness.
    AyUnknownZ3Decided,
    /// z3 answered `unknown` where AY decided — AY strictly stronger here.
    Z3UnknownAyDecided,
    TimeoutAy,
    TimeoutZ3,
    TimeoutBoth,
    MemoutAy,
    MemoutZ3,
    MemoutBoth,
    CrashAy,
    CrashZ3,
    CrashBoth,
    /// Count mismatch, no verdicts at all, or a harness-side input error.
    Other,
    /// `sat` vs `unsat` — a SOUNDNESS BUG. Must be zero.
    Disagree,
}

impl Category {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Category::AgreeSat => "AGREE-sat",
            Category::AgreeUnsat => "AGREE-unsat",
            Category::AgreeMixed => "AGREE-mixed",
            Category::BothUnknown => "BOTH-unknown",
            Category::AyUnknownZ3Decided => "AY-unknown-z3-decided",
            Category::Z3UnknownAyDecided => "Z3-unknown-ay-decided",
            Category::TimeoutAy => "TIMEOUT-ay",
            Category::TimeoutZ3 => "TIMEOUT-z3",
            Category::TimeoutBoth => "TIMEOUT-both",
            Category::MemoutAy => "MEMOUT-ay",
            Category::MemoutZ3 => "MEMOUT-z3",
            Category::MemoutBoth => "MEMOUT-both",
            Category::CrashAy => "CRASH-ay",
            Category::CrashZ3 => "CRASH-z3",
            Category::CrashBoth => "CRASH-both",
            Category::Other => "OTHER",
            Category::Disagree => "DISAGREE",
        }
    }
}

/// Classify one file's paired outcomes. Soundness first: any positional
/// sat-vs-unsat conflict is DISAGREE even if other checks also diverged.
pub(crate) fn categorize(ay: &BenchOutcome, z3: &BenchOutcome) -> Category {
    // Disagreement is only observable when both sides produced verdicts.
    if let (OutcomeKind::Verdicts(av), OutcomeKind::Verdicts(zv)) = (&ay.kind, &z3.kind) {
        for (a, z) in av.iter().zip(zv.iter()) {
            if matches!(
                (a, z),
                (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat)
            ) {
                return Category::Disagree;
            }
        }
    }
    match (&ay.kind, &z3.kind) {
        (OutcomeKind::InputError(_), _) | (_, OutcomeKind::InputError(_)) => {
            return Category::Other
        }
        (OutcomeKind::Crash(_), OutcomeKind::Crash(_)) => return Category::CrashBoth,
        (OutcomeKind::Crash(_), _) => return Category::CrashAy,
        (_, OutcomeKind::Crash(_)) => return Category::CrashZ3,
        (OutcomeKind::MemoryLimit, OutcomeKind::MemoryLimit) => return Category::MemoutBoth,
        (OutcomeKind::MemoryLimit, _) => return Category::MemoutAy,
        (_, OutcomeKind::MemoryLimit) => return Category::MemoutZ3,
        (OutcomeKind::Timeout, OutcomeKind::Timeout) => return Category::TimeoutBoth,
        (OutcomeKind::Timeout, _) => return Category::TimeoutAy,
        (_, OutcomeKind::Timeout) => return Category::TimeoutZ3,
        (OutcomeKind::Verdicts(_), OutcomeKind::Verdicts(_)) => {}
    }
    let (OutcomeKind::Verdicts(av), OutcomeKind::Verdicts(zv)) = (&ay.kind, &z3.kind) else {
        unreachable!("all non-verdict combinations returned above");
    };

    if av.is_empty() && zv.is_empty() {
        return Category::Other;
    }
    if av.len() != zv.len() {
        return Category::Other;
    }
    if av == zv {
        if av.iter().any(|v| *v == Verdict::Unknown) {
            return Category::BothUnknown;
        }
        let sat = av.iter().any(|v| *v == Verdict::Sat);
        let unsat = av.iter().any(|v| *v == Verdict::Unsat);
        return match (sat, unsat) {
            (true, false) => Category::AgreeSat,
            (false, true) => Category::AgreeUnsat,
            _ => Category::AgreeMixed,
        };
    }
    // Same length, no sat-vs-unsat conflict, not equal: unknowns on one or
    // both sides. AY incompleteness dominates the classification.
    let ay_unk = av
        .iter()
        .zip(zv.iter())
        .any(|(a, z)| *a == Verdict::Unknown && *z != Verdict::Unknown);
    if ay_unk {
        Category::AyUnknownZ3Decided
    } else {
        Category::Z3UnknownAyDecided
    }
}

// ---------------------------------------------------------------------------
// Running one (file, solver) pair in a child process
// ---------------------------------------------------------------------------

/// Raw result of running one child process under a hard timebox — the shared
/// plumbing behind both the `bench-one` runner and the scoreboard's `ay
/// solve --self-check` runner. Interpreting the exit code / stdout into a
/// verdict is left to the caller, since the two child protocols differ.
pub(crate) struct RawRun {
    /// True iff the child was SIGKILLed for exceeding the deadline.
    pub(crate) killed: bool,
    /// True iff the RSS watchdog terminated the process group.
    pub(crate) memout: bool,
    /// Exit code if the child exited normally; `None` if it died by signal.
    pub(crate) code: Option<i32>,
    /// Human-readable status (`exit status: N` / `signal: 6`) for messages.
    pub(crate) status_str: String,
    /// Everything the child wrote to stdout.
    pub(crate) stdout: Vec<u8>,
    /// Parent-observed wall time from spawn to reap (used as a fallback when
    /// the child does not self-report an eval time).
    pub(crate) observed: Duration,
    /// The child produced more stdout than the fixed one-MiB parent cap.
    pub(crate) output_truncated: bool,
    /// Set iff spawning or waiting on the child failed at the harness level
    /// (not the solver's fault).
    pub(crate) harness_error: Option<String>,
}

/// Run a stopped-exec child under the campaign's exact RSS watchdog and
/// bounded stdout capture. The watchdog-owned wait keeps the group leader
/// unreaped until residual descendants have been killed. Successful
/// `bench-one` children self-report peak RSS in their protocol header.
pub(crate) fn spawn_timeboxed(
    resources: &PlannedResources,
    program: &Path,
    args: &[OsString],
    timeout: Duration,
    label: &str,
) -> RawRun {
    let Ok(hard_timeout) = hard_timeout(timeout) else {
        return RawRun {
            killed: false,
            memout: false,
            code: None,
            status_str: String::new(),
            stdout: Vec::new(),
            observed: Duration::ZERO,
            output_truncated: false,
            harness_error: Some("child hard-timeout overflow".to_string()),
        };
    };
    match resources.run_external_captured(program, args, hard_timeout, label) {
        Ok(output) => {
            let code = output
                .status
                .as_ref()
                .and_then(std::process::ExitStatus::code);
            let status_str = output
                .status
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_default();
            RawRun {
                killed: output.timed_out,
                memout: output.memout,
                code,
                status_str,
                stdout: output.stdout,
                observed: output.observed,
                output_truncated: output.output_truncated,
                harness_error: None,
            }
        }
        Err(error) => RawRun {
            killed: false,
            memout: false,
            code: None,
            status_str: String::new(),
            stdout: Vec::new(),
            observed: Duration::ZERO,
            output_truncated: false,
            harness_error: Some(error.to_string()),
        },
    }
}

/// Spawn `bench-one` for one (library, file) pair with a hard timebox.
///
/// The child self-reports eval-only wall time on its first stdout line; a
/// result over budget is a timeout even if the child finished in the grace
/// window. A SIGKILLed child is a timeout; any other abnormal exit is a crash.
pub(crate) fn run_one(
    resources: &PlannedResources,
    exe: &Path,
    lib: &Path,
    file: &Path,
    timeout: Duration,
    label: &str,
) -> BenchOutcome {
    let args = [
        OsString::from("bench-one"),
        lib.as_os_str().to_owned(),
        file.as_os_str().to_owned(),
    ];
    let raw = spawn_timeboxed(resources, exe, &args, timeout, label);
    if let Some(err) = raw.harness_error {
        return BenchOutcome {
            kind: OutcomeKind::InputError(err),
            wall: raw.observed,
            peak_rss: None,
        };
    }
    if raw.output_truncated {
        return BenchOutcome {
            kind: OutcomeKind::InputError(
                "child stdout exceeded the fixed one-MiB capture limit".to_string(),
            ),
            wall: raw.observed,
            peak_rss: None,
        };
    }
    if raw.memout {
        return BenchOutcome {
            kind: OutcomeKind::MemoryLimit,
            wall: raw.observed.min(timeout),
            peak_rss: None,
        };
    }
    if raw.killed {
        return BenchOutcome {
            kind: OutcomeKind::Timeout,
            wall: timeout,
            peak_rss: None,
        };
    }
    let text = String::from_utf8_lossy(&raw.stdout);
    match raw.code {
        Some(0) => {
            let parsed = match parse_bench_child_output(&text) {
                Ok(parsed) => parsed,
                Err(error) => {
                    return BenchOutcome {
                        kind: OutcomeKind::InputError(error),
                        wall: raw.observed,
                        peak_rss: None,
                    };
                }
            };
            let wall = parsed.wall;
            if wall > timeout {
                // Finished inside the kill grace but over budget: a timeout.
                BenchOutcome {
                    kind: OutcomeKind::Timeout,
                    wall: timeout,
                    peak_rss: None,
                }
            } else {
                BenchOutcome {
                    kind: OutcomeKind::Verdicts(verdicts_of(parsed.solver_output)),
                    wall,
                    peak_rss: parsed.peak_rss,
                }
            }
        }
        Some(3) | Some(4) | Some(5) => BenchOutcome {
            kind: OutcomeKind::InputError(format!("bench-one exited {}", raw.status_str)),
            wall: raw.observed,
            peak_rss: None,
        },
        Some(code) => BenchOutcome {
            kind: OutcomeKind::Crash(format!("exit code {code}")),
            wall: raw.observed,
            peak_rss: None,
        },
        None => BenchOutcome {
            kind: OutcomeKind::Crash(format!("killed by signal ({})", raw.status_str)),
            wall: raw.observed,
            peak_rss: None,
        },
    }
}

struct BenchChildOutput<'a> {
    wall: Duration,
    peak_rss: Option<u64>,
    solver_output: &'a str,
}

fn parse_bench_child_output(text: &str) -> Result<BenchChildOutput<'_>, String> {
    let mut fields = text.splitn(3, '\n');
    let wall_ns = fields
        .next()
        .and_then(|line| line.strip_prefix("AYZ3_WALL_NS "))
        .ok_or_else(|| "bench-one omitted its wall-time protocol header".to_string())?
        .parse::<u64>()
        .map_err(|_| "bench-one emitted an invalid wall-time protocol header".to_string())?;
    let rss_field = fields
        .next()
        .and_then(|line| line.strip_prefix("AYZ3_RSS_BYTES "))
        .ok_or_else(|| "bench-one omitted its peak-RSS protocol header".to_string())?;
    let peak_rss = if rss_field == "-" {
        None
    } else {
        let bytes = rss_field
            .parse::<u64>()
            .map_err(|_| "bench-one emitted an invalid peak-RSS protocol header".to_string())?;
        if bytes == 0 {
            return Err("bench-one emitted a zero peak-RSS measurement".to_string());
        }
        Some(bytes)
    };
    let solver_output = fields
        .next()
        .ok_or_else(|| "bench-one omitted its solver-output protocol separator".to_string())?;
    Ok(BenchChildOutput {
        wall: Duration::from_nanos(wall_ns),
        peak_rss,
        solver_output,
    })
}

/// AY's fail-closed self-certification verdict for one file, obtained by
/// running the `ay` CLI binary as `ay solve --self-check <file>` in a fresh,
/// timeboxed child (same isolation as [`run_one`]). AY emits `sat`/`unsat`
/// only when its own in-tree checker confirms the answer, else `unknown`; the
/// scoreboard reads these tokens straight from stdout.
#[derive(Clone, Debug)]
pub(crate) enum SelfCheck {
    /// Verdict tokens parsed from AY's stdout (may be empty or contain
    /// `unknown` — both mean "not self-certified").
    Verdicts(Vec<Verdict>),
    /// Exceeded the wall-clock budget.
    Timeout,
    /// Exceeded the enforced process-group RSS budget.
    MemoryLimit,
    /// The `ay` process died by signal with no usable verdict.
    Crash(String),
    /// The harness could not spawn/await the `ay` binary at all.
    Error(String),
}

impl SelfCheck {
    /// Failure detail (crash signal / harness error), `None` otherwise.
    pub(crate) fn detail(&self) -> Option<&str> {
        match self {
            SelfCheck::Crash(d) | SelfCheck::Error(d) => Some(d.as_str()),
            _ => None,
        }
    }

    /// The decisive verdict list, if self-certified.
    pub(crate) fn verdicts(&self) -> Option<&[Verdict]> {
        match self {
            SelfCheck::Verdicts(v) if !v.is_empty() && v.iter().all(|x| *x != Verdict::Unknown) => {
                Some(v)
            }
            _ => None,
        }
    }

    pub(crate) fn label(&self) -> String {
        match self {
            SelfCheck::Verdicts(v) if v.is_empty() => "-".to_string(),
            SelfCheck::Verdicts(v) => v.iter().map(|x| x.as_str()).collect::<Vec<_>>().join(","),
            SelfCheck::Timeout => "timeout".to_string(),
            SelfCheck::MemoryLimit => "memout".to_string(),
            SelfCheck::Crash(_) => "crash".to_string(),
            SelfCheck::Error(_) => "error".to_string(),
        }
    }
}

/// Extract self-check verdict tokens from the `ay` CLI's stdout. Unlike the
/// FFI eval, the CLI interleaves `c `-prefixed comment lines (e.g.
/// `c writing Alethe proof ... on unsat`) and `(:reason-unknown ...)` s-exprs
/// that would poison a whole-blob token scan, so we match ONLY lines whose
/// trimmed content is exactly a verdict token — the shape a check-sat answer
/// actually prints on.
fn selfcheck_verdicts(output: &str) -> Vec<Verdict> {
    output
        .lines()
        .filter_map(|l| match l.trim() {
            "sat" => Some(Verdict::Sat),
            "unsat" => Some(Verdict::Unsat),
            "unknown" => Some(Verdict::Unknown),
            _ => None,
        })
        .collect()
}

/// Run `ay solve --self-check --competition <file>` in a timeboxed child and
/// read AY's self-certification verdict from stdout.
///
/// `--competition` keeps the fail-closed `--self-check` gate and every
/// soundness default, but turns OFF the redundant runtime validation, the
/// post-solve proof re-check, and — crucially — the default proof-certificate
/// emission, so the run neither wastes time nor writes `*.alethe` artifacts
/// into the corpus directory next to each input.
pub(crate) fn run_selfcheck(
    resources: &PlannedResources,
    ay_cli: &Path,
    file: &Path,
    timeout: Duration,
) -> SelfCheck {
    let args = [
        OsString::from("solve"),
        OsString::from("--self-check"),
        OsString::from("--competition"),
        OsString::from("--memory"),
        OsString::from(resources.plan.memlimit_mb_per_child.to_string()),
        file.as_os_str().to_owned(),
    ];
    interpret_selfcheck_raw(
        spawn_timeboxed(resources, ay_cli, &args, timeout, "ay-z3-parity self-check"),
        timeout,
    )
}

fn interpret_selfcheck_raw(raw: RawRun, timeout: Duration) -> SelfCheck {
    if let Some(err) = raw.harness_error {
        return SelfCheck::Error(err);
    }
    if raw.output_truncated {
        return SelfCheck::Error(
            "self-check stdout exceeded the fixed one-MiB capture limit".to_string(),
        );
    }
    if raw.memout {
        return SelfCheck::MemoryLimit;
    }
    if raw.killed || raw.observed > timeout {
        return SelfCheck::Timeout;
    }
    match raw.code {
        Some(0) => {}
        Some(code) => {
            return SelfCheck::Error(format!("ay solve exited {code} ({})", raw.status_str));
        }
        None => {
            return SelfCheck::Crash(format!("killed by signal ({})", raw.status_str));
        }
    }
    let text = String::from_utf8_lossy(&raw.stdout);
    SelfCheck::Verdicts(selfcheck_verdicts(&text))
}

// ---------------------------------------------------------------------------
// Corpus collection and division mapping
// ---------------------------------------------------------------------------

/// Division of a file relative to its corpus root:
/// `<root-name>/<top-level-subdir>`, or `<root-name>/(top)` for files sitting
/// directly in the root.
fn division_of(root: &Path, file: &Path) -> String {
    let root_name = root
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("corpus");
    let sub = file
        .strip_prefix(root)
        .ok()
        .and_then(|rel| {
            let mut comps = rel.components();
            let first = comps.next()?;
            // Only a subdirectory (i.e. the file is deeper) names a division.
            comps.next()?;
            first.as_os_str().to_str().map(str::to_string)
        })
        .unwrap_or_else(|| "(top)".to_string());
    format!("{root_name}/{sub}")
}

/// Recursively collect `.smt2` files under each root, tagged with divisions.
fn collect(roots: &[PathBuf]) -> Vec<(String, PathBuf)> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        if dir.is_dir() {
            if let Ok(entries) = std::fs::read_dir(dir) {
                for e in entries.flatten() {
                    walk(&e.path(), out);
                }
            }
        } else if dir.extension().and_then(|e| e.to_str()) == Some("smt2") {
            out.push(dir.to_path_buf());
        }
    }
    let mut tagged = Vec::new();
    for root in roots {
        let mut files = Vec::new();
        walk(root, &mut files);
        files.sort();
        for f in files {
            tagged.push((division_of(root, &f), f));
        }
    }
    tagged
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

struct FileRecord {
    division: String,
    file: PathBuf,
    ay: BenchOutcome,
    z3: BenchOutcome,
    category: Category,
    /// AY/z3 wall ratio, present iff decided-by-both (floored at
    /// [`RATIO_FLOOR_SECS`] on both sides).
    ratio: Option<f64>,
}

#[derive(Default)]
struct DivStats {
    files: usize,
    agree_sat: usize,
    agree_unsat: usize,
    agree_mixed: usize,
    both_unknown: usize,
    ay_unknown: usize,
    z3_unknown: usize,
    timeout_ay: usize,
    timeout_z3: usize,
    timeout_both: usize,
    memout_ay: usize,
    memout_z3: usize,
    memout_both: usize,
    crash_ay: usize,
    crash_z3: usize,
    crash_both: usize,
    other: usize,
    disagree: usize,
    ratios: Vec<f64>,
    ay_wins_2x: usize,
    z3_wins_2x: usize,
}

impl DivStats {
    fn add(&mut self, r: &FileRecord) {
        self.files += 1;
        match r.category {
            Category::AgreeSat => self.agree_sat += 1,
            Category::AgreeUnsat => self.agree_unsat += 1,
            Category::AgreeMixed => self.agree_mixed += 1,
            Category::BothUnknown => self.both_unknown += 1,
            Category::AyUnknownZ3Decided => self.ay_unknown += 1,
            Category::Z3UnknownAyDecided => self.z3_unknown += 1,
            Category::TimeoutAy => self.timeout_ay += 1,
            Category::TimeoutZ3 => self.timeout_z3 += 1,
            Category::TimeoutBoth => self.timeout_both += 1,
            Category::MemoutAy => self.memout_ay += 1,
            Category::MemoutZ3 => self.memout_z3 += 1,
            Category::MemoutBoth => self.memout_both += 1,
            Category::CrashAy => self.crash_ay += 1,
            Category::CrashZ3 => self.crash_z3 += 1,
            Category::CrashBoth => self.crash_both += 1,
            Category::Other => self.other += 1,
            Category::Disagree => self.disagree += 1,
        }
        if let Some(ratio) = r.ratio {
            self.ratios.push(ratio);
            let slower = r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64());
            if slower >= WIN_LOSS_MIN_SECS {
                if ratio < 0.5 {
                    self.ay_wins_2x += 1;
                } else if ratio > 2.0 {
                    self.z3_wins_2x += 1;
                }
            }
        }
    }

    fn merge(&mut self, o: &DivStats) {
        self.files += o.files;
        self.agree_sat += o.agree_sat;
        self.agree_unsat += o.agree_unsat;
        self.agree_mixed += o.agree_mixed;
        self.both_unknown += o.both_unknown;
        self.ay_unknown += o.ay_unknown;
        self.z3_unknown += o.z3_unknown;
        self.timeout_ay += o.timeout_ay;
        self.timeout_z3 += o.timeout_z3;
        self.timeout_both += o.timeout_both;
        self.memout_ay += o.memout_ay;
        self.memout_z3 += o.memout_z3;
        self.memout_both += o.memout_both;
        self.crash_ay += o.crash_ay;
        self.crash_z3 += o.crash_z3;
        self.crash_both += o.crash_both;
        self.other += o.other;
        self.disagree += o.disagree;
        self.ratios.extend_from_slice(&o.ratios);
        self.ay_wins_2x += o.ay_wins_2x;
        self.z3_wins_2x += o.z3_wins_2x;
    }
}

pub(crate) fn median(sorted: &[f64]) -> Option<f64> {
    if sorted.is_empty() {
        return None;
    }
    let n = sorted.len();
    Some(if n % 2 == 1 {
        sorted[n / 2]
    } else {
        f64::midpoint(sorted[n / 2 - 1], sorted[n / 2])
    })
}

pub(crate) fn geomean(values: &[f64]) -> Option<f64> {
    if values.is_empty() {
        return None;
    }
    let sum: f64 = values.iter().map(|v| v.ln()).sum();
    Some((sum / values.len() as f64).exp())
}

pub(crate) fn ratio_of(ay: &BenchOutcome, z3: &BenchOutcome) -> f64 {
    let a = ay.wall.as_secs_f64().max(RATIO_FLOOR_SECS);
    let z = z3.wall.as_secs_f64().max(RATIO_FLOOR_SECS);
    a / z
}

pub(crate) fn fmt_ratio(r: Option<f64>) -> String {
    match r {
        None => "-".to_string(),
        Some(v) if v >= 100.0 => format!("{v:.0}"),
        Some(v) => format!("{v:.2}"),
    }
}

pub(crate) fn fmt_ms(d: Duration) -> String {
    format!("{:.1}", d.as_secs_f64() * 1000.0)
}

// ---------------------------------------------------------------------------
// Certificate metadata helpers
// ---------------------------------------------------------------------------

/// A benchmark's OWN `(set-info :status ...)` annotation — ground truth that
/// depends on neither solver.
///
/// This is the only oracle available when the reference solver fails to decide
/// a file, so it is what keeps a z3 timeout from laundering a wrong AY answer
/// into an unchallenged "beyond z3" win.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum DeclaredStatus {
    Sat,
    Unsat,
    /// The file declares `unknown`, or declares two DIFFERENT statuses (a
    /// self-contradicting benchmark is no oracle either). Declared, but
    /// unusable as ground truth.
    Unknown,
    /// No `(set-info :status ...)` at all — deliberately distinct from a
    /// declared `unknown`, because "nobody stated an answer" and "the author
    /// stated they do not know" are different pieces of evidence.
    Absent,
}

impl DeclaredStatus {
    /// The JSON / table token. All four states are distinguishable.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            DeclaredStatus::Sat => "sat",
            DeclaredStatus::Unsat => "unsat",
            DeclaredStatus::Unknown => "unknown",
            DeclaredStatus::Absent => "absent",
        }
    }

    /// The oracle verdict this file supplies, if it supplies one at all.
    pub(crate) fn decided(self) -> Option<Verdict> {
        match self {
            DeclaredStatus::Sat => Some(Verdict::Sat),
            DeclaredStatus::Unsat => Some(Verdict::Unsat),
            DeclaredStatus::Unknown | DeclaredStatus::Absent => None,
        }
    }
}

/// Can `c` continue an SMT-LIB simple symbol (and therefore a keyword)? Used to
/// require that a `:status` keyword ENDS where it is found, so `:status-bits`
/// is never read as `:status`.
fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c)
}

/// Parse a benchmark's own `(set-info :status sat|unsat|unknown)` annotation.
///
/// Lexer-accurate rather than a substring search: `;` comments, `|quoted
/// symbols|`, and `"string literals"` are skipped. SMT-LIB benchmarks routinely
/// carry a `(set-info :source | ... |)` blob of prose, and taking the FIRST
/// `:status` in the raw bytes reads such prose as the answer. Every real
/// annotation is collected; if two of them disagree the file declares nothing
/// usable ([`DeclaredStatus::Unknown`]) rather than accusing a solver on a coin
/// flip.
pub(crate) fn parse_declared_status(text: &str) -> DeclaredStatus {
    const KEYWORD: &str = ":status";
    let bytes = text.as_bytes();
    let mut found: Option<DeclaredStatus> = None;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            // Comment: skip to end of line.
            b';' => {
                i += bytes[i..]
                    .iter()
                    .position(|b| *b == b'\n')
                    .unwrap_or(bytes.len() - i);
            }
            // |quoted symbol| — the shape of a (set-info :source | ... |) blob.
            b'|' => {
                i += 1;
                i += bytes[i..]
                    .iter()
                    .position(|b| *b == b'|')
                    .map_or(bytes.len() - i, |n| n + 1);
            }
            // "string literal", in which "" is an escaped quote (SMT-LIB 2.6).
            b'"' => {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        i += 1;
                        if bytes.get(i) != Some(&b'"') {
                            break;
                        }
                    }
                    i += 1;
                }
            }
            // `:` is ASCII, so `text[i..]` is always on a char boundary here.
            b':' if text[i..].starts_with(KEYWORD) => {
                i += KEYWORD.len();
                let rest = &text[i..];
                if rest.starts_with(is_symbol_char) {
                    continue; // a longer keyword, e.g. `:status-bits`
                }
                let token = rest
                    .trim_start()
                    .split(|c: char| c.is_whitespace() || "()|\";".contains(c))
                    .next()
                    .unwrap_or_default();
                let declared = match token {
                    "sat" => Some(DeclaredStatus::Sat),
                    "unsat" => Some(DeclaredStatus::Unsat),
                    "unknown" => Some(DeclaredStatus::Unknown),
                    // Not a status we can read; contribute no judgement.
                    _ => None,
                };
                if let Some(d) = declared {
                    found = Some(match found {
                        None => d,
                        Some(prev) if prev == d => d,
                        Some(_) => DeclaredStatus::Unknown,
                    });
                }
            }
            _ => i += 1,
        }
    }
    found.unwrap_or(DeclaredStatus::Absent)
}

/// Declared `:status` of a benchmark file. An unreadable file declares nothing;
/// invalid UTF-8 is read lossily rather than discarded, so one stray byte deep
/// in a benchmark cannot hide its `:status` header.
pub(crate) fn declared_status_of_file(file: &Path) -> DeclaredStatus {
    match std::fs::read(file) {
        Ok(bytes) => parse_declared_status(&String::from_utf8_lossy(&bytes)),
        Err(_) => DeclaredStatus::Absent,
    }
}

/// Declared `:status` token of a benchmark file, `None` when unannotated.
pub(crate) fn declared_status(file: &Path) -> Option<String> {
    match declared_status_of_file(file) {
        DeclaredStatus::Absent => None,
        declared => Some(declared.as_str().to_string()),
    }
}

/// SHA-256 of a file via the system `shasum`/`sha256sum` tool — re-runnable
/// by any auditor with the same command.
pub(crate) fn sha256_of(path: &Path) -> Option<String> {
    for (cmd, args) in [("shasum", vec!["-a", "256"]), ("sha256sum", vec![])] {
        let out = Command::new(cmd).args(&args).arg(path).output();
        if let Ok(out) = out {
            if out.status.success() {
                let text = String::from_utf8_lossy(&out.stdout);
                if let Some(tok) = text.split_whitespace().next() {
                    return Some(tok.to_string());
                }
            }
        }
    }
    None
}

/// UTC timestamp `YYYY-MM-DDTHH:MM:SSZ` from the system clock (Howard
/// Hinnant's civil-from-days algorithm; no chrono dependency).
pub(crate) fn utc_now_iso() -> String {
    let secs = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (h, m, s) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let mo = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if mo <= 2 { y + 1 } else { y };
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{m:02}:{s:02}Z")
}

pub(crate) fn host_info() -> serde_json::Value {
    let cpu = Command::new("sysctl")
        .args(["-n", "machdep.cpu.brand_string"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());
    serde_json::json!({
        "os": std::env::consts::OS,
        "arch": std::env::consts::ARCH,
        "cpu": cpu,
        "logical_cores": std::thread::available_parallelism().map(usize::from).ok(),
    })
}

// ---------------------------------------------------------------------------
// Campaign driver
// ---------------------------------------------------------------------------

pub(crate) struct BenchConfig {
    pub ay: PathBuf,
    pub z3: PathBuf,
    pub roots: Vec<PathBuf>,
    pub timeout_secs: u64,
    pub jobs: usize,
    pub json_stdout: bool,
    pub json_out: PathBuf,
    pub report_out: PathBuf,
}

pub(crate) fn run(cfg: &BenchConfig) -> i32 {
    let files = collect(&cfg.roots);
    if files.is_empty() {
        eprintln!("error: no .smt2 files found under {:?}", cfg.roots);
        return 2;
    }
    let exe = match std::env::current_exe() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: cannot locate own executable for child mode: {e}");
            return 2;
        }
    };

    // Preflight: both libraries must load and expose the eval entry points,
    // and we capture their self-reported versions for the certificate.
    let mut versions = Vec::new();
    for (label, path) in [("AY", &cfg.ay), ("z3", &cfg.z3)] {
        match loader::open_local(path) {
            Ok(lib) => {
                if let Err(e) = loader::load_api(&lib) {
                    eprintln!("error ({label} lib): {e}");
                    return 2;
                }
                versions.push(loader::full_version(&lib));
            }
            Err(e) => {
                eprintln!("error ({label} lib): {e}");
                return 2;
            }
        }
    }
    let (ay_version, z3_version) = (versions[0].clone(), versions[1].clone());

    let timeout = Duration::from_secs(cfg.timeout_secs);
    let resources = match PlannedResources::plan(
        &ay_bench::runner::repo_root_public(),
        cfg.jobs,
        "ay-z3-parity bench",
    ) {
        Ok(resources) => resources,
        Err(error) => {
            eprintln!("error: resource planning failed: {error}");
            return 2;
        }
    };
    let resource_evidence = match resource_evidence(&resources.plan, timeout, false) {
        Ok(evidence) => evidence,
        Err(error) => {
            eprintln!("error: resource envelope failed: {error}");
            return 2;
        }
    };
    let total = files.len();
    eprintln!(
        "bench: {total} files, timeout {}s, jobs requested/effective {}/{}, memory {}MiB/child, NBCORE {}, AY={} z3={}",
        cfg.timeout_secs,
        cfg.jobs,
        resources.plan.jobs,
        resources.plan.memlimit_mb_per_child,
        resources.plan.nbcore_per_child,
        cfg.ay.display(),
        cfg.z3.display()
    );

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let slots: Mutex<Vec<Option<FileRecord>>> = Mutex::new((0..total).map(|_| None).collect());
    let campaign_t0 = Instant::now();

    std::thread::scope(|scope| {
        for _ in 0..resources.plan.jobs {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= total {
                    break;
                }
                let (division, file) = &files[i];
                let z3 = run_one(
                    &resources,
                    &exe,
                    &cfg.z3,
                    file,
                    timeout,
                    "ay-z3-parity bench z3",
                );
                let ay = run_one(
                    &resources,
                    &exe,
                    &cfg.ay,
                    file,
                    timeout,
                    "ay-z3-parity bench AY",
                );
                let category = categorize(&ay, &z3);
                let ratio = matches!(
                    category,
                    Category::AgreeSat | Category::AgreeUnsat | Category::AgreeMixed
                )
                .then(|| ratio_of(&ay, &z3));
                let n_done = done.fetch_add(1, Ordering::Relaxed) + 1;
                eprintln!(
                    "[{n_done}/{total}] {} {}: z3={} ({}ms) ay={} ({}ms) {}",
                    division,
                    file.file_name().and_then(|n| n.to_str()).unwrap_or("?"),
                    z3.label(),
                    fmt_ms(z3.wall),
                    ay.label(),
                    fmt_ms(ay.wall),
                    category.label()
                );
                slots.lock().expect("slots poisoned")[i] = Some(FileRecord {
                    division: division.clone(),
                    file: file.clone(),
                    ay,
                    z3,
                    category,
                    ratio,
                });
            });
        }
    });

    let records: Vec<FileRecord> = slots
        .into_inner()
        .expect("slots poisoned")
        .into_iter()
        .flatten()
        .collect();
    let campaign_wall = campaign_t0.elapsed();

    let mut divisions: BTreeMap<String, DivStats> = BTreeMap::new();
    for r in &records {
        divisions.entry(r.division.clone()).or_default().add(r);
    }
    let mut totals = DivStats::default();
    for stats in divisions.values() {
        totals.merge(stats);
    }

    // ---- stdout table ----
    let table = render_table(&divisions, &totals);
    if !cfg.json_stdout {
        println!("== ay-z3-parity bench: differential campaign ==");
        println!(
            "  under test (AY):  {}  [{}]",
            cfg.ay.display(),
            ay_version.as_deref().unwrap_or("?")
        );
        println!(
            "  reference (z3):   {}  [{}]",
            cfg.z3.display(),
            z3_version.as_deref().unwrap_or("?")
        );
        println!(
            "  timeout {}s | jobs requested/effective {}/{} | memory {}MiB/child | NBCORE {} | campaign wall {:.1}s",
            cfg.timeout_secs,
            cfg.jobs,
            resources.plan.jobs,
            resources.plan.memlimit_mb_per_child,
            resources.plan.nbcore_per_child,
            campaign_wall.as_secs_f64()
        );
        println!();
        println!("{table}");
    }

    // ---- JSON certificate ----
    let cert = build_certificate(
        cfg,
        &records,
        &divisions,
        &totals,
        ay_version.as_deref(),
        z3_version.as_deref(),
        campaign_wall,
        &resources.plan,
        &resource_evidence,
    );
    let cert_text = serde_json::to_string_pretty(&cert).unwrap_or_default();
    if let Some(dir) = cfg.json_out.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    if let Err(e) = std::fs::write(&cfg.json_out, &cert_text) {
        eprintln!("error: writing {}: {e}", cfg.json_out.display());
        return 2;
    }
    if cfg.json_stdout {
        println!("{cert_text}");
    }

    // ---- markdown report ----
    let report = render_report(
        cfg,
        &records,
        &divisions,
        &totals,
        ay_version.as_deref(),
        z3_version.as_deref(),
        campaign_wall,
        &resources.plan,
        &resource_evidence,
    );
    if let Some(dir) = cfg.report_out.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    if let Err(e) = std::fs::write(&cfg.report_out, report) {
        eprintln!("error: writing {}: {e}", cfg.report_out.display());
        return 2;
    }

    if !cfg.json_stdout {
        println!();
        println!("certificate: {}", cfg.json_out.display());
        println!("report:      {}", cfg.report_out.display());
        println!();
        if totals.disagree == 0 {
            println!(
                "RESULT: PASS — 0 sat-vs-unsat disagreements across {} files.",
                totals.files
            );
        } else {
            println!(
                "RESULT: FAIL — {} SOUNDNESS DISAGREEMENT(S):",
                totals.disagree
            );
            for r in records.iter().filter(|r| r.category == Category::Disagree) {
                println!(
                    "    {}  declared={} z3={} ay={}",
                    r.file.display(),
                    declared_status(&r.file).unwrap_or_else(|| "(none)".into()),
                    r.z3.label(),
                    r.ay.label()
                );
            }
        }
    }

    i32::from(totals.disagree != 0)
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

fn stats_row(name: &str, s: &DivStats) -> Vec<String> {
    let mut sorted = s.ratios.clone();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("no NaN ratios"));
    vec![
        name.to_string(),
        s.files.to_string(),
        s.agree_sat.to_string(),
        s.agree_unsat.to_string(),
        s.agree_mixed.to_string(),
        s.both_unknown.to_string(),
        s.ay_unknown.to_string(),
        s.z3_unknown.to_string(),
        format!("{}/{}/{}", s.timeout_ay, s.timeout_z3, s.timeout_both),
        format!("{}/{}/{}", s.memout_ay, s.memout_z3, s.memout_both),
        format!(
            "{}/{}",
            s.crash_ay + s.crash_both,
            s.crash_z3 + s.crash_both
        ),
        s.other.to_string(),
        s.disagree.to_string(),
        fmt_ratio(median(&sorted)),
        fmt_ratio(geomean(&s.ratios)),
        format!("{}/{}", s.ay_wins_2x, s.z3_wins_2x),
    ]
}

const HEADERS: [&str; 16] = [
    "DIVISION",
    "FILES",
    "A-SAT",
    "A-UNSAT",
    "A-MIX",
    "BOTH-UNK",
    "AY-UNK",
    "Z3-UNK",
    "T/O a/z/b",
    "MEM a/z/b",
    "CRASH a/z",
    "OTHER",
    "DISAGREE",
    "MED ay/z3",
    "GEO ay/z3",
    "W/L 2x",
];

fn render_table(divisions: &BTreeMap<String, DivStats>, totals: &DivStats) -> String {
    let mut rows: Vec<Vec<String>> = vec![HEADERS.iter().map(|h| h.to_string()).collect()];
    for (name, s) in divisions {
        rows.push(stats_row(name, s));
    }
    rows.push(stats_row("TOTAL", totals));

    let cols = HEADERS.len();
    let mut widths = vec![0usize; cols];
    for row in &rows {
        for (i, cell) in row.iter().enumerate() {
            widths[i] = widths[i].max(cell.len());
        }
    }
    let mut out = String::new();
    for (ri, row) in rows.iter().enumerate() {
        let line: Vec<String> = row
            .iter()
            .enumerate()
            .map(|(i, cell)| {
                if i == 0 {
                    format!("{cell:<width$}", width = widths[i])
                } else {
                    format!("{cell:>width$}", width = widths[i])
                }
            })
            .collect();
        out.push_str(line.join("  ").trim_end());
        out.push('\n');
        // Rule under the header and above the TOTAL row.
        if ri == 0 || ri + 2 == rows.len() {
            out.push_str(&"-".repeat(widths.iter().sum::<usize>() + 2 * (cols - 1)));
            out.push('\n');
        }
    }
    out
}

fn md_row(cells: &[String]) -> String {
    format!("| {} |", cells.join(" | "))
}

fn build_certificate(
    cfg: &BenchConfig,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
    ay_version: Option<&str>,
    z3_version: Option<&str>,
    campaign_wall: Duration,
    resource_plan: &ResourcePlan,
    resource_evidence: &serde_json::Value,
) -> serde_json::Value {
    let div_json = |name: &str, s: &DivStats| {
        let mut sorted = s.ratios.clone();
        sorted.sort_by(|a, b| a.partial_cmp(b).expect("no NaN ratios"));
        serde_json::json!({
            "name": name,
            "files": s.files,
            "agree_sat": s.agree_sat,
            "agree_unsat": s.agree_unsat,
            "agree_mixed": s.agree_mixed,
            "both_unknown": s.both_unknown,
            "ay_unknown_z3_decided": s.ay_unknown,
            "z3_unknown_ay_decided": s.z3_unknown,
            "timeout_ay": s.timeout_ay,
            "timeout_z3": s.timeout_z3,
            "timeout_both": s.timeout_both,
            "memout_ay": s.memout_ay,
            "memout_z3": s.memout_z3,
            "memout_both": s.memout_both,
            "crash_ay": s.crash_ay,
            "crash_z3": s.crash_z3,
            "crash_both": s.crash_both,
            "other": s.other,
            "disagree": s.disagree,
            "decided_by_both": s.ratios.len(),
            "median_wall_ratio_ay_over_z3": median(&sorted),
            "geomean_wall_ratio_ay_over_z3": geomean(&s.ratios),
            "ay_wins_2x": s.ay_wins_2x,
            "z3_wins_2x": s.z3_wins_2x,
        })
    };
    let files_json: Vec<_> = records
        .iter()
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                "division": r.division,
                "z3": { "outcome": r.z3.label(), "wall_ms": r.z3.wall.as_secs_f64() * 1000.0, "peak_rss_bytes": r.z3.peak_rss, "detail": r.z3.detail() },
                "ay": { "outcome": r.ay.label(), "wall_ms": r.ay.wall.as_secs_f64() * 1000.0, "peak_rss_bytes": r.ay.peak_rss, "detail": r.ay.detail() },
                "category": r.category.label(),
                "wall_ratio_ay_over_z3": r.ratio,
            })
        })
        .collect();
    let disagree_files: Vec<serde_json::Value> = records
        .iter()
        .filter(|r| r.category == Category::Disagree)
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                "z3": r.z3.label(),
                "ay": r.ay.label(),
                "declared_status": declared_status(&r.file),
            })
        })
        .collect();
    serde_json::json!({
        "kind": "ay-z3-bench-certificate",
        "format_version": 2,
        "generated_utc": utc_now_iso(),
        "invocation": std::env::args().collect::<Vec<_>>().join(" "),
        "host": host_info(),
        "ay_lib": {
            "path": cfg.ay.display().to_string(),
            "sha256": sha256_of(&cfg.ay),
            "full_version": ay_version,
        },
        "z3_lib": {
            "path": cfg.z3.display().to_string(),
            "sha256": sha256_of(&cfg.z3),
            "full_version": z3_version,
        },
        "timeout_secs": cfg.timeout_secs,
        "jobs": resource_plan.jobs,
        "requested_jobs": resource_plan.requested_jobs,
        "resource": resource_evidence,
        "roots": cfg.roots.iter().map(|r| r.display().to_string()).collect::<Vec<_>>(),
        "campaign_wall_secs": campaign_wall.as_secs_f64(),
        "methodology": {
            "isolation": "each (file, solver) pair runs in a stopped-exec child process group; the campaign RSS watchdog arms before exec, residual descendants are killed before the leader is reaped, and stdout retention is capped at one MiB",
            "timeout": "hard process-group SIGKILL at timeout + 2s grace; any eval wall over the budget is recorded as timeout",
            "memory": "zero-grace RSS watchdog enforces the persisted per-child process-group envelope; memout is distinct from timeout/crash",
            "peak_rss": "each successful bench-one child self-reports getrusage(RUSAGE_SELF).ru_maxrss in bytes after solver teardown; missing measurements remain explicit",
            "ratio_floor_secs": RATIO_FLOOR_SECS,
            "win_loss_min_secs": WIN_LOSS_MIN_SECS,
            "decided_by_both": "verdict lists equal, nonempty, no unknown, no timeout/crash — the only files entering ratio statistics",
        },
        "divisions": divisions.iter().map(|(n, s)| div_json(n, s)).collect::<Vec<_>>(),
        "totals": div_json("TOTAL", totals),
        "files": files_json,
        "disagree_files": disagree_files,
        "pass": totals.disagree == 0,
    })
}

#[allow(clippy::too_many_lines)]
fn render_report(
    cfg: &BenchConfig,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
    ay_version: Option<&str>,
    z3_version: Option<&str>,
    campaign_wall: Duration,
    resource_plan: &ResourcePlan,
    resource_evidence: &serde_json::Value,
) -> String {
    use std::fmt::Write as _;
    let mut md = String::new();
    let _ = writeln!(md, "# AY vs z3 — differential benchmark report");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "Generated {} by `ay-z3-parity bench`. Every number below is mechanically",
        utc_now_iso()
    );
    let _ = writeln!(
        md,
        "derived from the run recorded in the JSON certificate next to this file;"
    );
    // "no file was skipped" is a claim about THIS RUN over the corpus roots it
    // was given. It says nothing about whether those roots are the whole of
    // SMT-LIB, and readers took it to mean exactly that: reports generated over
    // `benchmarks/smtlib-sample` (1,500 files, 5 of 84 divisions) were quoted as
    // corpus-wide parity results. State the scope limit in the artifact itself.
    let _ = writeln!(
        md,
        "nothing is hand-edited. Within the corpus roots listed below, no file was"
    );
    let _ = writeln!(
        md,
        "skipped or sampled. SCOPE: these numbers describe exactly those roots and"
    );
    let _ = writeln!(
        md,
        "are not corpus-wide unless the roots are — `benchmarks/smtlib-sample` is a"
    );
    let _ = writeln!(
        md,
        "1,500-file, 5-division slice of SMT-LIB 2024 (84 divisions); the complete"
    );
    let _ = writeln!(
        md,
        "corpus is `benchmarks/smtlib-all` via `ay-z3-parity fetch`."
    );
    let _ = writeln!(md);
    let _ = writeln!(md, "## Reproduce");
    let _ = writeln!(md);
    let _ = writeln!(md, "```sh");
    let _ = writeln!(
        md,
        "# 1. build the solver library under test (release) and this tool"
    );
    let _ = writeln!(md, "cargo build --release -p ay-ffi");
    let _ = writeln!(md, "cargo build --release -p ay-z3-parity");
    let _ = writeln!(
        md,
        "# 2. fetch the SMT-LIB samples (see benchmarks/smtlib-sample/MANIFEST.md"
    );
    let _ = writeln!(
        md,
        "#    for URLs, checksums, and the deterministic sampling rule)"
    );
    let _ = writeln!(md, "# 3. run the campaign (exact invocation of this run):");
    let _ = writeln!(md, "{}", std::env::args().collect::<Vec<_>>().join(" "));
    let _ = writeln!(md, "```");
    let _ = writeln!(md);
    let _ = writeln!(md, "| | |");
    let _ = writeln!(md, "|---|---|");
    let _ = writeln!(md, "| AY library | `{}` |", cfg.ay.display());
    let _ = writeln!(
        md,
        "| AY sha256 | `{}` |",
        sha256_of(&cfg.ay).unwrap_or_else(|| "?".into())
    );
    let _ = writeln!(
        md,
        "| AY `Z3_get_full_version` | {} |",
        ay_version.unwrap_or("?")
    );
    let _ = writeln!(md, "| z3 library | `{}` |", cfg.z3.display());
    let _ = writeln!(
        md,
        "| z3 sha256 | `{}` |",
        sha256_of(&cfg.z3).unwrap_or_else(|| "?".into())
    );
    let _ = writeln!(
        md,
        "| z3 `Z3_get_full_version` | {} |",
        z3_version.unwrap_or("?")
    );
    let _ = writeln!(
        md,
        "| timeout per (file, solver) | {} s |",
        cfg.timeout_secs
    );
    let _ = writeln!(
        md,
        "| hard process-group timeout | {} s |",
        resource_evidence["hard_timeout_secs"]
    );
    let _ = writeln!(
        md,
        "| parallel jobs requested / effective | {} / {} |",
        resource_plan.requested_jobs, resource_plan.jobs
    );
    let _ = writeln!(
        md,
        "| memory per child | {} MiB |",
        resource_plan.memlimit_mb_per_child
    );
    let _ = writeln!(
        md,
        "| NBCORE per child | {} |",
        resource_plan.nbcore_per_child
    );
    let _ = writeln!(
        md,
        "| reserved host headroom | {} MiB |",
        resource_plan.headroom_mb
    );
    let _ = writeln!(
        md,
        "| resource enforcement | `{ENFORCEMENT_RSS_WATCHDOG_V1}` |"
    );
    let _ = writeln!(
        md,
        "| exact execution envelope | `{}` |",
        resource_evidence["external_ffi"]["execution_envelope"]
            .as_str()
            .unwrap_or("?")
    );
    let _ = writeln!(
        md,
        "| campaign wall time | {:.1} s |",
        campaign_wall.as_secs_f64()
    );
    let _ = writeln!(md, "| host | {} |", host_info());
    let _ = writeln!(md);

    // Soundness verdict, first and prominent.
    let _ = writeln!(md, "## Soundness: sat-vs-unsat disagreements");
    let _ = writeln!(md);
    if totals.disagree == 0 {
        let _ = writeln!(
            md,
            "**DISAGREE = 0** across {} files. No paired decisive answers conflicted;",
            totals.files
        );
        let _ = writeln!(
            md,
            "unknown, timeout, memout, crash, and missing-verdict cases remain accounted below."
        );
    } else {
        let _ = writeln!(
            md,
            "**DISAGREE = {} — SOUNDNESS BUG(S). This run FAILS.**",
            totals.disagree
        );
        let _ = writeln!(md);
        let _ = writeln!(
            md,
            "The \"declared\" column is the benchmark's own `(set-info :status ...)`"
        );
        let _ = writeln!(
            md,
            "annotation — ground truth independent of both solvers. A solver whose"
        );
        let _ = writeln!(md, "verdict contradicts it has the wrong answer.");
        let _ = writeln!(md);
        let _ = writeln!(md, "| file | declared | z3 | AY |");
        let _ = writeln!(md, "|---|---|---|---|");
        for r in records.iter().filter(|r| r.category == Category::Disagree) {
            let _ = writeln!(
                md,
                "| `{}` | {} | {} | {} |",
                r.file.display(),
                declared_status(&r.file).unwrap_or_else(|| "(none)".into()),
                r.z3.label(),
                r.ay.label()
            );
        }
    }
    let _ = writeln!(md);

    // Per-division table.
    let _ = writeln!(md, "## Per-division results");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "{}",
        md_row(&HEADERS.iter().map(|h| h.to_string()).collect::<Vec<_>>())
    );
    let _ = writeln!(md, "|{}", "---|".repeat(HEADERS.len()));
    for (name, s) in divisions {
        let _ = writeln!(md, "{}", md_row(&stats_row(name, s)));
    }
    let _ = writeln!(md, "{}", md_row(&stats_row("**TOTAL**", totals)));
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "Column key: A-SAT/A-UNSAT/A-MIX = both solvers produced identical decisive"
    );
    let _ = writeln!(
        md,
        "verdicts; BOTH-UNK = identical verdicts containing `unknown`; AY-UNK = AY"
    );
    let _ = writeln!(
        md,
        "`unknown` where z3 decided (AY incompleteness); Z3-UNK = the reverse;"
    );
    let _ = writeln!(md, "T/O a/z/b = timeouts (AY only / z3 only / both);");
    let _ = writeln!(
        md,
        "MEM a/z/b = enforced memory-limit exits; CRASH a/z = solver process died"
    );
    let _ = writeln!(
        md,
        "(either alone or both); OTHER = verdict-count mismatch or no verdicts;"
    );
    let _ = writeln!(
        md,
        "MED/GEO = median / geometric-mean wall ratio AY/z3 over decided-by-both"
    );
    let _ = writeln!(
        md,
        "files (ratio < 1 means AY is faster); W/L 2x = files where AY / z3 was more"
    );
    let _ = writeln!(
        md,
        "than 2x faster and the slower side took at least {} ms.",
        (WIN_LOSS_MIN_SECS * 1000.0) as u64
    );
    let _ = writeln!(md);

    // ---- Where z3 wins (auto-populated, honest) ----
    let _ = writeln!(md, "## Where z3 wins");
    let _ = writeln!(md);
    let mut z3_wins_any = false;

    let ay_crashes: Vec<&FileRecord> = records
        .iter()
        .filter(|r| matches!(r.category, Category::CrashAy | Category::CrashBoth))
        .collect();
    if !ay_crashes.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(md, "### AY crashes ({})", ay_crashes.len());
        let _ = writeln!(md);
        for r in ay_crashes.iter().take(30) {
            let detail = r.ay.detail().unwrap_or("?");
            let _ = writeln!(
                md,
                "- `{}` — {} (z3: {})",
                r.file.display(),
                detail,
                r.z3.label()
            );
        }
        if ay_crashes.len() > 30 {
            let _ = writeln!(
                md,
                "- … and {} more (see certificate)",
                ay_crashes.len() - 30
            );
        }
        let _ = writeln!(md);
    }

    let ay_to_z3_decided: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::TimeoutAy && r.z3.decided())
        .collect();
    if !ay_to_z3_decided.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### AY timed out where z3 decided ({} files)",
            ay_to_z3_decided.len()
        );
        let _ = writeln!(md);
        let _ = writeln!(md, "| file | z3 verdict | z3 ms |");
        let _ = writeln!(md, "|---|---|---|");
        for r in ay_to_z3_decided.iter().take(20) {
            let _ = writeln!(
                md,
                "| `{}` | {} | {} |",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall)
            );
        }
        if ay_to_z3_decided.len() > 20 {
            let _ = writeln!(
                md,
                "| … and {} more (see certificate) | | |",
                ay_to_z3_decided.len() - 20
            );
        }
        let _ = writeln!(md);
    }

    let ay_memout_z3_decided: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::MemoutAy && r.z3.decided())
        .collect();
    if !ay_memout_z3_decided.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### AY exceeded its memory envelope where z3 decided ({} files)",
            ay_memout_z3_decided.len()
        );
        let _ = writeln!(md);
        for r in ay_memout_z3_decided.iter().take(20) {
            let _ = writeln!(
                md,
                "- `{}` (z3: {} in {} ms)",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall)
            );
        }
        if ay_memout_z3_decided.len() > 20 {
            let _ = writeln!(
                md,
                "- … and {} more (see certificate)",
                ay_memout_z3_decided.len() - 20
            );
        }
        let _ = writeln!(md);
    }

    if totals.ay_unknown > 0 {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### AY answered `unknown` where z3 decided ({} files)",
            totals.ay_unknown
        );
        let _ = writeln!(md);
        for (name, s) in divisions {
            if s.ay_unknown == 0 {
                continue;
            }
            let _ = writeln!(md, "- **{name}**: {} of {} files", s.ay_unknown, s.files);
            for r in records
                .iter()
                .filter(|r| r.division == *name && r.category == Category::AyUnknownZ3Decided)
                .take(8)
            {
                let _ = writeln!(
                    md,
                    "  - `{}` (z3: {} in {} ms)",
                    r.file.display(),
                    r.z3.label(),
                    fmt_ms(r.z3.wall)
                );
            }
            if s.ay_unknown > 8 {
                let _ = writeln!(md, "  - … and {} more (see certificate)", s.ay_unknown - 8);
            }
        }
        let _ = writeln!(md);
    }

    let ay_no_verdict: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::Other && r.ay.no_verdict() && r.z3.decided())
        .collect();
    if !ay_no_verdict.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### AY produced no verdict where z3 decided ({} files)",
            ay_no_verdict.len()
        );
        let _ = writeln!(md);
        let _ = writeln!(
            md,
            "AY ran to completion but emitted no `sat`/`unsat` token — typically an"
        );
        let _ = writeln!(
            md,
            "`(error ...)`-only reply such as an unsupported logic or command in the"
        );
        let _ = writeln!(
            md,
            "`Z3_eval_smtlib2_string` path. These count as OTHER in the table."
        );
        let _ = writeln!(md);
        for r in ay_no_verdict.iter().take(15) {
            let _ = writeln!(
                md,
                "- `{}` (z3: {} in {} ms)",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall)
            );
        }
        if ay_no_verdict.len() > 15 {
            let _ = writeln!(
                md,
                "- … and {} more (see certificate)",
                ay_no_verdict.len() - 15
            );
        }
        let _ = writeln!(md);
    }

    let mut slowdowns: Vec<&FileRecord> = records
        .iter()
        .filter(|r| {
            r.ratio.is_some_and(|x| x > 2.0)
                && r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64()) >= WIN_LOSS_MIN_SECS
        })
        .collect();
    slowdowns.sort_by(|a, b| b.ratio.partial_cmp(&a.ratio).expect("no NaN ratios"));
    if !slowdowns.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### z3 more than 2x faster (decided-by-both; {} files, top 20 by ratio)",
            slowdowns.len()
        );
        let _ = writeln!(md);
        let _ = writeln!(md, "| file | verdict | z3 ms | AY ms | AY/z3 |");
        let _ = writeln!(md, "|---|---|---|---|---|");
        for r in slowdowns.iter().take(20) {
            let _ = writeln!(
                md,
                "| `{}` | {} | {} | {} | {} |",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall),
                fmt_ms(r.ay.wall),
                fmt_ratio(r.ratio)
            );
        }
        let _ = writeln!(md);
    }

    if !z3_wins_any {
        let _ = writeln!(
            md,
            "No z3 advantage observed on this corpus: no AY crashes, no AY-only"
        );
        let _ = writeln!(
            md,
            "timeouts on z3-decided files, no AY-unknowns where z3 decided, and no"
        );
        let _ = writeln!(
            md,
            "decided-by-both file where z3 was more than 2x faster (with the slower"
        );
        let _ = writeln!(md, "side over {} ms).", (WIN_LOSS_MIN_SECS * 1000.0) as u64);
        let _ = writeln!(md);
    }

    // ---- Where AY wins (same rules, reversed) ----
    let _ = writeln!(md, "## Where AY wins");
    let _ = writeln!(md);
    let mut ay_wins_any = false;
    let z3_to_ay_decided = records
        .iter()
        .filter(|r| r.category == Category::TimeoutZ3 && r.ay.decided())
        .count();
    if z3_to_ay_decided > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 timed out where AY decided: {z3_to_ay_decided} files"
        );
    }
    let z3_memout_ay_decided = records
        .iter()
        .filter(|r| r.category == Category::MemoutZ3 && r.ay.decided())
        .count();
    if z3_memout_ay_decided > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 exceeded its memory envelope where AY decided: {z3_memout_ay_decided} files"
        );
    }
    if totals.z3_unknown > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 answered `unknown` where AY decided: {} files",
            totals.z3_unknown
        );
    }
    let speedups = records
        .iter()
        .filter(|r| {
            r.ratio.is_some_and(|x| x < 0.5)
                && r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64()) >= WIN_LOSS_MIN_SECS
        })
        .count();
    if speedups > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- AY more than 2x faster (decided-by-both, slower side ≥ {} ms): {} files",
            (WIN_LOSS_MIN_SECS * 1000.0) as u64,
            speedups
        );
    }
    let z3_no_verdict = records
        .iter()
        .filter(|r| r.category == Category::Other && r.z3.no_verdict() && r.ay.decided())
        .count();
    if z3_no_verdict > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 produced no verdict where AY decided: {z3_no_verdict} files"
        );
    }
    let z3_crashes = records
        .iter()
        .filter(|r| matches!(r.category, Category::CrashZ3 | Category::CrashBoth))
        .count();
    if z3_crashes > 0 {
        ay_wins_any = true;
        let _ = writeln!(md, "- z3 crashes: {z3_crashes} files");
    }
    if !ay_wins_any {
        let _ = writeln!(
            md,
            "No AY advantage observed on this corpus under the same rules."
        );
    }
    let _ = writeln!(md);

    let _ = writeln!(md, "## Methodology");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "- Both libraries are `dlopen`ed by path; each (file, solver) pair runs in a"
    );
    let _ = writeln!(
        md,
        "  stopped-exec child process group (`ay-z3-parity bench-one <lib> <file>`)."
    );
    let _ = writeln!(
        md,
        "  `_oom_guard.py` caps jobs and arms a zero-grace RSS watchdog before exec;"
    );
    let _ = writeln!(
        md,
        "  residual descendants are killed before leader reap, and stdout retention is"
    );
    let _ = writeln!(md, "  capped at one MiB.");
    let _ = writeln!(
        md,
        "- Wall time is measured inside the child strictly around"
    );
    let _ = writeln!(
        md,
        "  `Z3_eval_smtlib2_string` — process spawn, `dlopen`, and file reading are"
    );
    let _ = writeln!(md, "  excluded, identically for both solvers.");
    let _ = writeln!(
        md,
        "- Timeout: the child is SIGKILLed {}s after the {}s budget; a child that",
        KILL_GRACE.as_secs(),
        cfg.timeout_secs
    );
    let _ = writeln!(
        md,
        "  finishes in the grace window but whose eval time exceeded the budget is"
    );
    let _ = writeln!(md, "  still recorded as a timeout.");
    let _ = writeln!(
        md,
        "- Verdicts are the ordered whole-word `sat`/`unsat`/`unknown` tokens of each"
    );
    let _ = writeln!(
        md,
        "  solver's output; `sat` never substring-matches `unsat`."
    );
    let _ = writeln!(
        md,
        "- Ratio statistics use only decided-by-both files (identical decisive verdict"
    );
    let _ = writeln!(
        md,
        "  lists), with each side floored at {} ms to keep timer granularity from",
        RATIO_FLOOR_SECS * 1000.0
    );
    let _ = writeln!(md, "  fabricating extreme ratios on trivial files.");
    let _ = writeln!(
        md,
        "- z3 is run first, then AY, for every file; ordering is identical across the"
    );
    let _ = writeln!(md, "  corpus and both solvers see the exact same bytes.");
    md
}

// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn verdicts(v: &[Verdict]) -> BenchOutcome {
        BenchOutcome {
            kind: OutcomeKind::Verdicts(v.to_vec()),
            wall: Duration::from_millis(5),
            peak_rss: None,
        }
    }
    fn timeout() -> BenchOutcome {
        BenchOutcome {
            kind: OutcomeKind::Timeout,
            wall: Duration::from_secs(20),
            peak_rss: None,
        }
    }
    fn memout() -> BenchOutcome {
        BenchOutcome {
            kind: OutcomeKind::MemoryLimit,
            wall: Duration::from_secs(1),
            peak_rss: None,
        }
    }
    fn crash() -> BenchOutcome {
        BenchOutcome {
            kind: OutcomeKind::Crash("signal 6".into()),
            wall: Duration::from_millis(1),
            peak_rss: None,
        }
    }

    #[test]
    fn categorize_soundness_dominates() {
        use Verdict::*;
        assert_eq!(
            categorize(&verdicts(&[Sat]), &verdicts(&[Unsat])),
            Category::Disagree
        );
        // Disagreement at any position wins over unknown noise elsewhere.
        assert_eq!(
            categorize(&verdicts(&[Unknown, Sat]), &verdicts(&[Sat, Unsat])),
            Category::Disagree
        );
    }

    #[test]
    fn categorize_agreement_classes() {
        use Verdict::*;
        assert_eq!(
            categorize(&verdicts(&[Sat]), &verdicts(&[Sat])),
            Category::AgreeSat
        );
        assert_eq!(
            categorize(&verdicts(&[Unsat]), &verdicts(&[Unsat])),
            Category::AgreeUnsat
        );
        assert_eq!(
            categorize(&verdicts(&[Sat, Unsat]), &verdicts(&[Sat, Unsat])),
            Category::AgreeMixed
        );
        assert_eq!(
            categorize(&verdicts(&[Sat, Unknown]), &verdicts(&[Sat, Unknown])),
            Category::BothUnknown
        );
    }

    #[test]
    fn categorize_unknown_sides() {
        use Verdict::*;
        assert_eq!(
            categorize(&verdicts(&[Unknown]), &verdicts(&[Sat])),
            Category::AyUnknownZ3Decided
        );
        assert_eq!(
            categorize(&verdicts(&[Unsat]), &verdicts(&[Unknown])),
            Category::Z3UnknownAyDecided
        );
        // AY incompleteness dominates when both directions occur.
        assert_eq!(
            categorize(&verdicts(&[Unknown, Sat]), &verdicts(&[Sat, Unknown])),
            Category::AyUnknownZ3Decided
        );
    }

    #[test]
    fn categorize_timeouts_and_crashes() {
        use Verdict::*;
        assert_eq!(
            categorize(&timeout(), &verdicts(&[Sat])),
            Category::TimeoutAy
        );
        assert_eq!(
            categorize(&verdicts(&[Sat]), &timeout()),
            Category::TimeoutZ3
        );
        assert_eq!(categorize(&timeout(), &timeout()), Category::TimeoutBoth);
        assert_eq!(categorize(&memout(), &verdicts(&[Sat])), Category::MemoutAy);
        assert_eq!(categorize(&verdicts(&[Sat]), &memout()), Category::MemoutZ3);
        assert_eq!(categorize(&memout(), &memout()), Category::MemoutBoth);
        assert_eq!(categorize(&crash(), &verdicts(&[Sat])), Category::CrashAy);
        assert_eq!(categorize(&verdicts(&[Sat]), &crash()), Category::CrashZ3);
        assert_eq!(categorize(&crash(), &crash()), Category::CrashBoth);
        assert_eq!(categorize(&crash(), &timeout()), Category::CrashAy);
    }

    #[test]
    fn categorize_count_mismatch_and_empty() {
        use Verdict::*;
        assert_eq!(categorize(&verdicts(&[]), &verdicts(&[])), Category::Other);
        assert_eq!(
            categorize(&verdicts(&[Sat]), &verdicts(&[Sat, Sat])),
            Category::Other
        );
    }

    #[test]
    fn median_and_geomean() {
        assert_eq!(median(&[]), None);
        assert_eq!(median(&[2.0]), Some(2.0));
        assert_eq!(median(&[1.0, 2.0, 4.0]), Some(2.0));
        assert_eq!(median(&[1.0, 2.0, 3.0, 4.0]), Some(2.5));
        let g = geomean(&[0.5, 2.0]).expect("nonempty");
        assert!(
            (g - 1.0).abs() < 1e-12,
            "geomean of reciprocal pair is 1, got {g}"
        );
        assert_eq!(geomean(&[]), None);
    }

    #[test]
    fn resource_evidence_persists_requested_and_effective_envelope() {
        let plan = ResourcePlan {
            requested_jobs: 8,
            jobs: 3,
            memlimit_mb_per_child: 2048,
            nbcore_per_child: 2,
            headroom_mb: 16_384,
            planner: "scripts/_oom_guard.py".to_string(),
        };
        let evidence =
            resource_evidence(&plan, Duration::from_secs(20), true).expect("resource evidence");
        assert_eq!(evidence["requested_jobs"], 8);
        assert_eq!(evidence["effective_jobs"], 3);
        assert_eq!(evidence["memlimit_mb_per_child"], 2048);
        assert_eq!(evidence["nbcore_per_child"], 2);
        assert_eq!(evidence["headroom_mb"], 16_384);
        assert_eq!(evidence["solver_timeout_secs"], 20.0);
        assert_eq!(evidence["hard_timeout_secs"], 22.0);
        assert_eq!(
            evidence["external_ffi"]["enforcement"],
            ENFORCEMENT_RSS_WATCHDOG_V1
        );
        assert_eq!(
            evidence["ay_selfcheck"]["enforcement"],
            ENFORCEMENT_AY_MEMORY_RSS_V1
        );
        assert!(evidence["external_ffi"]["execution_envelope"]
            .as_str()
            .is_some_and(|value| value.contains("jobs=3")));
    }

    #[test]
    fn ratio_floor_damps_trivial_files() {
        let fast = BenchOutcome {
            kind: OutcomeKind::Verdicts(vec![Verdict::Sat]),
            wall: Duration::from_nanos(200),
            peak_rss: None,
        };
        let slow = BenchOutcome {
            kind: OutcomeKind::Verdicts(vec![Verdict::Sat]),
            wall: Duration::from_micros(20),
            peak_rss: None,
        };
        // Both below the floor: ratio clamps to 1 rather than 100x.
        assert!((ratio_of(&slow, &fast) - 1.0).abs() < 1e-9);
    }

    #[test]
    fn win_loss_requires_meaningful_time() {
        let mut s = DivStats::default();
        let mk = |ms: u64| BenchOutcome {
            kind: OutcomeKind::Verdicts(vec![Verdict::Sat]),
            wall: Duration::from_millis(ms),
            peak_rss: None,
        };
        // 1ms vs 4ms: 4x apart but both trivial — a tie, not a win.
        let ay = mk(1);
        let z3 = mk(4);
        s.add(&FileRecord {
            division: "d".into(),
            file: PathBuf::from("a.smt2"),
            ratio: Some(ratio_of(&ay, &z3)),
            ay,
            z3,
            category: Category::AgreeSat,
        });
        assert_eq!((s.ay_wins_2x, s.z3_wins_2x), (0, 0));
        // 5ms vs 25ms: real 5x win for AY.
        let ay = mk(5);
        let z3 = mk(25);
        s.add(&FileRecord {
            division: "d".into(),
            file: PathBuf::from("b.smt2"),
            ratio: Some(ratio_of(&ay, &z3)),
            ay,
            z3,
            category: Category::AgreeSat,
        });
        assert_eq!((s.ay_wins_2x, s.z3_wins_2x), (1, 0));
    }

    #[test]
    fn division_mapping() {
        let root = PathBuf::from("benchmarks/smt");
        assert_eq!(
            division_of(&root, &root.join("QF_LIA/x.smt2")),
            "smt/QF_LIA"
        );
        assert_eq!(
            division_of(&root, &root.join("QF_LIA/deep/x.smt2")),
            "smt/QF_LIA"
        );
        assert_eq!(division_of(&root, &root.join("top.smt2")), "smt/(top)");
    }

    #[test]
    fn utc_timestamp_shape() {
        let t = utc_now_iso();
        assert_eq!(t.len(), 20, "{t}");
        assert!(t.ends_with('Z'));
        assert_eq!(&t[4..5], "-");
        assert_eq!(&t[10..11], "T");
    }

    #[test]
    fn declared_status_parsing() {
        assert_eq!(
            parse_declared_status("(set-info :status unsat)\n(check-sat)"),
            DeclaredStatus::Unsat
        );
        assert_eq!(
            parse_declared_status("(set-info :status sat)"),
            DeclaredStatus::Sat
        );
        assert_eq!(
            parse_declared_status("(set-info :status unknown)"),
            DeclaredStatus::Unknown
        );
        assert_eq!(
            parse_declared_status("(set-logic QF_AX)"),
            DeclaredStatus::Absent
        );
        assert_eq!(
            parse_declared_status("(set-info :status bogus)"),
            DeclaredStatus::Absent
        );
    }

    /// A missing annotation, a declared `unknown`, and a declared `sat`/`unsat`
    /// are three DIFFERENT pieces of evidence and must never collapse: `absent`
    /// means nobody stated an answer, `unknown` means the author stated they do
    /// not know, and only `sat`/`unsat` is an oracle a solver can be judged on.
    #[test]
    fn declared_status_distinguishes_absent_from_unknown() {
        assert_eq!(parse_declared_status(""), DeclaredStatus::Absent);
        assert_eq!(
            parse_declared_status("(set-logic UFBV)\n(check-sat)\n(exit)\n"),
            DeclaredStatus::Absent
        );
        assert_eq!(DeclaredStatus::Absent.as_str(), "absent");
        assert_eq!(DeclaredStatus::Unknown.as_str(), "unknown");
        assert_eq!(DeclaredStatus::Absent.decided(), None);
        assert_eq!(DeclaredStatus::Unknown.decided(), None);
        assert_eq!(DeclaredStatus::Sat.decided(), Some(Verdict::Sat));
        assert_eq!(DeclaredStatus::Unsat.decided(), Some(Verdict::Unsat));
    }

    /// The real shape of an SMT-LIB header: several `set-info` commands, the
    /// status among them, and — the trap — a `(set-info :source | ... |)` blob
    /// of prose that MENTIONS `:status`. A substring search for the first
    /// `:status` reads the prose as the answer; the real annotation must win.
    #[test]
    fn declared_status_ignores_quoted_source_blocks_and_comments() {
        let file = "\
(set-info :smt-lib-version 2.6)
(set-logic UFBV)
(set-info :source |
Hardware fixpoint check problems. Generated with :status sat by a script that
also emits (set-info :status sat) for the companion family.
|)
(set-info :category \"industrial\")
(set-info :status unsat)
(check-sat)
";
        assert_eq!(parse_declared_status(file), DeclaredStatus::Unsat);

        // Same trap in a string literal, and in a line comment.
        assert_eq!(
            parse_declared_status(
                "(set-info :notes \":status sat\")\n; was (set-info :status sat)\n(set-info :status unsat)\n"
            ),
            DeclaredStatus::Unsat
        );
        // The trap ALONE (no real annotation) declares nothing.
        assert_eq!(
            parse_declared_status("(set-info :source |see :status sat|)\n(check-sat)\n"),
            DeclaredStatus::Absent
        );
        // A longer keyword is not `:status`.
        assert_eq!(
            parse_declared_status("(set-info :status-bits sat)\n"),
            DeclaredStatus::Absent
        );
    }

    /// Multiple `set-info` commands are normal. Repeating the SAME status is
    /// still that status; two DIFFERENT statuses make the benchmark
    /// self-contradicting, and a self-contradicting file is no oracle — it must
    /// degrade to `unknown`, never pick one and accuse a solver on a coin flip.
    #[test]
    fn declared_status_over_multiple_set_info_lines() {
        assert_eq!(
            parse_declared_status(
                "(set-info :smt-lib-version 2.6)\n(set-info :category \"crafted\")\n\
                 (set-info :status unsat)\n(set-info :license \"CC0\")\n"
            ),
            DeclaredStatus::Unsat
        );
        assert_eq!(
            parse_declared_status("(set-info :status sat)\n(set-info :status sat)\n"),
            DeclaredStatus::Sat
        );
        assert_eq!(
            parse_declared_status("(set-info :status sat)\n(set-info :status unsat)\n"),
            DeclaredStatus::Unknown
        );
        assert_eq!(
            parse_declared_status("(set-info :status unsat)\n(set-info :status unknown)\n"),
            DeclaredStatus::Unknown
        );
    }

    /// The file-level entry point the scoreboard actually calls: it must reach
    /// the annotation through the same traps, and an unreadable path declares
    /// nothing rather than failing the run.
    #[test]
    fn declared_status_of_file_reads_the_real_annotation() {
        let dir = std::env::temp_dir().join(format!(
            "ay-z3-parity-declared-{}-{}",
            std::process::id(),
            utc_now_iso().replace([':', '-'], "")
        ));
        std::fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("b.smt2");
        std::fs::write(
            &path,
            "(set-info :source |generated for :status sat|)\n(set-info :status unsat)\n(check-sat)\n",
        )
        .expect("write");
        assert_eq!(declared_status_of_file(&path), DeclaredStatus::Unsat);
        assert_eq!(declared_status(&path).as_deref(), Some("unsat"));

        let missing = dir.join("nope.smt2");
        assert_eq!(declared_status_of_file(&missing), DeclaredStatus::Absent);
        assert_eq!(declared_status(&missing), None);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn decided_requires_no_unknown() {
        use Verdict::*;
        assert!(verdicts(&[Sat, Unsat]).decided());
        assert!(!verdicts(&[Sat, Unknown]).decided());
        assert!(!verdicts(&[]).decided());
        assert!(!timeout().decided());
    }

    fn selfcheck_raw(code: Option<i32>, stdout: &str, observed: Duration) -> RawRun {
        RawRun {
            killed: false,
            memout: false,
            code,
            status_str: code.map_or_else(|| "signal: 6".to_string(), |code| code.to_string()),
            stdout: stdout.as_bytes().to_vec(),
            observed,
            output_truncated: false,
            harness_error: None,
        }
    }

    #[test]
    fn bench_child_protocol_requires_rss_and_preserves_solver_output() {
        let parsed =
            parse_bench_child_output("AYZ3_WALL_NS 123\nAYZ3_RSS_BYTES 4096\nsat\n(model)\n")
                .expect("valid child protocol");
        assert_eq!(parsed.wall, Duration::from_nanos(123));
        assert_eq!(parsed.peak_rss, Some(4096));
        assert_eq!(parsed.solver_output, "sat\n(model)\n");

        assert!(parse_bench_child_output("AYZ3_WALL_NS 123\nsat\n").is_err());
        let without_host_rss =
            parse_bench_child_output("AYZ3_WALL_NS 1\nAYZ3_RSS_BYTES -\nunsat\n")
                .expect("unsupported hosts use an explicit missing-RSS marker");
        assert_eq!(without_host_rss.peak_rss, None);
    }

    #[test]
    fn selfcheck_requires_a_clean_zero_exit_before_accepting_verdicts() {
        let timeout = Duration::from_secs(1);
        assert!(matches!(
            interpret_selfcheck_raw(selfcheck_raw(Some(0), "unsat\n", Duration::from_millis(1)), timeout),
            SelfCheck::Verdicts(verdicts) if verdicts == [Verdict::Unsat]
        ));
        assert!(matches!(
            interpret_selfcheck_raw(
                selfcheck_raw(Some(1), "unsat\n", Duration::from_millis(1)),
                timeout
            ),
            SelfCheck::Error(_)
        ));
        assert!(matches!(
            interpret_selfcheck_raw(
                selfcheck_raw(None, "unsat\n", Duration::from_millis(1)),
                timeout
            ),
            SelfCheck::Crash(_)
        ));
    }

    #[test]
    fn selfcheck_result_finishing_in_kill_grace_is_still_a_timeout() {
        let timeout = Duration::from_secs(1);
        assert!(matches!(
            interpret_selfcheck_raw(
                selfcheck_raw(Some(0), "sat\n", timeout + Duration::from_millis(1)),
                timeout
            ),
            SelfCheck::Timeout
        ));
    }

    #[test]
    fn selfcheck_distinguishes_memout_and_stdout_limit() {
        let timeout = Duration::from_secs(1);
        let mut memout = selfcheck_raw(None, "", Duration::from_millis(10));
        memout.memout = true;
        assert!(matches!(
            interpret_selfcheck_raw(memout, timeout),
            SelfCheck::MemoryLimit
        ));

        let mut oversized = selfcheck_raw(Some(0), "unsat\n", Duration::from_millis(10));
        oversized.output_truncated = true;
        assert!(matches!(
            interpret_selfcheck_raw(oversized, timeout),
            SelfCheck::Error(message) if message.contains("capture limit")
        ));
    }
}
