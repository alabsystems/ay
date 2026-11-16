// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequential-fallback composed solve (`--fallback-solver`).
//!
//! AY gets a first-stage budget on the ORIGINAL CNF. If that stage publishes no
//! verdict, a second engine gets the remaining budget on the SAME ORIGINAL CNF.
//! Nothing is translated, preprocessed, or re-encoded between the stages: both
//! engines read the identical file the harness handed us, so a model from
//! either one is a model of the harness's formula and needs no reconstruction.
//!
//! # What ships today: the SAT leg only
//!
//! * Second engine says SAT -> this driver re-reads the ORIGINAL CNF and checks
//!   the assignment clause by clause ITSELF. Only a model that satisfies every
//!   original clause is allowed to become `s SATISFIABLE`. A model checked
//!   against the original formula is self-certifying: it needs no proof, no
//!   trust in the second engine, and no change to the submission's declared
//!   checker.
//! * Second engine says UNSAT -> [`refuse_fallback_unsat`] DISCARDS it and the
//!   run reports what AY itself reported (unknown). AY's declared checker is
//!   VeriPB, which cannot read another engine's DRAT, so an UNSAT this process
//!   cannot certify must never reach stdout. That refusal is a named function
//!   with one caller, not an accident of control flow.
//!
//! The UNSAT leg needs a DRAT -> VeriPB translation and is deliberately absent.
//! Its seam is [`FallbackVerdict::Unsat`] in [`run_stage2`]: a future translator
//! plugs in exactly there, and until it does the refusal stands.
//!
//! # Structure: two processes, never overlapping
//!
//! Stage 1 is a re-exec of THIS binary with the identical argument vector minus
//! the `--fallback-*` flags and with `--timeout` overridden to the first-stage
//! budget. That is deliberate: stage 1 is not a special mode, it is today's AY,
//! bit for bit, including its proof emission, its supervisor, its memory
//! governor and its exit codes. Nothing in AY's own solve path is aware this
//! driver exists.
//!
//! Because stage 1 is a separate process that is reaped before stage 2 is
//! spawned, the two engines' heaps never coexist: peak RSS of the composition
//! is `max(stage1, stage2)`, not `stage1 + stage2`. That is the memory argument,
//! and it is structural rather than a tuning parameter.
//!
//! # Budget
//!
//! `--timeout` is the whole wall clock the harness allows (run.sh already
//! subtracts its own margin from `BENCHCLOUD_WALLCLOCK_LIMIT`). Every deadline
//! below is measured from the driver's own start instant and is strictly
//! inside it; see [`ComposeBudget`].
//!
//! # Shipping the second binary (proposal, not yet wired into the submission)
//!
//! `competition/prepare_sat26_submission.sh` builds a Main/regular root that
//! MUST carry `source.tar.gz` and MUST NOT stage a prebuilt binary (see its
//! `--source-mode archive` guard). The judges run `./build.sh`, which extracts
//! the archive and cargo-builds `ay`. A second engine therefore cannot be
//! dropped in as a binary; it has to be built there from bundled source:
//!
//! 1. add the engine's release tarball and its licence to the submission root
//!    (e.g. `third_party/kissat-4.0.4.tar.gz`, `third_party/kissat-LICENSE`),
//!    with their SHA-256 recorded next to `source_archive_sha256` in
//!    `profile/satcomp26_profile.json` so the existing `verify_declared_hash`
//!    machinery covers them;
//! 2. have the generated `build.sh` unpack and `./configure && make` it after
//!    the cargo build, installing the result as `$SCRIPT_DIR/kissat`;
//! 3. have the generated `run.sh` append
//!    `--fallback-solver "$SCRIPT_DIR/kissat" --fallback-after "$FIRST_STAGE_MS"`
//!    to `ARGS`, computing `FIRST_STAGE_MS` from the same `BUDGET_MS` it
//!    already derives, and skip both flags when the binary is absent so a
//!    failed second-engine build degrades to today's AY-only run rather than
//!    failing the instance.
//!
//! Locating it: the driver takes an explicit path and refuses to start if it is
//! not an executable file (see `validate`), so there is no `$PATH` search to go
//! wrong on the judges' machine. `$SCRIPT_DIR` is what run.sh already uses to
//! find `ay`.
//!
//! Licence: kissat is MIT (Biere et al., Freiburg/JKU). Redistribution in a
//! submission is permitted provided the copyright notice and permission notice
//! travel with it, which is why step 1 ships the licence file; the notice also
//! belongs in `THIRD_PARTY.md`, which is already inside `source.tar.gz`. MIT
//! imposes no copyleft obligation on AY's own Apache-2.0 sources.

use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::{Duration, Instant};

use wait_timeout::ChildExt as _;

/// Wall clock the driver keeps in hand purely to publish its answer once the
/// second stage has been reaped: flushing `v` lines for a large model.
const OUTPUT_RESERVE_BASE_MS: u64 = 2_000;

/// Extra reserve per MiB of the original CNF, for the model check. The check is
/// one sequential pass over the file; 10 ms/MiB budgets it at 100 MiB/s, well
/// under a cold spinning-disk read and far under a warm page-cache read.
const OUTPUT_RESERVE_MS_PER_MIB: u64 = 10;

/// Cap on the derived reserve. Beyond this the reserve costs more than the
/// instances it protects; the process-wide watchdog is the backstop.
const OUTPUT_RESERVE_CAP_MS: u64 = 30_000;

/// Below this, a second stage cannot plausibly beat AY on an instance AY just
/// failed, so the split is rejected at configuration time rather than shipping
/// a budget that silently wastes the tail.
const MIN_STAGE2_MS: u64 = 5_000;

/// Grace the driver allows stage 1 beyond its own `--timeout` before killing
/// it: AY's watchdog fires cooperatively at T', then hard-exits 2 s later.
/// 5 s covers that plus process teardown.
const STAGE1_GRACE_MS: u64 = 5_000;

/// Interval between SIGTERM and SIGKILL when the driver has to stop a stage
/// that overran its own deadline.
const KILL_ESCALATION: Duration = Duration::from_millis(1_500);

/// PID of the stage child that is live right now, or 0.
///
/// Published so the process-wide hard-exit path can reap it. That path is
/// [`crate::hard_timeout_fallback_exit`], which is reached both by the global
/// `--timeout` watchdog and by the SIGTERM handler, and which calls
/// `process::exit` — skipping every destructor in the process, including the
/// [`StageChildGuard`] below. Without this, a SIGTERM at the budget edge would
/// orphan a running second engine.
static LIVE_STAGE_CHILD: AtomicI32 = AtomicI32::new(0);

/// Pre-spawn snapshot of the staging entries in the sweep directories, for the
/// stage that is running right now. Published so the destructor-skipping exit
/// paths can still run the sweep. `None` means no stage is live.
///
/// Locked with a plain mutex: every reader runs on an ordinary thread (the
/// signal ITERATOR thread and the watchdog thread), never inside a signal
/// handler, so there is no async-signal-safety obligation here.
static LIVE_STAGE_SNAPSHOT: std::sync::OnceLock<std::sync::Mutex<Option<StagingSnapshot>>> =
    std::sync::OnceLock::new();

fn live_stage_snapshot() -> &'static std::sync::Mutex<Option<StagingSnapshot>> {
    LIVE_STAGE_SNAPSHOT.get_or_init(|| std::sync::Mutex::new(None))
}

/// SIGKILL the live stage child, if any, and sweep the staging artifacts it may
/// have left. Safe to call from any exit path and from a signal-driven thread;
/// a no-op when no stage child is running, which is every non-composed run.
pub(crate) fn kill_live_stage_child() {
    let pid = LIVE_STAGE_CHILD.swap(0, Ordering::SeqCst);
    if pid <= 0 {
        return;
    }
    signal_pid(pid, Signal::Kill);
    let snapshot = live_stage_snapshot().lock().ok().and_then(|mut s| s.take());
    if let Some(snapshot) = snapshot {
        snapshot.sweep_new_orphans();
    }
}

/// Register SIGINT and SIGHUP so an interactive or hang-up kill of the driver
/// reaps the stage child instead of orphaning it.
///
/// SIGTERM is deliberately NOT registered here. `run_solve` has already
/// installed the process-wide SIGTERM handler, and that handler ends in
/// [`crate::hard_timeout_fallback_exit`], which reaps through
/// [`kill_live_stage_child`]. Registering it twice would race two shutdown
/// paths for one signal.
#[cfg(unix)]
fn install_stage_child_reaper() {
    use signal_hook::consts::{SIGHUP, SIGINT};

    let Ok(mut signals) = signal_hook::iterator::Signals::new([SIGINT, SIGHUP]) else {
        return;
    };
    let _ = std::thread::Builder::new()
        .name("ay-compose-signals".to_string())
        .spawn(move || {
            if let Some(raw_signal) = (&mut signals).into_iter().next() {
                kill_live_stage_child();
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(128 + raw_signal);
            }
        });
}

#[cfg(not(unix))]
fn install_stage_child_reaper() {}

#[derive(Clone, Copy)]
enum Signal {
    Term,
    Kill,
}

/// Signal a stage child AND everything it spawned.
///
/// Both stages are spawned with `process_group(0)`, so each one leads its own
/// process group whose id is its pid; `kill(-pid)` therefore reaches the whole
/// subtree. That matters concretely: AY's session supervisor FORKS a solve
/// child which inherits the stdout pipe. Killing only the direct child would
/// leave that grandchild alive holding the write end open, the driver's reader
/// would never see EOF, and a run that was supposed to stop at its stage-1
/// deadline would block past the whole wall clock. The direct pid is signalled
/// too, in case the group could not be established.
#[cfg(unix)]
fn signal_pid(pid: i32, signal: Signal) {
    if pid <= 0 {
        return;
    }
    let signal = match signal {
        Signal::Term => nix::sys::signal::Signal::SIGTERM,
        Signal::Kill => nix::sys::signal::Signal::SIGKILL,
    };
    let _ = nix::sys::signal::kill(nix::unistd::Pid::from_raw(-pid), signal);
    let _ = nix::sys::signal::kill(nix::unistd::Pid::from_raw(pid), signal);
}

#[cfg(not(unix))]
fn signal_pid(_pid: i32, _signal: Signal) {}

/// Put a stage child in its own process group so [`signal_pid`] can reach every
/// process it goes on to create.
fn isolate_process_group(command: &mut Command) {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt as _;
        command.process_group(0);
    }
    #[cfg(not(unix))]
    {
        let _ = command;
    }
}

/// RAII guard over one stage child.
///
/// On every exit from the scope — normal return, `?`, or panic unwind — the
/// guard kills a child that is still running and then sweeps the staging
/// artifacts that child may have left behind.
///
/// The sweep exists because AY leaks `.ay-dimacs-proof-<pid>-<n>[.stage]` next
/// to its proof target when it dies abnormally: `create_named_dimacs_staging_file`
/// and `create_private_dimacs_staging_directory` name them after the producing
/// PID, and the epilogue that removes them is skipped on `process::exit`. One
/// sweep of this repository's benchmark corpus found 68 orphans holding 36.2 GB,
/// the oldest from 7 August. Stage 1 is exactly a process this driver may have
/// to kill, so it is exactly a process that would leak. Scoping the glob to the
/// child's own PID makes the sweep incapable of touching a concurrent run's
/// files.
struct StageChildGuard {
    pid: i32,
    kill_on_drop: bool,
}

impl StageChildGuard {
    fn new(pid: i32, snapshot: StagingSnapshot) -> Self {
        LIVE_STAGE_CHILD.store(pid, Ordering::SeqCst);
        if let Ok(mut slot) = live_stage_snapshot().lock() {
            *slot = Some(snapshot);
        }
        Self {
            pid,
            kill_on_drop: true,
        }
    }

    /// The child has been reaped; the guard must no longer signal a PID the OS
    /// is free to recycle. The staging sweep still runs on drop.
    fn reaped(&mut self) {
        self.kill_on_drop = false;
        LIVE_STAGE_CHILD.store(0, Ordering::SeqCst);
    }
}

impl Drop for StageChildGuard {
    fn drop(&mut self) {
        if self.kill_on_drop {
            signal_pid(self.pid, Signal::Kill);
            LIVE_STAGE_CHILD.store(0, Ordering::SeqCst);
        }
        let snapshot = live_stage_snapshot().lock().ok().and_then(|mut s| s.take());
        if let Some(snapshot) = snapshot {
            snapshot.sweep_new_orphans();
        }
    }
}

/// Filename prefix of AY's DIMACS proof staging artifacts. Mirrors
/// `DIMACS_PROOF_STAGING_PREFIX` in `dimacs/proof_registry.rs`; the two must
/// move together.
const DIMACS_PROOF_STAGING_PREFIX: &str = ".ay-dimacs-proof-";

/// What the sweep directories held immediately BEFORE a stage was spawned.
///
/// Naming the artifacts after the producing PID is not enough to find them
/// afterwards, and this was measured rather than assumed: a stage-1 run left
/// `.ay-dimacs-proof-84667-0.stage` behind, and 84667 was not the stage child
/// this driver spawned. AY's session supervisor FORKS the process that does the
/// solving, and it is that grandchild whose PID lands in the filename. A sweep
/// scoped to the direct child's PID sees nothing.
///
/// So the sweep is scoped by TIME instead, with a liveness check as the second
/// gate. An entry is removed only when BOTH hold:
///
/// * it was not there before this stage started, and
/// * the PID in its name is no longer a live process.
///
/// Together those make it impossible to touch a pre-existing orphan (which is
/// not this run's to delete) or a concurrent run's live staging file (which
/// would corrupt that run). What remains is exactly the set this stage
/// stranded.
struct StagingSnapshot {
    dirs: Vec<(PathBuf, Vec<std::ffi::OsString>)>,
}

impl StagingSnapshot {
    fn take(dirs: &[PathBuf]) -> Self {
        Self {
            dirs: dirs
                .iter()
                .map(|dir| (dir.clone(), staging_entries(dir)))
                .collect(),
        }
    }

    fn sweep_new_orphans(&self) {
        for (dir, before) in &self.dirs {
            for name in staging_entries(dir) {
                if before.contains(&name) {
                    continue;
                }
                let Some(pid) = staging_entry_pid(&name) else {
                    continue;
                };
                if pid_is_live(pid) {
                    continue;
                }
                let path = dir.join(&name);
                let removed = if path.is_dir() {
                    std::fs::remove_dir_all(&path).is_ok()
                } else {
                    std::fs::remove_file(&path).is_ok()
                };
                if removed {
                    safe_eprintln!(
                        "c compose: removed stranded staging artifact {}",
                        path.display()
                    );
                }
            }
        }
    }
}

fn staging_entries(dir: &Path) -> Vec<std::ffi::OsString> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    entries
        .flatten()
        .map(|entry| entry.file_name())
        .filter(|name| {
            name.to_str()
                .is_some_and(|name| name.starts_with(DIMACS_PROOF_STAGING_PREFIX))
        })
        .collect()
}

/// Pull the producing PID out of `.ay-dimacs-proof-<pid>-<nonce>[.stage]`.
fn staging_entry_pid(name: &std::ffi::OsStr) -> Option<i32> {
    name.to_str()?
        .strip_prefix(DIMACS_PROOF_STAGING_PREFIX)?
        .split('-')
        .next()?
        .parse()
        .ok()
}

/// Whether `pid` still names a live process. A staging artifact whose producer
/// is gone is an orphan by definition; one whose producer is alive is a file
/// that run is still writing to.
fn pid_is_live(pid: i32) -> bool {
    if pid <= 0 {
        return true;
    }
    #[cfg(unix)]
    {
        nix::sys::signal::kill(nix::unistd::Pid::from_raw(pid), None).is_ok()
    }
    #[cfg(not(unix))]
    {
        true
    }
}

// ---------------------------------------------------------------------------
// Configuration and budget
// ---------------------------------------------------------------------------

/// Everything the driver needs, resolved from `SolveArgs` by the caller so this
/// module never reaches into the 200-field argument struct.
pub(crate) struct ComposeConfig {
    /// The original CNF, exactly as the harness named it.
    pub instance: PathBuf,
    /// Second-engine binary.
    pub fallback_solver: PathBuf,
    /// Extra arguments handed to the second engine, before the instance path.
    pub fallback_args: Vec<String>,
    /// First-stage budget in milliseconds.
    pub stage1_ms: u64,
    /// Whole-run budget in milliseconds (the harness's `--timeout`).
    pub total_ms: u64,
    /// This process's entire argument vector, used to build stage 1's.
    pub raw_args: Vec<String>,
    /// `--proof` destination, if any. Only used to know which directory stage 1
    /// could have staged into.
    pub proof_path: Option<PathBuf>,
}

/// Deadlines, all measured from one instant so they cannot drift apart.
struct ComposeBudget {
    started: Instant,
    /// Hard wall for stage 1: it must be reaped by here.
    stage1_wall: Duration,
    /// Hard wall for stage 2: it is SIGKILLed at here.
    stage2_wall: Duration,
}

impl ComposeBudget {
    /// `reserve_ms` is time held back at the very end for the model check and
    /// for writing the model out.
    fn new(started: Instant, stage1_ms: u64, total_ms: u64, reserve_ms: u64) -> Self {
        let total = Duration::from_millis(total_ms);
        let reserve = Duration::from_millis(reserve_ms);
        // Everything after this instant belongs to publication, not to solving.
        let solve_wall = total.saturating_sub(reserve);
        // Stage 1 is allowed its own budget plus teardown grace, but may never
        // reach into the publication reserve.
        let stage1_wall = Duration::from_millis(stage1_ms.saturating_add(STAGE1_GRACE_MS));
        Self {
            started,
            stage1_wall: stage1_wall.min(solve_wall),
            stage2_wall: solve_wall,
        }
    }

    fn elapsed(&self) -> Duration {
        self.started.elapsed()
    }

    fn stage1_remaining(&self) -> Duration {
        self.stage1_wall.saturating_sub(self.elapsed())
    }

    fn stage2_remaining(&self) -> Duration {
        self.stage2_wall.saturating_sub(self.elapsed())
    }
}

/// Reserve derived from the size of the CNF the model check has to re-read.
fn output_reserve_ms(cnf_bytes: u64) -> u64 {
    let mib = cnf_bytes / (1024 * 1024);
    OUTPUT_RESERVE_BASE_MS
        .saturating_add(mib.saturating_mul(OUTPUT_RESERVE_MS_PER_MIB))
        .min(OUTPUT_RESERVE_CAP_MS)
}

// ---------------------------------------------------------------------------
// Stage-1 argument vector
// ---------------------------------------------------------------------------

/// Long options this driver owns and must not hand to stage 1.
const COMPOSE_OWN_FLAGS: [&str; 3] = ["--fallback-solver", "--fallback-after", "--fallback-arg"];

/// clap's exit code for a rejected command line.
const CLAP_USAGE_EXIT_CODE: i32 = 2;

/// How a token participates in an option that the driver has to remove.
enum Removal {
    /// Not ours; keep it.
    Keep,
    /// A complete `--flag=value` token; drop this token only.
    DropToken,
    /// A bare `--flag`; drop this token and the one that follows it.
    DropTokenAndValue,
}

/// Classify one raw token against the options the driver rewrites.
///
/// `--timeout` has to be REMOVED rather than merely overridden: clap rejects it
/// outright when it appears twice ("the argument '--timeout <TIMEOUT>' cannot be
/// used multiple times"), so appending a second one makes stage 1 exit 2 without
/// solving anything. That failure is silent from the outside — the fallback
/// still answers — which is exactly how a composition could ship having quietly
/// stopped running AY at all.
fn classify_stage1_token(arg: &str) -> Result<Removal, String> {
    if COMPOSE_OWN_FLAGS.contains(&arg) || arg == "--timeout" || arg == "-t" {
        return Ok(Removal::DropTokenAndValue);
    }
    if arg.starts_with("--timeout=")
        || COMPOSE_OWN_FLAGS.iter().any(|flag| {
            arg.len() > flag.len() && arg.starts_with(flag) && arg.as_bytes()[flag.len()] == b'='
        })
    {
        return Ok(Removal::DropToken);
    }
    // `-t500` / `-t=500`: the short spelling with an attached value.
    if arg.starts_with("-t") && !arg.starts_with("--") && arg.len() > 2 {
        return Ok(Removal::DropToken);
    }
    // A short-flag CLUSTER containing `t` (`-qt 500`) would smuggle a second
    // timeout past the filter. Refuse rather than guess where the value is.
    if arg.len() > 1
        && arg.starts_with('-')
        && !arg.starts_with("--")
        && arg[1..].contains('t')
        && arg.chars().nth(1) != Some('t')
    {
        return Err(format!(
            "cannot rewrite the first stage's budget: {arg} is a short-flag cluster containing \
             -t. Spell the timeout as --timeout=<ms>"
        ));
    }
    Ok(Removal::Keep)
}

/// Build stage 1's argument vector from this process's own.
///
/// Rebuilt from the RAW vector, not from the parsed `SolveArgs`, so every one
/// of AY's several hundred flags reaches stage 1 exactly as the harness spelled
/// it. Exactly two edits are made:
///
/// 1. the `--fallback-*` options are dropped, which is also what makes an
///    infinite re-exec chain impossible;
/// 2. every spelling of the whole-run timeout is dropped and a single
///    `--timeout=<stage1_ms>` put in its place.
///
/// The replacement goes before a `--` separator if one is present, so it can
/// never land in the trailing positional region.
fn stage1_args(raw_args: &[String], stage1_ms: u64) -> Result<Vec<String>, String> {
    let mut out: Vec<String> = Vec::with_capacity(raw_args.len() + 1);
    let mut skip_value = false;
    let mut after_separator = false;
    for arg in raw_args.iter().skip(1) {
        if skip_value {
            skip_value = false;
            continue;
        }
        if after_separator {
            out.push(arg.clone());
            continue;
        }
        if arg == "--" {
            after_separator = true;
            out.push(arg.clone());
            continue;
        }
        match classify_stage1_token(arg)? {
            Removal::Keep => out.push(arg.clone()),
            Removal::DropToken => {}
            Removal::DropTokenAndValue => skip_value = true,
        }
    }
    if skip_value {
        return Err("an option was given without its value".to_string());
    }

    let timeout_override = format!("--timeout={stage1_ms}");
    match out.iter().position(|arg| arg == "--") {
        Some(index) => out.insert(index, timeout_override.clone()),
        None => out.push(timeout_override.clone()),
    }

    // Fail closed rather than risk a re-exec chain or a second timeout: if
    // anything the driver owns survived the filter, do not spawn.
    if let Some(leftover) = out
        .iter()
        .take_while(|arg| arg.as_str() != "--")
        .find(|arg| {
            arg.starts_with("--fallback-")
                || (arg.starts_with("--timeout") && **arg != timeout_override)
        })
    {
        return Err(format!(
            "internal error: {leftover} survived stage-1 argument construction"
        ));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Verdict parsing
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

/// Classify one stdout line as a solver status line.
///
/// Accepts the DIMACS competition grammar (`s SATISFIABLE`) and the bare
/// SMT-LIB words AY prints outside a competition wrapper, so the driver reads
/// its own child correctly under either output policy.
fn classify_status_line(line: &str) -> Option<Verdict> {
    let line = line.trim_end();
    match line {
        "s SATISFIABLE" | "sat" => Some(Verdict::Sat),
        "s UNSATISFIABLE" | "unsat" => Some(Verdict::Unsat),
        "s UNKNOWN" | "unknown" => Some(Verdict::Unknown),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Stage 1: AY itself
// ---------------------------------------------------------------------------

struct Stage1Outcome {
    verdict: Option<Verdict>,
    /// The exact status line stage 1 printed, replayed verbatim if the
    /// composition ends up with nothing better to say.
    status_line: Option<String>,
    exit_code: i32,
}

impl Stage1Outcome {
    fn decisive(&self) -> bool {
        matches!(self.verdict, Some(Verdict::Sat) | Some(Verdict::Unsat))
    }
}

/// Relay stage 1's stdout, deciding as soon as its status line appears.
///
/// A decisive verdict is passed through byte for byte, including every `v` line
/// after it, and the composition is over. An `unknown` is withheld: the driver
/// may still have something better to print, and two status lines on one stdout
/// is a disqualifying transcript.
///
/// `c` comment lines are forwarded either way; they are comments in the
/// competition grammar, so forwarding them early can never conflict with a
/// later status line.
fn relay_stage1_stdout<R: Read>(reader: R) -> Stage1Outcome {
    let mut reader = BufReader::with_capacity(1 << 16, reader);
    let stdout = io::stdout();
    let mut sink = stdout.lock();
    let mut verdict: Option<Verdict> = None;
    let mut status_line: Option<String> = None;
    let mut buf: Vec<u8> = Vec::with_capacity(4096);

    loop {
        buf.clear();
        match reader.read_until(b'\n', &mut buf) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        let is_comment = buf.first() == Some(&b'c');
        if verdict.is_none() && !is_comment {
            if let Ok(text) = std::str::from_utf8(&buf) {
                if let Some(found) = classify_status_line(text) {
                    verdict = Some(found);
                    status_line = Some(text.trim_end().to_string());
                    if found == Verdict::Unknown {
                        // Withheld on purpose: the fallback may still answer.
                        continue;
                    }
                    let _ = sink.write_all(&buf);
                    continue;
                }
            }
        }
        // Suppress everything that trails a withheld `unknown` except comments;
        // pass everything else straight through.
        if verdict == Some(Verdict::Unknown) && !is_comment {
            continue;
        }
        let _ = sink.write_all(&buf);
    }
    let _ = sink.flush();

    Stage1Outcome {
        verdict,
        status_line,
        exit_code: 0,
    }
}

fn run_stage1(config: &ComposeConfig, budget: &ComposeBudget) -> Result<Stage1Outcome, String> {
    let exe = std::env::current_exe()
        .map_err(|error| format!("failed to resolve current executable: {error}"))?;
    let args = stage1_args(&config.raw_args, config.stage1_ms)?;

    let mut command = Command::new(&exe);
    command
        .args(&args)
        .stdin(Stdio::inherit())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());
    isolate_process_group(&mut command);
    #[cfg(unix)]
    {
        // Keep argv[0]: AY reads its own program name (a `z3`-named copy turns
        // on Z3 output conventions), and stage 1 must not differ from the run
        // the harness asked for.
        use std::os::unix::process::CommandExt as _;
        if let Some(argv0) = config.raw_args.first() {
            command.arg0(argv0);
        }
    }

    safe_eprintln!(
        "c compose: stage 1 = ay, budget {} ms of {} ms",
        config.stage1_ms,
        config.total_ms
    );
    // Snapshot BEFORE the spawn: anything matching that appears after this
    // instant is this stage's to clean up, and nothing else is.
    let snapshot = StagingSnapshot::take(&config.sweep_dirs());
    let mut child = command
        .spawn()
        .map_err(|error| format!("failed to launch the first stage: {error}"))?;
    let pid = i32::try_from(child.id()).unwrap_or(0);
    let mut guard = StageChildGuard::new(pid, snapshot);

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| "first stage produced no stdout pipe".to_string())?;
    // The relay must run concurrently with the wait: a model large enough to
    // fill the 64 KiB pipe buffer would otherwise deadlock the child against a
    // parent that is not reading.
    let relay = std::thread::Builder::new()
        .name("ay-compose-stage1".to_string())
        .spawn(move || relay_stage1_stdout(stdout))
        .map_err(|error| format!("failed to start the stage-1 relay: {error}"))?;

    let status = wait_with_deadline(&mut child, budget.stage1_remaining());
    guard.reaped();
    let mut outcome = relay
        .join()
        .map_err(|_| "the stage-1 relay thread panicked".to_string())?;
    outcome.exit_code = status
        .as_ref()
        .and_then(std::process::ExitStatus::code)
        .unwrap_or(0);

    safe_eprintln!(
        "c compose: stage 1 finished at {} ms with {}",
        budget.elapsed().as_millis(),
        outcome
            .status_line
            .as_deref()
            .unwrap_or("no status line (killed or crashed)")
    );
    drop(guard);

    // A stage 1 that exits with clap's usage code without ever solving means the
    // argument vector this driver built is not one AY accepts. Composing on top
    // of that would still produce answers — the fallback engine would supply
    // them — while AY silently never ran at all. That is a submission that has
    // quietly replaced its own solver, so it is fatal here, not a fallback.
    if outcome.status_line.is_none() && outcome.exit_code == CLAP_USAGE_EXIT_CODE {
        return Err(format!(
            "the first stage rejected its own argument vector (exit {CLAP_USAGE_EXIT_CODE}); \
             AY never ran. Refusing to let the fallback engine answer alone"
        ));
    }
    Ok(outcome)
}

/// Wait for a child, escalating SIGTERM then SIGKILL once `remaining` is spent.
/// Always reaps, so no zombie survives this function.
fn wait_with_deadline(child: &mut Child, remaining: Duration) -> Option<std::process::ExitStatus> {
    match child.wait_timeout(remaining) {
        Ok(Some(status)) => return Some(status),
        Ok(None) => {}
        Err(error) => {
            safe_eprintln!("c compose: wait failed ({error}); killing the stage child");
        }
    }
    let pid = i32::try_from(child.id()).unwrap_or(0);
    signal_pid(pid, Signal::Term);
    if let Ok(Some(status)) = child.wait_timeout(KILL_ESCALATION) {
        return Some(status);
    }
    let _ = child.kill();
    child.wait().ok()
}

// ---------------------------------------------------------------------------
// Stage 2: the second engine
// ---------------------------------------------------------------------------

struct FallbackVerdict {
    verdict: Option<Verdict>,
    /// Literals the engine printed on its `v` lines, in file order.
    model_literals: Vec<i32>,
}

/// Read the second engine's stdout: keep the status line and the model, send
/// its commentary to stderr so this process's stdout stays entirely ours.
fn read_fallback_stdout<R: Read>(reader: R) -> FallbackVerdict {
    let mut reader = BufReader::with_capacity(1 << 16, reader);
    let mut verdict = None;
    let mut model_literals = Vec::new();
    let mut buf: Vec<u8> = Vec::with_capacity(4096);

    loop {
        buf.clear();
        match reader.read_until(b'\n', &mut buf) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        let Ok(text) = std::str::from_utf8(&buf) else {
            continue;
        };
        let trimmed = text.trim_end();
        if trimmed.starts_with('c') {
            safe_eprintln!("{trimmed}");
            continue;
        }
        if verdict.is_none() {
            if let Some(found) = classify_status_line(trimmed) {
                verdict = Some(found);
                continue;
            }
        }
        if let Some(rest) = trimmed.strip_prefix("v ") {
            for token in rest.split_whitespace() {
                match token.parse::<i32>() {
                    Ok(0) => {}
                    Ok(literal) => model_literals.push(literal),
                    Err(_) => {
                        safe_eprintln!("c compose: unparsable model token {token:?} discarded");
                    }
                }
            }
        }
    }

    FallbackVerdict {
        verdict,
        model_literals,
    }
}

/// The whole reason the UNSAT leg is not shipped, in one place.
///
/// AY's SAT-COMP submission declares VeriPB as its proof checker and writes a
/// pseudo-Boolean derivation. A second engine emits DRAT. VeriPB cannot read
/// DRAT, so this process has no way to turn the second engine's refutation into
/// something its own declared checker accepts — and emitting `s UNSATISFIABLE`
/// with a proof file the declared checker rejects is disqualifying. Discarding
/// the answer costs instances; emitting it risks the submission.
///
/// The seam: a DRAT -> VeriPB translator would replace this call with a
/// translation of the second engine's proof, and only then may
/// `s UNSATISFIABLE` be printed. Nothing else in this file has to change.
fn refuse_fallback_unsat(engine: &Path) {
    safe_eprintln!(
        "c compose: REFUSING the fallback engine's UNSAT. {} emits DRAT; this submission \
         declares VeriPB, which cannot read it. An UNSAT this process cannot certify with \
         its own declared checker is never published. Reporting unknown instead.",
        engine.display()
    );
}

fn run_stage2(config: &ComposeConfig, budget: &ComposeBudget) -> Result<FallbackVerdict, String> {
    let remaining = budget.stage2_remaining();
    let mut command = Command::new(&config.fallback_solver);
    command
        .args(&config.fallback_args)
        .arg(&config.instance)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());
    isolate_process_group(&mut command);

    safe_eprintln!(
        "c compose: stage 2 = {}, budget {} ms (elapsed {} ms of {} ms)",
        config.fallback_solver.display(),
        remaining.as_millis(),
        budget.elapsed().as_millis(),
        config.total_ms
    );
    let snapshot = StagingSnapshot::take(&config.sweep_dirs());
    let mut child = command.spawn().map_err(|error| {
        format!(
            "failed to launch the fallback engine {}: {error}",
            config.fallback_solver.display()
        )
    })?;
    let pid = i32::try_from(child.id()).unwrap_or(0);
    let mut guard = StageChildGuard::new(pid, snapshot);

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| "the fallback engine produced no stdout pipe".to_string())?;
    let reader = std::thread::Builder::new()
        .name("ay-compose-stage2".to_string())
        .spawn(move || read_fallback_stdout(stdout))
        .map_err(|error| format!("failed to start the stage-2 reader: {error}"))?;

    let _status = wait_with_deadline(&mut child, budget.stage2_remaining());
    guard.reaped();
    let outcome = reader
        .join()
        .map_err(|_| "the stage-2 reader thread panicked".to_string())?;
    drop(guard);
    Ok(outcome)
}

// ---------------------------------------------------------------------------
// Model check against the ORIGINAL CNF
// ---------------------------------------------------------------------------

/// Result of checking an assignment against every clause of the original file.
pub(crate) struct ModelCheck {
    pub satisfied: bool,
    pub clauses: u64,
    /// 1-based: `values[v - 1]` is the polarity assigned to variable `v`.
    pub values: Vec<bool>,
    pub detail: Option<String>,
}

/// Check an assignment against the ORIGINAL CNF, streaming.
///
/// This is the whole soundness argument for the SAT leg, so it is deliberately
/// independent of the solver: it re-reads the file the harness named and
/// evaluates every clause in it. It shares no parser, no data structure and no
/// preprocessing with either engine.
///
/// Variables the second engine did not mention are assigned FALSE and included
/// in the emitted model, so the answer is a total assignment and the check is a
/// complete check, not a spot check.
///
/// Memory is one bit-ish per variable plus a 1 MiB read buffer; the file itself
/// is never held.
pub(crate) fn check_model_against_cnf(cnf: &Path, literals: &[i32]) -> io::Result<ModelCheck> {
    let mut values: Vec<bool> = Vec::new();
    let mut assigned: Vec<bool> = Vec::new();
    let mut conflict: Option<String> = None;
    for &literal in literals {
        let Some(var) = literal.unsigned_abs().checked_sub(1) else {
            continue;
        };
        let var = var as usize;
        if var >= values.len() {
            values.resize(var + 1, false);
            assigned.resize(var + 1, false);
        }
        let polarity = literal > 0;
        if assigned[var] && values[var] != polarity && conflict.is_none() {
            conflict = Some(format!(
                "the fallback engine assigned variable {} both polarities",
                var + 1
            ));
        }
        values[var] = polarity;
        assigned[var] = true;
    }
    if let Some(detail) = conflict {
        return Ok(ModelCheck {
            satisfied: false,
            clauses: 0,
            values,
            detail: Some(detail),
        });
    }

    let file = std::fs::File::open(cnf)?;
    let mut reader = BufReader::with_capacity(1 << 20, file);

    let mut clauses: u64 = 0;
    let mut clause_satisfied = false;
    let mut clause_open = false;
    let mut first_unsatisfied: Option<u64> = None;

    // Token scanner state, carried across read-buffer boundaries so a clause
    // that straddles a 1 MiB boundary parses identically to one that does not.
    let mut in_number = false;
    let mut negative = false;
    let mut magnitude: u64 = 0;
    let mut at_line_start = true;
    let mut skipping_line = false;
    // `%` is the SATLIB end-of-formula marker; the `0` that conventionally
    // follows it is a trailer, not an empty clause. Stop the scan there.
    let mut halted = false;

    'read: loop {
        let chunk = reader.fill_buf()?;
        if chunk.is_empty() {
            break;
        }
        let consumed = chunk.len();
        for &byte in chunk {
            if skipping_line {
                if byte == b'\n' {
                    skipping_line = false;
                    at_line_start = true;
                }
                continue;
            }
            match byte {
                b'0'..=b'9' => {
                    at_line_start = false;
                    in_number = true;
                    magnitude = magnitude
                        .saturating_mul(10)
                        .saturating_add(u64::from(byte - b'0'));
                }
                b'-' => {
                    at_line_start = false;
                    in_number = true;
                    negative = true;
                }
                _ => {
                    if in_number {
                        let literal = magnitude;
                        in_number = false;
                        magnitude = 0;
                        let signed_negative = negative;
                        negative = false;
                        if literal == 0 {
                            // EVERY `0` closes a clause, including one with no
                            // literals. An empty clause makes the formula
                            // unsatisfiable, so skipping it would let this
                            // checker accept a "model" of a refuted formula.
                            clauses += 1;
                            if !clause_satisfied && first_unsatisfied.is_none() {
                                first_unsatisfied = Some(clauses);
                            }
                            clause_open = false;
                            clause_satisfied = false;
                        } else {
                            clause_open = true;
                            let var = usize::try_from(literal - 1).unwrap_or(usize::MAX);
                            if var >= values.len() {
                                // Undeclared by the engine: FALSE, and part of
                                // the model this process will emit.
                                values.resize(var + 1, false);
                                assigned.resize(var + 1, false);
                            }
                            if values[var] != signed_negative {
                                clause_satisfied = true;
                            }
                        }
                    }
                    if byte == b'\n' {
                        at_line_start = true;
                    } else if at_line_start && (byte == b'c' || byte == b'p') {
                        skipping_line = true;
                    } else if at_line_start && byte == b'%' {
                        halted = true;
                        reader.consume(consumed);
                        break 'read;
                    } else if !byte.is_ascii_whitespace() {
                        at_line_start = false;
                    }
                }
            }
        }
        reader.consume(consumed);
    }
    // A final literal with no trailing whitespace.
    if in_number && !halted {
        if magnitude == 0 {
            clauses += 1;
            if !clause_satisfied && first_unsatisfied.is_none() {
                first_unsatisfied = Some(clauses);
            }
            clause_open = false;
        } else {
            clause_open = true;
            let var = usize::try_from(magnitude - 1).unwrap_or(usize::MAX);
            if var >= values.len() {
                values.resize(var + 1, false);
            }
            if values[var] != negative {
                clause_satisfied = true;
            }
        }
    }
    if clause_open {
        // A clause with no terminating `0`. Count it and judge it; a truncated
        // final clause must never be silently dropped.
        clauses += 1;
        if !clause_satisfied && first_unsatisfied.is_none() {
            first_unsatisfied = Some(clauses);
        }
    }

    let detail = first_unsatisfied
        .map(|index| format!("clause {index} of {clauses} is not satisfied by the model"));
    Ok(ModelCheck {
        satisfied: first_unsatisfied.is_none() && clauses > 0,
        clauses,
        values,
        detail: if clauses == 0 {
            Some("the original CNF contains no clauses".to_string())
        } else {
            detail
        },
    })
}

/// Emit `v` lines in the SAT-competition wrapping.
fn emit_model_lines(values: &[bool]) {
    let stdout = io::stdout();
    let mut sink = io::BufWriter::with_capacity(1 << 20, stdout.lock());
    let mut line = String::from("v");
    for (index, &polarity) in values.iter().enumerate() {
        let variable = index + 1;
        let token = if polarity {
            format!(" {variable}")
        } else {
            format!(" -{variable}")
        };
        if line.len() + token.len() > 78 {
            let _ = writeln!(sink, "{line}");
            line = String::from("v");
        }
        line.push_str(&token);
    }
    if line.len() > 1 {
        let _ = writeln!(sink, "{line}");
    }
    let _ = writeln!(sink, "v 0");
    let _ = sink.flush();
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

impl ComposeConfig {
    /// Directories in which a stage child could have staged a proof file.
    fn sweep_dirs(&self) -> Vec<PathBuf> {
        let mut dirs: Vec<PathBuf> = Vec::new();
        let mut push = |path: Option<&Path>| {
            if let Some(parent) = path.and_then(Path::parent) {
                let parent = if parent.as_os_str().is_empty() {
                    Path::new(".")
                } else {
                    parent
                };
                if !dirs.iter().any(|existing| existing == parent) {
                    dirs.push(parent.to_path_buf());
                }
            }
        };
        push(self.proof_path.as_deref());
        push(Some(self.instance.as_path()));
        dirs
    }
}

/// Validate the composition before anything is spawned. Fails closed: every
/// rejection here is a run that would otherwise have silently mis-split its
/// budget or composed on an input the model check cannot read.
fn validate(config: &ComposeConfig, reserve_ms: u64) -> Result<(), String> {
    if !config.fallback_solver.is_file() {
        return Err(format!(
            "--fallback-solver {} is not a file",
            config.fallback_solver.display()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        let executable = std::fs::metadata(&config.fallback_solver)
            .map(|meta| meta.permissions().mode() & 0o111 != 0)
            .unwrap_or(false);
        if !executable {
            return Err(format!(
                "--fallback-solver {} is not executable",
                config.fallback_solver.display()
            ));
        }
    }
    if !config.instance.is_file() {
        return Err(format!(
            "the composed solve needs a readable input file; {} is not one",
            config.instance.display()
        ));
    }
    if !looks_like_dimacs(&config.instance) {
        return Err(format!(
            "--fallback-solver composes two DIMACS engines on the SAME file, and {} does not \
             start with a `p cnf` header",
            config.instance.display()
        ));
    }
    if config.stage1_ms == 0 {
        return Err("--fallback-after must be positive".to_string());
    }
    let stage2_ms = config
        .total_ms
        .saturating_sub(config.stage1_ms)
        .saturating_sub(reserve_ms);
    if stage2_ms < MIN_STAGE2_MS {
        return Err(format!(
            "the split leaves the fallback engine {stage2_ms} ms: --timeout {} minus \
             --fallback-after {} minus a {reserve_ms} ms publication reserve. Widen --timeout \
             or lower --fallback-after (at least {MIN_STAGE2_MS} ms are needed)",
            config.total_ms, config.stage1_ms
        ));
    }
    Ok(())
}

/// Cheap sniff for a DIMACS CNF header, so a composed run on an SMT-LIB or
/// compressed input is rejected up front instead of at model-check time.
fn looks_like_dimacs(path: &Path) -> bool {
    let Ok(file) = std::fs::File::open(path) else {
        return false;
    };
    let mut reader = BufReader::with_capacity(1 << 16, file);
    let mut line = String::new();
    for _ in 0..4096 {
        line.clear();
        match reader.read_line(&mut line) {
            Ok(0) | Err(_) => return false,
            Ok(_) => {}
        }
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        return trimmed.starts_with("p cnf");
    }
    false
}

/// Print the verdict the composition ended up with and leave the process.
fn finish_unknown(stage1: &Stage1Outcome) -> ! {
    // Replaying stage 1's own line (and its own exit code) is what makes a
    // composed run that gains nothing byte-identical on stdout to today's run.
    if !crate::mark_verdict_printed() {
        match stage1.status_line.as_deref() {
            Some(line) => safe_println!("{line}"),
            None => safe_println!("s UNKNOWN"),
        }
    }
    let code = match stage1.status_line {
        Some(_) => stage1.exit_code,
        None => crate::timeout_exit_code_for_sat_competition_wrapper(
            crate::sat_competition_wrapper_timeout_policy(),
        ),
    };
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(code);
}

/// Entry point. Never returns.
pub(crate) fn run_composed_solve(config: &ComposeConfig) -> ! {
    let started = Instant::now();
    let cnf_bytes = std::fs::metadata(&config.instance)
        .map(|meta| meta.len())
        .unwrap_or(0);
    let reserve_ms = output_reserve_ms(cnf_bytes);

    if let Err(error) = validate(config, reserve_ms) {
        safe_eprintln!("Error: {error}");
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(1);
    }

    install_stage_child_reaper();
    let budget = ComposeBudget::new(started, config.stage1_ms, config.total_ms, reserve_ms);

    let stage1 = match run_stage1(config, &budget) {
        Ok(outcome) => outcome,
        Err(error) => {
            // Fatal on purpose. Every error reaching here means AY itself did
            // not get its budget, and a composition that answers with the
            // fallback engine alone is not the solver this submission is.
            safe_eprintln!("Error: composed solve: {error}");
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(1);
        }
    };

    if stage1.decisive() {
        // AY answered. Its verdict and model/proof are already on stdout and at
        // the proof path; the composition adds nothing and changes nothing.
        crate::mark_verdict_printed();
        crate::mark_decisive_verdict_printed();
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(stage1.exit_code);
    }

    if budget.stage2_remaining() < Duration::from_millis(MIN_STAGE2_MS) {
        safe_eprintln!(
            "c compose: only {} ms left after stage 1; not starting the fallback engine",
            budget.stage2_remaining().as_millis()
        );
        finish_unknown(&stage1);
    }

    let stage2 = match run_stage2(config, &budget) {
        Ok(outcome) => outcome,
        Err(error) => {
            safe_eprintln!("c compose: {error}");
            finish_unknown(&stage1);
        }
    };

    match stage2.verdict {
        Some(Verdict::Unsat) => {
            refuse_fallback_unsat(&config.fallback_solver);
            finish_unknown(&stage1);
        }
        Some(Verdict::Sat) => {}
        _ => {
            safe_eprintln!(
                "c compose: the fallback engine returned no verdict within its budget \
                 ({} ms elapsed of {} ms)",
                budget.elapsed().as_millis(),
                config.total_ms
            );
            finish_unknown(&stage1);
        }
    }

    let check = match check_model_against_cnf(&config.instance, &stage2.model_literals) {
        Ok(check) => check,
        Err(error) => {
            safe_eprintln!(
                "c compose: could not re-read {} to check the fallback model ({error}); \
                 withholding the SAT verdict",
                config.instance.display()
            );
            finish_unknown(&stage1);
        }
    };

    if !check.satisfied {
        // The fallback said SAT and was wrong, or its model did not survive the
        // budget. Either way it never becomes a verdict.
        safe_eprintln!(
            "c compose: REJECTED the fallback model: {}",
            check
                .detail
                .as_deref()
                .unwrap_or("it does not satisfy the original formula")
        );
        finish_unknown(&stage1);
    }

    safe_eprintln!(
        "c compose: fallback model verified against all {} clauses of {} ({} variables, \
         {} ms elapsed of {} ms)",
        check.clauses,
        config.instance.display(),
        check.values.len(),
        budget.elapsed().as_millis(),
        config.total_ms
    );

    if crate::mark_verdict_printed() {
        // Something already published a verdict (a watchdog racing us at the
        // budget edge). Never print a second status line.
        let _ = io::stdout().flush();
        std::process::exit(crate::dimacs_verdict_exit_code(10));
    }
    crate::mark_decisive_verdict_printed();
    safe_println!("s SATISFIABLE");
    emit_model_lines(&check.values);
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(crate::dimacs_verdict_exit_code(10));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    #[test]
    fn stage1_args_drop_the_drivers_own_flags_and_override_the_timeout() {
        let raw = strings(&[
            "/opt/ay",
            "solve",
            "--proof",
            "/out/proof.out",
            "--fallback-solver",
            "/opt/kissat",
            "--fallback-after",
            "1200000",
            "--fallback-arg",
            "--quiet",
            "--timeout=1500000",
            "/bench/x.cnf",
        ]);
        let built = stage1_args(&raw, 1_200_000).expect("built");
        assert!(!built.iter().any(|arg| arg.starts_with("--fallback-")));
        assert!(!built.iter().any(|arg| arg == "/opt/kissat"));
        assert!(!built.iter().any(|arg| arg == "1200000"));
        assert_eq!(
            built
                .iter()
                .filter(|arg| arg.starts_with("--timeout"))
                .count(),
            1
        );
        assert_eq!(built.last().map(String::as_str), Some("--timeout=1200000"));
        assert!(built.contains(&"/bench/x.cnf".to_string()));
        assert!(built.contains(&"--proof".to_string()));
        assert!(built.contains(&"/out/proof.out".to_string()));
    }

    #[test]
    fn stage1_args_handle_the_equals_spelling() {
        let raw = strings(&[
            "ay",
            "solve",
            "--fallback-solver=/opt/kissat",
            "--fallback-after=1000",
            "x.cnf",
        ]);
        let built = stage1_args(&raw, 1000).expect("built");
        assert_eq!(built, strings(&["solve", "x.cnf", "--timeout=1000"]));
    }

    #[test]
    fn stage1_args_insert_before_a_double_dash() {
        let raw = strings(&["ay", "solve", "--", "x.cnf"]);
        let built = stage1_args(&raw, 42).expect("built");
        assert_eq!(built, strings(&["solve", "--timeout=42", "--", "x.cnf"]));
    }

    #[test]
    fn stage1_args_reject_a_dangling_option() {
        assert!(stage1_args(&strings(&["ay", "solve", "--fallback-after"]), 1).is_err());
    }

    /// The rewrite has to survive CLAP, not just look right in the vector.
    /// clap rejects a repeated `--timeout` outright, so a stage-1 vector
    /// carrying both the harness's timeout and the driver's would exit 2 and
    /// never solve — with the fallback engine quietly answering in AY's place.
    /// Every spelling of the option is exercised here for that reason.
    #[test]
    fn every_timeout_spelling_is_replaced_and_clap_accepts_the_result() {
        use clap::Parser as _;
        for spelling in [
            vec!["-t", "1500000"],
            vec!["-t1500000"],
            vec!["--timeout", "1500000"],
            vec!["--timeout=1500000"],
        ] {
            let mut raw = strings(&["ay", "solve"]);
            raw.extend(strings(&spelling));
            raw.extend(strings(&[
                "--fallback-solver",
                "/opt/kissat",
                "--fallback-after",
                "1200000",
                "x.cnf",
            ]));
            let built = stage1_args(&raw, 1_200_000)
                .unwrap_or_else(|error| panic!("{spelling:?}: {error}"));
            let mut argv = vec!["ay".to_string()];
            argv.extend(built);
            let cli = crate::Cli::try_parse_from(&argv)
                .unwrap_or_else(|error| panic!("{spelling:?}: clap rejected the vector: {error}"));
            let Some(crate::Command::Solve(args)) = cli.command else {
                panic!("expected a solve command");
            };
            assert_eq!(args.timeout, Some(1_200_000), "{spelling:?}");
            assert!(args.fallback_solver.is_none(), "{spelling:?}");
            assert_eq!(
                args.file.as_deref(),
                Some(Path::new("x.cnf")),
                "{spelling:?}"
            );
        }
    }

    #[test]
    fn a_short_cluster_hiding_the_timeout_is_refused_rather_than_guessed() {
        let raw = strings(&["ay", "solve", "-qt", "1500000", "x.cnf"]);
        let error = stage1_args(&raw, 1000).expect_err("must refuse");
        assert!(error.contains("short-flag cluster"), "{error}");
    }

    #[test]
    fn status_lines_are_classified_under_both_output_policies() {
        assert_eq!(classify_status_line("s SATISFIABLE\n"), Some(Verdict::Sat));
        assert_eq!(
            classify_status_line("s UNSATISFIABLE"),
            Some(Verdict::Unsat)
        );
        assert_eq!(classify_status_line("s UNKNOWN"), Some(Verdict::Unknown));
        assert_eq!(classify_status_line("sat"), Some(Verdict::Sat));
        assert_eq!(classify_status_line("unsat"), Some(Verdict::Unsat));
        assert_eq!(classify_status_line("c s SATISFIABLE"), None);
        assert_eq!(classify_status_line("v 1 -2 0"), None);
    }

    #[test]
    fn a_withheld_unknown_never_reaches_the_relay_output() {
        let out = relay_stage1_stdout(&b"c hello\ns UNKNOWN\n"[..]);
        assert_eq!(out.verdict, Some(Verdict::Unknown));
        assert_eq!(out.status_line.as_deref(), Some("s UNKNOWN"));
    }

    #[test]
    fn a_decisive_stage1_verdict_is_recognised_with_its_model() {
        let out = relay_stage1_stdout(&b"c x\ns SATISFIABLE\nv 1 -2 0\n"[..]);
        assert_eq!(out.verdict, Some(Verdict::Sat));
        assert!(out.decisive());
    }

    #[test]
    fn the_fallback_reader_keeps_the_model_and_drops_commentary() {
        let text = b"c kissat\ns SATISFIABLE\nv 1 -2 3 0\nv 0\n";
        let out = read_fallback_stdout(&text[..]);
        assert_eq!(out.verdict, Some(Verdict::Sat));
        assert_eq!(out.model_literals, vec![1, -2, 3]);
    }

    fn write_cnf(name: &str, body: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("ay-compose-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(name);
        std::fs::write(&path, body).expect("write cnf");
        path
    }

    #[test]
    fn a_satisfying_assignment_is_accepted() {
        let cnf = write_cnf("ok.cnf", "c a comment\np cnf 3 2\n1 -2 0\n2 3 0\n");
        let check = check_model_against_cnf(&cnf, &[1, 2, 3]).expect("check");
        assert!(check.satisfied, "{:?}", check.detail);
        assert_eq!(check.clauses, 2);
        assert_eq!(check.values, vec![true, true, true]);
    }

    #[test]
    fn a_non_satisfying_assignment_is_rejected() {
        let cnf = write_cnf("bad.cnf", "p cnf 2 2\n1 0\n-1 0\n");
        let check = check_model_against_cnf(&cnf, &[1]).expect("check");
        assert!(!check.satisfied);
        assert!(check.detail.unwrap().contains("clause 2"));
    }

    /// A clause mentioning a variable the engine never printed must not be
    /// waved through: the missing variable is pinned to FALSE and the clause is
    /// judged under that.
    #[test]
    fn variables_the_engine_omitted_are_pinned_false_and_judged() {
        let cnf = write_cnf("short.cnf", "p cnf 3 1\n3 0\n");
        let check = check_model_against_cnf(&cnf, &[1, 2]).expect("check");
        assert!(!check.satisfied);
        assert_eq!(check.values.len(), 3);

        let cnf = write_cnf("short2.cnf", "p cnf 3 1\n-3 0\n");
        let check = check_model_against_cnf(&cnf, &[1, 2]).expect("check");
        assert!(check.satisfied);
        assert_eq!(check.values, vec![true, true, false]);
    }

    #[test]
    fn clauses_spanning_lines_and_trailing_junk_parse() {
        let cnf = write_cnf("multi.cnf", "p cnf 4 2\n1\n  -2\n 0\n3 4 0\n%\n0\n");
        let check = check_model_against_cnf(&cnf, &[-1, -2, 3, -4]).expect("check");
        assert!(check.satisfied, "{:?}", check.detail);
        assert_eq!(check.clauses, 2);
    }

    /// An empty clause refutes the formula outright. A checker that skipped it
    /// would let the composition publish `s SATISFIABLE` for an UNSAT input,
    /// which is the single worst outcome this module could produce.
    #[test]
    fn an_empty_clause_is_never_skipped() {
        let cnf = write_cnf("empty.cnf", "p cnf 1 2\n1 0\n0\n");
        let check = check_model_against_cnf(&cnf, &[1]).expect("check");
        assert!(!check.satisfied);
        assert_eq!(check.clauses, 2);
        assert!(check.detail.unwrap().contains("clause 2"));
    }

    #[test]
    fn a_contradictory_model_is_rejected_before_any_file_read() {
        let cnf = write_cnf("unused.cnf", "p cnf 1 1\n1 0\n");
        let check = check_model_against_cnf(&cnf, &[1, -1]).expect("check");
        assert!(!check.satisfied);
        assert!(check.detail.unwrap().contains("both polarities"));
    }

    #[test]
    fn budget_deadlines_never_exceed_the_total() {
        let started = Instant::now();
        let budget = ComposeBudget::new(started, 1_200_000, 1_500_000, 2_000);
        assert_eq!(budget.stage2_wall, Duration::from_secs(1_498));
        assert_eq!(budget.stage1_wall, Duration::from_secs(1_205));
        assert!(budget.stage1_wall <= budget.stage2_wall);

        // A first stage that asks for the whole budget is clamped, not honoured.
        let budget = ComposeBudget::new(started, 1_500_000, 1_500_000, 2_000);
        assert_eq!(budget.stage1_wall, Duration::from_secs(1_498));
        assert_eq!(budget.stage2_wall, Duration::from_secs(1_498));
    }

    #[test]
    fn the_reserve_grows_with_the_file_and_is_capped() {
        assert_eq!(output_reserve_ms(0), OUTPUT_RESERVE_BASE_MS);
        assert_eq!(
            output_reserve_ms(100 * 1024 * 1024),
            OUTPUT_RESERVE_BASE_MS + 1_000
        );
        assert_eq!(output_reserve_ms(u64::MAX / 2), OUTPUT_RESERVE_CAP_MS);
    }

    fn validatable_config(stage1_ms: u64, total_ms: u64, instance: PathBuf) -> ComposeConfig {
        ComposeConfig {
            instance,
            // A real executable, so validation reaches the checks under test
            // instead of stopping at "is not a file".
            fallback_solver: PathBuf::from("/bin/sh"),
            fallback_args: Vec::new(),
            stage1_ms,
            total_ms,
            raw_args: Vec::new(),
            proof_path: None,
        }
    }

    #[test]
    fn a_split_that_starves_the_fallback_is_refused() {
        let cnf = write_cnf("validate.cnf", "p cnf 1 1\n1 0\n");
        let good = validatable_config(1_200_000, 1_500_000, cnf.clone());
        validate(&good, 2_000).expect("a 1200/1500 split is accepted");

        let starved = validatable_config(1_499_000, 1_500_000, cnf);
        let error = validate(&starved, 2_000).expect_err("must refuse");
        assert!(error.contains("leaves the fallback engine"), "{error}");
    }

    /// The composition runs two DIMACS engines on one file. An input the model
    /// check cannot read must be refused before either engine starts, not
    /// discovered after the second one has already answered.
    #[test]
    fn a_non_dimacs_input_is_refused_up_front() {
        let smt = write_cnf("input.smt2", "(set-logic QF_BV)\n(check-sat)\n");
        let config = validatable_config(1_000, 100_000, smt);
        let error = validate(&config, 2_000).expect_err("must refuse");
        assert!(error.contains("p cnf"), "{error}");
    }

    /// The sweep must remove what THIS stage stranded — including artifacts
    /// named after a grandchild PID the driver never saw — while leaving both
    /// pre-existing orphans and a concurrent run's live files alone.
    #[test]
    fn the_staging_sweep_removes_only_this_stages_orphans() {
        let dir = std::env::temp_dir().join(format!("ay-compose-sweep-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("temp dir");

        // Present before the stage ran: not ours to delete, however dead.
        let pre_existing = dir.join(".ay-dimacs-proof-4242-0.stage");
        std::fs::write(&pre_existing, b"x").expect("write");

        let snapshot = StagingSnapshot::take(std::slice::from_ref(&dir));

        // Stranded during the stage by a DEAD producer (a grandchild PID, i.e.
        // not the pid the driver spawned) — both a file and a directory. The
        // PIDs are of children this test ran and reaped: fixed numbers can be
        // live processes on a busy host, and the sweep rightly spares those.
        let dead_pid = || {
            let mut child = Command::new("true")
                .spawn()
                .expect("spawn a short-lived child");
            let pid = child.id();
            child.wait().expect("reap the child");
            pid
        };
        let stranded_file = dir.join(format!(".ay-dimacs-proof-{}-0.stage", dead_pid()));
        let stranded_dir = dir.join(format!(".ay-dimacs-proof-{}-1", dead_pid()));
        std::fs::write(&stranded_file, b"x").expect("write");
        std::fs::create_dir_all(&stranded_dir).expect("mkdir");
        std::fs::write(stranded_dir.join("proof"), b"x").expect("write");
        // Created during the stage by a LIVE producer: a concurrent run.
        let live = dir.join(format!(".ay-dimacs-proof-{}-7.stage", std::process::id()));
        std::fs::write(&live, b"x").expect("write");

        snapshot.sweep_new_orphans();

        assert!(!stranded_file.exists(), "a stranded file must be removed");
        assert!(
            !stranded_dir.exists(),
            "a stranded directory must be removed"
        );
        assert!(
            pre_existing.exists(),
            "an orphan that predates this run is not ours to delete"
        );
        assert!(
            live.exists(),
            "a concurrent run's live staging file must never be touched"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn staging_entry_pids_are_parsed_from_both_artifact_shapes() {
        use std::ffi::OsStr;
        assert_eq!(
            staging_entry_pid(OsStr::new(".ay-dimacs-proof-84667-0.stage")),
            Some(84667)
        );
        assert_eq!(
            staging_entry_pid(OsStr::new(".ay-dimacs-proof-10141-128")),
            Some(10141)
        );
        assert_eq!(staging_entry_pid(OsStr::new("proof.out")), None);
    }
}
