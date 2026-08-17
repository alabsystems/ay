// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trial runner: invoke the `ay` binary as a subprocess with a chosen subset of
//! feature-disable CLI flags and parse the `sat`/`unsat`/`unknown` verdict from
//! stdout.
//!
//! Feature flags are passed as CLI arguments (`--no-bve`, `--no-vivify`, ...)
//! per the project's CLI-over-env-var convention. The only child environment
//! override is the resource planner's authoritative `NBCORE` budget.

use std::collections::VecDeque;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use crate::error::{BisectError, Result};

/// The expected verdict the user wants ay to produce on the benchmark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expected {
    Sat,
    Unsat,
}

impl Expected {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

/// Outcome of a single ay invocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
    /// Trial exceeded the configured timeout; the child was killed.
    Timeout,
    /// Solver crashed or produced unparseable output.
    Error,
}

impl SolveResult {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
            Self::Timeout => "timeout",
            Self::Error => "error",
        }
    }

    /// Does this result match the expected verdict exactly? `Timeout`,
    /// `Unknown` and `Error` never match.
    #[must_use]
    pub fn matches(self, expected: Expected) -> bool {
        matches!(
            (self, expected),
            (Self::Sat, Expected::Sat) | (Self::Unsat, Expected::Unsat)
        )
    }
}

/// Abstract trial runner. Implementors return the solver verdict for a given
/// flag subset. Separated from the concrete `ay`-subprocess runner so that
/// unit tests can inject deterministic mock oracles.
pub trait TrialRunner: Send + Sync {
    /// Execute one trial with `flags` passed as CLI args. Implementations must
    /// never panic; errors surface as `Err`.
    fn run(&self, flags: &[&str]) -> Result<SolveResult>;
}

/// Concrete runner that shells out to the `ay` binary.
pub struct CliRunner {
    binary: PathBuf,
    smt2_file: PathBuf,
    timeout: Duration,
    verbose: bool,
    memory_mb: Option<usize>,
    nbcore: Option<usize>,
}

impl CliRunner {
    /// Construct a runner.
    ///
    /// `binary` is the path to the `ay` executable; `smt2_file` is the
    /// benchmark to solve. `timeout` bounds each trial.
    #[must_use]
    pub fn new(binary: PathBuf, smt2_file: PathBuf, timeout: Duration, verbose: bool) -> Self {
        Self {
            binary,
            smt2_file,
            timeout,
            verbose,
            memory_mb: None,
            nbcore: None,
        }
    }

    /// Apply the `_oom_guard.py` envelope to every trial.
    #[must_use]
    pub fn with_resource_plan(mut self, plan: &crate::ResourcePlan) -> Self {
        self.memory_mb = (plan.memlimit_mb_per_child > 0).then_some(plan.memlimit_mb_per_child);
        self.nbcore = Some(plan.nbcore_per_child.max(1));
        self
    }
}

impl TrialRunner for CliRunner {
    fn run(&self, flags: &[&str]) -> Result<SolveResult> {
        if self.verbose {
            eprintln!(
                "[ay-bisect] trial: {} {} {}",
                self.binary.display(),
                self.memory_mb
                    .map(|memory| format!("--memory {memory} "))
                    .unwrap_or_default()
                    + &flags.join(" "),
                self.smt2_file.display()
            );
        }

        let mut cmd = Command::new(&self.binary);
        if let Some(memory_mb) = self.memory_mb {
            cmd.arg("--memory").arg(memory_mb.to_string());
        }
        if let Some(nbcore) = self.nbcore {
            cmd.env("NBCORE", nbcore.to_string());
        }
        // Subcommand-level flags belong to `ay solve`; the binary also accepts
        // them without an explicit subcommand because `preprocess_args` injects
        // `solve` when the first non-flag arg is a file path.
        for f in flags {
            cmd.arg(f);
        }
        cmd.arg(&self.smt2_file);
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());
        isolate_process_group(&mut cmd);

        let mut child = cmd.spawn().map_err(|e| BisectError::SpawnFailed {
            binary: self.binary.display().to_string(),
            source: e,
        })?;

        match wait_with_timeout(&mut child, self.timeout)? {
            WaitOutcome::Exited { stdout, success } => Ok(parse_result(&stdout, success)),
            WaitOutcome::TimedOut => Ok(SolveResult::Timeout),
        }
    }
}

enum WaitOutcome {
    Exited { stdout: String, success: bool },
    TimedOut,
}

const CAPTURE_LIMIT_BYTES: usize = 1024 * 1024;
const CAPTURE_HEAD_BYTES: usize = CAPTURE_LIMIT_BYTES / 2;

struct PipeCapture {
    receiver: mpsc::Receiver<String>,
}

impl PipeCapture {
    fn start<R>(mut reader: R) -> Self
    where
        R: Read + Send + 'static,
    {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let mut head = Vec::with_capacity(CAPTURE_HEAD_BYTES);
            let mut tail = VecDeque::with_capacity(CAPTURE_LIMIT_BYTES - CAPTURE_HEAD_BYTES);
            let tail_cap = CAPTURE_LIMIT_BYTES - CAPTURE_HEAD_BYTES;
            let mut total = 0usize;
            let mut chunk = [0u8; 8192];
            loop {
                let read = match reader.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(read) => read,
                };
                total = total.saturating_add(read);
                let mut offset = 0;
                if head.len() < CAPTURE_HEAD_BYTES {
                    let keep = read.min(CAPTURE_HEAD_BYTES - head.len());
                    head.extend_from_slice(&chunk[..keep]);
                    offset = keep;
                }
                for byte in &chunk[offset..read] {
                    if tail.len() == tail_cap {
                        tail.pop_front();
                    }
                    tail.push_back(*byte);
                }
            }
            if !tail.is_empty() {
                if total > CAPTURE_LIMIT_BYTES {
                    head.extend_from_slice(b"\n[... output truncated ...]\n");
                }
                head.extend(tail);
            }
            let _ = sender.send(String::from_utf8_lossy(&head).into_owned());
        });
        Self { receiver }
    }

    fn finish(self) -> String {
        self.receiver
            .recv_timeout(Duration::from_secs(2))
            .unwrap_or_default()
    }
}

#[cfg(unix)]
fn isolate_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    command.process_group(0);
}

#[cfg(not(unix))]
fn isolate_process_group(_command: &mut Command) {}

fn terminate_process_group(child: &mut std::process::Child) {
    #[cfg(unix)]
    {
        if let Ok(pid) = i32::try_from(child.id()) {
            let pgid = nix::unistd::Pid::from_raw(pid);
            let _ = nix::sys::signal::killpg(pgid, nix::sys::signal::Signal::SIGKILL);
        }
    }
    #[cfg(not(unix))]
    {
        let _ = child.kill();
    }
    let _ = child.wait();
}

fn wait_with_timeout(child: &mut std::process::Child, timeout: Duration) -> Result<WaitOutcome> {
    let stdout_pipe = child.stdout.take().ok_or(BisectError::Internal {
        message: "child stdout pipe was not captured",
    })?;
    let stderr_pipe = child.stderr.take();
    let stdout_capture = PipeCapture::start(stdout_pipe);
    let stderr_capture = stderr_pipe.map(PipeCapture::start);

    let deadline = Instant::now() + timeout;
    loop {
        let child_status = match child.try_wait() {
            Ok(status) => status,
            Err(source) => {
                terminate_process_group(child);
                let _ = stdout_capture.finish();
                if let Some(capture) = stderr_capture {
                    let _ = capture.finish();
                }
                return Err(BisectError::SpawnFailed {
                    binary: "<child>".to_string(),
                    source,
                });
            }
        };
        match child_status {
            Some(status) => {
                // A wrapper may exit while descendants keep stdout/stderr
                // open. Reap the whole isolated group before collecting the
                // bounded captures. Capture threads are intentionally detached:
                // a broken platform pipe must never turn a receive timeout into
                // an unbounded thread join.
                terminate_process_group(child);
                let stdout = stdout_capture.finish();
                if let Some(capture) = stderr_capture {
                    let _ = capture.finish();
                }
                return Ok(WaitOutcome::Exited {
                    stdout,
                    success: status.success(),
                });
            }
            None => {
                if Instant::now() >= deadline {
                    terminate_process_group(child);
                    let _ = stdout_capture.finish();
                    if let Some(capture) = stderr_capture {
                        let _ = capture.finish();
                    }
                    return Ok(WaitOutcome::TimedOut);
                }
                thread::sleep(Duration::from_millis(50));
            }
        }
    }
}

/// Parse ay stdout into a [`SolveResult`].
///
/// ay prints `sat` / `unsat` / `unknown` on its own line. If the process
/// produced multiple verdicts (e.g. several `check-sat` calls) we take the
/// last, mirroring SMT-LIB semantics.
pub(crate) fn parse_result(stdout: &str, exit_ok: bool) -> SolveResult {
    // A process that printed a verdict and then crashed did not complete a
    // trustworthy trial. Never let stale buffered output mask that failure.
    if !exit_ok {
        return SolveResult::Error;
    }
    let mut last: Option<SolveResult> = None;
    for line in stdout.lines() {
        match line.trim() {
            "sat" => last = Some(SolveResult::Sat),
            "unsat" => last = Some(SolveResult::Unsat),
            "unknown" => last = Some(SolveResult::Unknown),
            _ => {}
        }
    }
    last.unwrap_or(SolveResult::Error)
}

/// Locate the ay binary. Preference order:
///   1. Explicit path passed by the caller.
///   2. `./target/release/ay` (walking upward from cwd).
///   3. `./target/debug/ay` (walking upward from cwd).
///   4. `ay` on `PATH`.
pub fn locate_ay_binary(explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(p) = explicit {
        if !p.exists() {
            return Err(BisectError::BinaryNotFound {
                path: p.display().to_string(),
            });
        }
        return Ok(p.to_path_buf());
    }

    let start = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut dir = start;
    loop {
        for candidate in [dir.join("target/release/ay"), dir.join("target/debug/ay")] {
            if candidate.exists() {
                return Ok(candidate);
            }
        }
        if !dir.pop() {
            break;
        }
    }

    if let Ok(output) = Command::new("which").arg("ay").output() {
        if output.status.success() {
            let raw = String::from_utf8_lossy(&output.stdout);
            let p = raw.trim().to_string();
            if !p.is_empty() {
                return Ok(PathBuf::from(p));
            }
        }
    }

    Err(BisectError::BinaryNotFound {
        path: "<auto-detect>".to_string(),
    })
}

#[cfg(test)]
mod tests;
