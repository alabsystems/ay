// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! # ay-bisect
//!
//! Feature-flag bisection harness for the AY SMT solver.
//!
//! Given a benchmark that produces the wrong answer on `ay`, this crate
//! searches over `ay`'s `--no-*` feature-disable CLI flags and finds the
//! minimal subset that, when passed, makes `ay` produce the expected
//! verdict. The resulting minimal set localises the culprit feature to a
//! small number of subsystems.
//!
//! ## Typical usage
//!
//! ```no_run
//! use std::path::PathBuf;
//! use std::time::Duration;
//! use ay_bisect::{bisect, BisectConfig, Expected};
//!
//! let cfg = BisectConfig::new(PathBuf::from("bug.smt2"), Expected::Sat)
//!     .with_timeout(Duration::from_secs(30))
//!     .with_jobs(4);
//! let result = bisect(&cfg).expect("bisect");
//! println!("minimal flags: {:?}", result.minimal_flags);
//! ```
//!
//! All feature selection happens via CLI arguments; this crate never reads or
//! writes `AY_NO_*` environment variables.

#![forbid(unsafe_code)]

pub mod cli;
pub mod error;
pub mod flags;
mod resource;
pub mod runner;
pub mod search;

pub use error::{BisectError, Result};
pub use flags::{subsystems_for, Subsystem, FLAGS};
pub use resource::ResourcePlan;
pub use runner::{locate_ay_binary, CliRunner, Expected, SolveResult, TrialRunner};

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct BinaryIdentity {
    path: String,
    summary: Option<String>,
}

impl BinaryIdentity {
    fn probe(path: &Path) -> Self {
        let mut identity = Self {
            path: canonical_display_path(path),
            ..Self::default()
        };

        let output = match Command::new(path).arg("--version").output() {
            Ok(output) if output.status.success() => output,
            _ => return identity,
        };
        let text = preferred_version_output(&output);
        if text.trim().is_empty() {
            return identity;
        }

        identity.summary = extract_build_field(&text, "build.stamp")
            .or_else(|| first_nonempty_version_line(&text));
        identity
    }

    fn fallback(cfg: &BisectConfig) -> Self {
        match cfg.ay_binary.as_deref() {
            Some(path) => Self::probe(path),
            None => Self {
                path: "ay".to_string(),
                ..Self::default()
            },
        }
    }
}

fn canonical_display_path(path: &Path) -> String {
    path.canonicalize()
        .unwrap_or_else(|_| path.to_path_buf())
        .display()
        .to_string()
}

fn preferred_version_output(output: &std::process::Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if !stdout.is_empty() {
        return stdout;
    }
    String::from_utf8_lossy(&output.stderr).trim().to_string()
}

fn extract_build_field(text: &str, key: &str) -> Option<String> {
    let prefix = format!("{key}=");
    text.lines()
        .map(str::trim)
        .find_map(|line| line.strip_prefix(&prefix).map(str::to_owned))
}

fn first_nonempty_version_line(text: &str) -> Option<String> {
    text.lines()
        .map(str::trim)
        .find(|line| {
            !line.is_empty()
                && !line.contains('=')
                && !matches!(*line, "sat" | "unsat" | "unknown" | "error")
        })
        .map(str::to_owned)
}

/// Configuration for a single bisect run.
///
/// Use the builder-style `with_*` methods to override the defaults:
/// * timeout: 30 seconds per trial
/// * jobs: 4 parallel trials
/// * ay binary: auto-located (see [`locate_ay_binary`])
#[derive(Debug, Clone)]
#[must_use = "BisectConfig must be passed to bisect() to take effect"]
pub struct BisectConfig {
    pub smt2_file: PathBuf,
    pub expected: Expected,
    pub timeout: Duration,
    pub jobs: usize,
    pub ay_binary: Option<PathBuf>,
    pub verbose: bool,
}

impl BisectConfig {
    /// Construct a new configuration with defaults.
    pub fn new(smt2_file: PathBuf, expected: Expected) -> Self {
        Self {
            smt2_file,
            expected,
            timeout: Duration::from_secs(30),
            jobs: 4,
            ay_binary: None,
            verbose: false,
        }
    }

    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    pub fn with_jobs(mut self, jobs: usize) -> Self {
        self.jobs = jobs;
        self
    }

    pub fn with_ay_binary(mut self, path: PathBuf) -> Self {
        self.ay_binary = Some(path);
        self
    }

    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

/// Outcome of a bisect run.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct BisectResult {
    /// Minimal subset of `--no-*` flags whose disabling makes ay produce the
    /// expected verdict. Empty if `ay` was already correct on the baseline.
    pub minimal_flags: Vec<String>,
    /// Distinct subsystems touched by the minimal flag set (e.g. `["sat"]`,
    /// `["sat", "theory"]`).
    pub subsystems: Vec<String>,
    /// Number of ay trials executed, including the baseline probe.
    pub trials: usize,
    /// Total wall-clock time the bisect spent, in milliseconds.
    pub wall_ms: u64,
    /// Whether the baseline (no `--no-*` flags) already produced the expected
    /// verdict — if so, `minimal_flags` is empty and there is nothing to
    /// debug.
    pub baseline_already_correct: bool,
    /// Whether disabling every known flag still failed to produce the
    /// expected verdict, indicating the bug is outside the flag set this
    /// harness controls.
    pub outside_flag_set: bool,
    /// Actual ay binary path used for all trials.
    ay_binary: String,
    /// Build/version summary extracted from `ay --version` when available.
    ay_build_summary: Option<String>,
    /// Exact `_oom_guard.py` envelope used by concrete AY subprocesses.
    /// Custom [`TrialRunner`] callers do not have a known child process and
    /// therefore report `None`.
    pub resource_plan: Option<ResourcePlan>,
}

impl BisectResult {
    /// Emit a human-readable report to a writer. Separated from the data so
    /// callers can customise formatting (JSON vs text).
    pub fn write_report(
        &self,
        w: &mut dyn std::io::Write,
        cfg: &BisectConfig,
    ) -> std::io::Result<()> {
        writeln!(w, "ay-bisect report")?;
        writeln!(w, "================")?;
        writeln!(w, "ay binary: {}", self.ay_binary)?;
        writeln!(
            w,
            "ay build:  {}",
            self.ay_build_summary
                .as_deref()
                .unwrap_or("(unavailable from --version)")
        )?;
        writeln!(w, "file:     {}", cfg.smt2_file.display())?;
        writeln!(w, "expected: {}", cfg.expected.as_str())?;
        writeln!(w, "trials:   {}", self.trials)?;
        writeln!(w, "wall_ms:  {}", self.wall_ms)?;
        if let Some(plan) = self.resource_plan.as_ref() {
            writeln!(
                w,
                "resources: jobs={} (requested {}) --memory={}MiB NBCORE={} headroom={}MiB",
                plan.jobs,
                plan.requested_jobs,
                plan.memlimit_mb_per_child,
                plan.nbcore_per_child,
                plan.headroom_mb,
            )?;
        }
        writeln!(w)?;
        if self.baseline_already_correct {
            writeln!(w, "Baseline already correct — nothing to bisect.")?;
            return Ok(());
        }
        if self.outside_flag_set {
            writeln!(
                w,
                "Bug reproduces with all known flags disabled — root cause is outside"
            )?;
            writeln!(w, "the flag set this harness controls.")?;
            return Ok(());
        }
        writeln!(
            w,
            "Minimal flag set ({} flag{}):",
            self.minimal_flags.len(),
            if self.minimal_flags.len() == 1 {
                ""
            } else {
                "s"
            }
        )?;
        for f in &self.minimal_flags {
            writeln!(w, "  {f}")?;
        }
        writeln!(w)?;
        writeln!(w, "Subsystems: {}", self.subsystems.join(", "))?;
        writeln!(w)?;
        writeln!(w, "Repro command:")?;
        write!(w, "  {}", self.ay_binary)?;
        if let Some(memory_mb) = self
            .resource_plan
            .as_ref()
            .map(|plan| plan.memlimit_mb_per_child)
            .filter(|memory_mb| *memory_mb > 0)
        {
            write!(w, " --memory {memory_mb}")?;
        }
        for f in &self.minimal_flags {
            write!(w, " {f}")?;
        }
        writeln!(w, " {}", cfg.smt2_file.display())?;
        Ok(())
    }
}

/// Run a bisect with the concrete CLI runner.
///
/// This is the primary public entry point. Internally it:
///   1. Locates the `ay` binary (explicit path → auto-detect).
///   2. Plans RAM-capped parallelism and builds a private Rayon pool.
///   3. Runs the baseline trial (no `--no-*` flags). If that already matches
///      the expected verdict, returns an empty result tagged
///      `baseline_already_correct`.
///   4. Runs a probe with every flag disabled. If that still doesn't match,
///      returns `outside_flag_set` with the full flag list.
///   5. Otherwise minimises the flag set via binary search.
pub fn bisect(cfg: &BisectConfig) -> Result<BisectResult> {
    if !cfg.smt2_file.exists() {
        return Err(BisectError::FileNotFound {
            path: cfg.smt2_file.clone(),
        });
    }

    let binary = locate_ay_binary(cfg.ay_binary.as_deref())?;
    let binary_identity = BinaryIdentity::probe(&binary);
    let resource_plan = resource::plan(cfg.jobs, &binary)?;
    eprintln!(
        "[ay-bisect] resource plan: requested_jobs={} jobs={} --memory={}MiB NBCORE={} headroom={}MiB",
        resource_plan.requested_jobs,
        resource_plan.jobs,
        resource_plan.memlimit_mb_per_child,
        resource_plan.nbcore_per_child,
        resource_plan.headroom_mb,
    );

    let smt2 = cfg
        .smt2_file
        .canonicalize()
        .unwrap_or_else(|_| cfg.smt2_file.clone());
    let runner =
        CliRunner::new(binary, smt2, cfg.timeout, cfg.verbose).with_resource_plan(&resource_plan);
    let pool = build_thread_pool(resource_plan.jobs)?;

    pool.install(|| bisect_with_runner_inner(&runner, cfg, &binary_identity, Some(&resource_plan)))
}

/// Run a bisect against a user-supplied runner. Useful for tests and for
/// callers that want to wrap `CliRunner` with logging or rate limiting.
pub fn bisect_with_runner(runner: &dyn TrialRunner, cfg: &BisectConfig) -> Result<BisectResult> {
    let binary_identity = BinaryIdentity::fallback(cfg);
    let pool = build_thread_pool(cfg.jobs.max(1))?;
    pool.install(|| bisect_with_runner_inner(runner, cfg, &binary_identity, None))
}

fn build_thread_pool(jobs: usize) -> Result<rayon::ThreadPool> {
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs.max(1))
        .build()
        .map_err(|error| BisectError::ThreadPool {
            message: error.to_string(),
        })
}

fn bisect_with_runner_inner(
    runner: &dyn TrialRunner,
    cfg: &BisectConfig,
    binary_identity: &BinaryIdentity,
    resource_plan: Option<&ResourcePlan>,
) -> Result<BisectResult> {
    let start = Instant::now();
    let trials = AtomicUsize::new(0);

    // Step 1: baseline probe with zero flags. If this already matches the
    // expected verdict, there is nothing to bisect — ay is correct.
    let baseline_verdict = {
        trials.fetch_add(1, Ordering::Relaxed);
        runner.run(&[])?
    };
    if cfg.verbose {
        eprintln!(
            "[ay-bisect] baseline (no --no-* flags): {}",
            baseline_verdict.as_str()
        );
    }
    if baseline_verdict.matches(cfg.expected) {
        return Ok(BisectResult {
            minimal_flags: Vec::new(),
            subsystems: Vec::new(),
            trials: trials.load(Ordering::Relaxed),
            wall_ms: start.elapsed().as_millis() as u64,
            baseline_already_correct: true,
            outside_flag_set: false,
            ay_binary: binary_identity.path.clone(),
            ay_build_summary: binary_identity.summary.clone(),
            resource_plan: resource_plan.cloned(),
        });
    }

    // Step 2: probe with ALL known flags disabled. If this still doesn't
    // match the expected verdict, the culprit is outside our flag set.
    let all_verdict = {
        trials.fetch_add(1, Ordering::Relaxed);
        runner.run(FLAGS)?
    };
    if cfg.verbose {
        eprintln!("[ay-bisect] all flags disabled: {}", all_verdict.as_str());
    }
    if !all_verdict.matches(cfg.expected) {
        let minimal_flags: Vec<String> = FLAGS.iter().map(|s| (*s).to_string()).collect();
        let subsystems = subsystems_for(&minimal_flags);
        return Ok(BisectResult {
            minimal_flags: Vec::new(),
            subsystems,
            trials: trials.load(Ordering::Relaxed),
            wall_ms: start.elapsed().as_millis() as u64,
            baseline_already_correct: false,
            outside_flag_set: true,
            ay_binary: binary_identity.path.clone(),
            ay_build_summary: binary_identity.summary.clone(),
            resource_plan: resource_plan.cloned(),
        });
    }

    // Step 3: binary-search minimise.
    let min = search::minimize(runner, FLAGS, cfg.expected, &trials)?;
    let minimal_flags: Vec<String> = min.iter().map(|s| (*s).to_string()).collect();
    let subsystems = subsystems_for(&minimal_flags);

    Ok(BisectResult {
        minimal_flags,
        subsystems,
        trials: trials.load(Ordering::Relaxed),
        wall_ms: start.elapsed().as_millis() as u64,
        baseline_already_correct: false,
        outside_flag_set: false,
        ay_binary: binary_identity.path.clone(),
        ay_build_summary: binary_identity.summary.clone(),
        resource_plan: resource_plan.cloned(),
    })
}

#[cfg(test)]
mod tests;
