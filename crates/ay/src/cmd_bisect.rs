// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay bisect` subcommand.
//!
//! Runs [`ay_bisect::bisect`] against a failing SMT-LIB2 file and prints the
//! minimal set of `--no-*` flags that make `ay` produce the expected verdict.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result};
use ay_bisect::{bisect, BisectConfig, Expected};
use clap::{Args, ValueEnum};

/// Detailed SAT/expected-UNSAT conflict guidance for internal builds.
pub(crate) const DIAGNOSE_SAT_EXPECTATION_CONFLICT_SUMMARY: &str =
    "AY returned SAT while the declared expectation is UNSAT. This is an \
    evidence conflict; validate both the model and the expectation before \
    assigning blame. Possible AY-side causes include (a) a theory solver \
    returned sat with an invalid model \
    (check `--debug lia` / `--debug lra` for the theory involved); (b) a \
    preprocessing rule dropped a constraint (try `ay bisect --expected \
    unsat` to localize which --no-* flag changes AY's verdict); \
    (c) the model assignment is correct but `(get-model)` rendering is \
    stale. Run `cargo build && ay <file>` — the debug build's verification \
    pipeline re-checks conflicts and may panic with the exact site.";

/// Detailed UNSAT/expected-SAT conflict guidance for internal builds.
pub(crate) const DIAGNOSE_UNSAT_EXPECTATION_CONFLICT_SUMMARY: &str =
    "AY returned UNSAT while the declared expectation is SAT. This is an \
    evidence conflict; verify both sides before assigning blame. Run \
    `ay solve --proof out.drat <file>` \
    then `ay check drat <file> out.drat` to see whether the DRAT proof \
    fails — a rejected step is evidence against AY's result. \
    `ay bisect --expected sat <file>` will localize which preprocessing \
    or theory feature produces the spurious UNSAT. For CHC/SMT: enable \
    `--debug verify` to see the per-conflict re-verification log.";

/// Print the internal bisection-first follow-up used by `ay diagnose`.
pub(crate) fn print_diagnose_next_steps(file: &Path, expected: &str) {
    let f = file.display();
    println!("  1. Bisect CLI feature flags:");
    println!("       ay bisect --expected {expected} {f}");
    println!("  2. Inspect proof (UNSAT only):");
    println!("       ay solve --proof /tmp/p.drat {f}");
    println!("       ay check drat {f} /tmp/p.drat");
    println!("  3. Enable theory tracing:");
    println!("       ay solve --debug theory,verify {f} 2>&1 | less");
    println!("  4. Run debug build for full verification asserts:");
    println!("       cargo build && ./target/debug/ay {f}");
}

#[derive(Args, Debug)]
pub(crate) struct BisectCommand {
    /// Path to the failing SMT-LIB2 file.
    pub file: PathBuf,

    /// Expected verdict on this benchmark.
    #[arg(long, value_enum)]
    pub expected: ExpectedArg,

    /// Per-trial timeout in seconds.
    #[arg(long, default_value_t = 30)]
    pub timeout: u64,

    /// Parallel trial count (passed to rayon).
    #[arg(long, default_value_t = 4)]
    pub jobs: usize,

    /// Explicit ay binary path. Defaults to the currently-executing ay
    /// binary resolved via `std::env::current_exe`.
    #[arg(long, value_name = "PATH")]
    pub ay_binary: Option<PathBuf>,

    /// Emit machine-readable JSON on stdout instead of the text report.
    #[arg(long)]
    pub json: bool,

    /// Verbose per-trial logging on stderr.
    #[arg(long)]
    pub verbose: bool,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
pub(crate) enum ExpectedArg {
    Sat,
    Unsat,
}

impl From<ExpectedArg> for Expected {
    fn from(a: ExpectedArg) -> Self {
        match a {
            ExpectedArg::Sat => Self::Sat,
            ExpectedArg::Unsat => Self::Unsat,
        }
    }
}

pub(crate) fn run(cmd: &BisectCommand) -> Result<i32> {
    let binary = match cmd.ay_binary.clone() {
        Some(p) => p,
        None => std::env::current_exe().context("locating the current ay executable")?,
    };

    let cfg = BisectConfig::new(cmd.file.clone(), cmd.expected.into())
        .with_timeout(Duration::from_secs(cmd.timeout))
        .with_jobs(cmd.jobs)
        .with_verbose(cmd.verbose)
        .with_ay_binary(binary);

    let result = bisect(&cfg).context("running ay-bisect")?;

    if cmd.json {
        let json = serde_json::json!({
            "minimal_flags": result.minimal_flags,
            "subsystems": result.subsystems,
            "trials": result.trials,
            "wall_ms": result.wall_ms,
            "baseline_already_correct": result.baseline_already_correct,
            "outside_flag_set": result.outside_flag_set,
            "resource_plan": result.resource_plan.as_ref().map(|plan| serde_json::json!({
                "requested_jobs": plan.requested_jobs,
                "jobs": plan.jobs,
                "memlimit_mb_per_child": plan.memlimit_mb_per_child,
                "nbcore_per_child": plan.nbcore_per_child,
                "headroom_mb": plan.headroom_mb,
                "planner": plan.planner,
                "enforcement": "ay --memory",
            })),
        });
        let stdout = std::io::stdout();
        let mut lock = stdout.lock();
        writeln!(lock, "{}", serde_json::to_string_pretty(&json)?)?;
    } else {
        let stdout = std::io::stdout();
        let mut lock = stdout.lock();
        result.write_report(&mut lock, &cfg)?;
    }

    let code = if result.outside_flag_set { 2 } else { 0 };
    Ok(code)
}
