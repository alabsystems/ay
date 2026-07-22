// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ay-bisect standalone CLI.
//!
//! Most users should invoke this via `ay bisect ...`; this binary is
//! preserved for out-of-tree users (e.g. CI scripts) that want to run
//! bisect without building the full `ay` binary.

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::{Parser, ValueEnum};

use crate::{bisect, BisectConfig, Expected};

#[derive(Parser, Debug)]
#[command(
    name = "ay-bisect",
    about = "Bisect ay feature-disable CLI flags to localize soundness bugs",
    version
)]
struct Args {
    /// Path to the failing SMT-LIB2 file.
    smt2_file: PathBuf,

    /// Expected verdict.
    #[arg(long, value_enum)]
    expected: ExpectedArg,

    /// Per-trial timeout in seconds.
    #[arg(long, default_value_t = 30)]
    timeout: u64,

    /// Parallel trials.
    #[arg(long, default_value_t = 4)]
    jobs: usize,

    /// Explicit path to the ay binary (default: auto-locate).
    #[arg(long)]
    ay_binary: Option<PathBuf>,

    /// Emit machine-readable JSON instead of text.
    #[arg(long)]
    json: bool,

    /// Verbose trial tracing to stderr.
    #[arg(long)]
    verbose: bool,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum ExpectedArg {
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

pub fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(e) => {
            eprintln!("ay-bisect: {e:#}");
            ExitCode::from(1)
        }
    }
}

fn run() -> Result<ExitCode> {
    let args = Args::parse();

    let mut cfg = BisectConfig::new(args.smt2_file.clone(), args.expected.into())
        .with_timeout(Duration::from_secs(args.timeout))
        .with_jobs(args.jobs)
        .with_verbose(args.verbose);
    if let Some(p) = args.ay_binary {
        cfg = cfg.with_ay_binary(p);
    }

    let result = bisect(&cfg).context("bisect")?;

    if args.json {
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
        println!("{}", serde_json::to_string_pretty(&json)?);
    } else {
        let mut out = std::io::stdout().lock();
        result.write_report(&mut out, &cfg)?;
    }

    let code = if result.outside_flag_set { 2 } else { 0 };
    Ok(ExitCode::from(code))
}
