// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-rim regression gate for the MILP solver.
//!
//! The ordinary MILP node and corpus gates drive the float-first lane. They can
//! therefore stay green while a change under `exact::` moves the reduced to
//! fraction-free switch by hundreds of pivots. This tool drives the
//! `#[cfg(test)]` exact-rim probe directly and byte-compares three
//! load-invariant currencies from `.milp_rim_baseline.toml`:
//!
//! - the representation and pivot at which conversion happened;
//! - phase-one and total algebraic pivot counts; and
//! - the exact rational optimum, never an `f64` approximation.
//!
//! Wall time is recorded to justify the fast/slow tier split, but is not a
//! verdict currency. The gate still requires a quiet host because a deadline
//! hit would turn an optimal pin into a machine-dependent result. Every probe
//! child runs serially under the repository's shared OOM planner and RSS
//! watchdog; the printed envelope is part of the persisted nightly log.
//!
//! Build the probe and tool before measuring so compilation load cannot trip
//! the quiet-host precondition:
//!
//! ```text
//! cargo test -p ay-milp --release --lib --no-run
//! cargo build -p ay-milp --release --example milp_rim_gate
//! target/release/examples/milp_rim_gate --check --tier fast
//! ```
//!
//! Exit status 0 means exact agreement, 1 means solver drift, and 2 means the
//! harness could not make a trustworthy measurement.

#[path = "milp_rim_gate/baseline.rs"]
mod baseline;
#[path = "milp_rim_gate/cli.rs"]
mod cli;
#[path = "milp_rim_gate/probe.rs"]
mod probe;

use std::path::{Path, PathBuf};
use std::time::Instant;

use baseline::Ratchet;
use cli::{Action, Args};
use thiserror::Error;

type GateResult<T> = Result<T, GateError>;

#[derive(Debug, Error)]
enum GateError {
    #[error("{0}")]
    Setup(String),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Format(#[from] std::fmt::Error),
}

impl GateError {
    fn setup(message: impl Into<String>) -> Self {
        Self::Setup(message.into())
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn baseline_path(repo: &Path) -> PathBuf {
    repo.join(".milp_rim_baseline.toml")
}

fn ensure_corpora(corpora: &[PathBuf]) -> GateResult<()> {
    for corpus in corpora {
        if !corpus.is_dir() {
            return Err(GateError::setup(format!(
                "corpus not found at {}\n       rebuild it: scripts/milp_gate_corpus.py --build",
                corpus.display()
            )));
        }
    }
    Ok(())
}

fn run_check(args: &Args, ratchet: &Ratchet, repo: &Path) -> GateResult<i32> {
    ensure_corpora(&args.corpora)?;
    probe::require_quiet_host(args.busy_policy)?;
    let resources = probe::plan_resources(repo)?;
    resources.report();
    let probe = probe::resolve(args.probe.as_deref(), repo)?;
    let wanted = ratchet.for_tier(args.tier);
    let started = Instant::now();
    let measured = probe::measure(
        wanted,
        &probe,
        &args.corpora,
        args.limit_secs,
        &resources,
        repo,
    )?;
    if !measured.missing.is_empty() {
        return Err(GateError::setup(format!(
            "{} of {} models not found in {}: {}",
            measured.missing.len(),
            wanted.len(),
            args.corpora
                .iter()
                .map(|path| path.display().to_string())
                .collect::<Vec<_>>()
                .join(", "),
            measured.missing.join(" ")
        )));
    }
    if args.action == Action::Ratchet {
        baseline::write(
            &baseline_path(repo),
            ratchet,
            &measured.rows,
            &wanted
                .iter()
                .map(|row| row.name.as_str())
                .collect::<Vec<_>>(),
        )?;
        println!(
            "ratcheted {} instance(s) in .milp_rim_baseline.toml ({:.1}s of solving)",
            measured.rows.len(),
            started.elapsed().as_secs_f64()
        );
        return Ok(0);
    }
    let failures = baseline::compare(wanted, &measured.rows);
    baseline::report(args.tier, wanted, &failures, started.elapsed());
    Ok(if failures.is_empty() { 0 } else { 1 })
}

fn execute() -> GateResult<i32> {
    let args = cli::parse()?;
    if args.action == Action::Help {
        cli::print_help();
        return Ok(0);
    }
    let repo = repo_root();
    let ratchet = baseline::load(&baseline_path(&repo))?;
    if args.action == Action::List {
        baseline::list(&ratchet);
        println!("\n(nothing measured: pass --check or --ratchet)");
        return Ok(0);
    }
    run_check(&args, &ratchet, &repo)
}

fn main() {
    let status = match execute() {
        Ok(status) => status,
        Err(error) => {
            eprintln!("SETUP: {error}");
            2
        }
    };
    std::process::exit(status);
}
