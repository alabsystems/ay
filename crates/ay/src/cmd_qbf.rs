// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF Gallery command surface.

use std::fs;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use ay_qbf::{is_qcir, parse_qcir, parse_qdimacs, QbfResult, QbfSolver};
use clap::Subcommand;

/// QBF solving commands.
#[derive(Subcommand)]
pub(crate) enum QbfCommand {
    /// Solve a QDIMACS or prenex QCIR (`#QCIR-G14`) instance with QBF
    /// Gallery exit codes.
    Solve(QbfSolveArgs),
}

/// Arguments for `ay qbf solve`.
#[derive(clap::Args)]
pub(crate) struct QbfSolveArgs {
    /// Input file: QDIMACS, or prenex QCIR when it starts with `#QCIR`.
    pub file: PathBuf,
    /// Wall-clock limit in seconds, counted from the start of the command
    /// (reading and parsing included). It is checked after reading, after
    /// parsing, after building the solver state, every few thousand clauses
    /// while the engine is set up, and during the search; once it has passed,
    /// ay prints `s UNKNOWN` (exit 0). Reading and parsing themselves are not
    /// interrupted, and the SAT back end reads the clock every few hundred
    /// conflicts, so a very large input can overrun it somewhat. Without it the search runs until it
    /// decides the formula or the process is stopped, as under the QBF
    /// Gallery's own time limit.
    #[arg(long, value_name = "SECONDS", value_parser = parse_timeout)]
    pub timeout: Option<Duration>,
}

fn parse_timeout(text: &str) -> Result<Duration, String> {
    let seconds: f64 = text
        .parse()
        .map_err(|_| format!("'{text}' is not a number of seconds"))?;
    Duration::try_from_secs_f64(seconds)
        .ok()
        .filter(|d| !d.is_zero())
        .ok_or_else(|| format!("timeout must be a positive number of seconds, got '{text}'"))
}

/// Run a QBF command and return the competition exit code.
pub(crate) fn run(cmd: &QbfCommand) -> Result<i32> {
    match cmd {
        QbfCommand::Solve(args) => solve(args),
    }
}

fn unknown() -> Result<i32> {
    println!("s UNKNOWN");
    Ok(0)
}

fn solve(args: &QbfSolveArgs) -> Result<i32> {
    let start = Instant::now();
    // A limit too large to add to the clock is no limit.
    let deadline = args.timeout.and_then(|limit| start.checked_add(limit));
    let expired = || deadline.is_some_and(|d| Instant::now() >= d);
    let input = fs::read_to_string(&args.file)
        .with_context(|| format!("failed to read '{}'", args.file.display()))?;
    if expired() {
        return unknown();
    }
    let formula = if is_qcir(&input) {
        parse_qcir(&input)
            .with_context(|| format!("failed to parse QCIR '{}'", args.file.display()))?
    } else {
        parse_qdimacs(&input)
            .with_context(|| format!("failed to parse '{}'", args.file.display()))?
    };
    if expired() {
        return unknown();
    }
    let mut solver = QbfSolver::new(formula);
    if expired() {
        return unknown();
    }

    match solver.solve_until(deadline) {
        QbfResult::Sat(_) => {
            println!("s TRUE");
            Ok(10)
        }
        QbfResult::Unsat(_) => {
            println!("s FALSE");
            Ok(20)
        }
        QbfResult::Unknown => unknown(),
    }
}
