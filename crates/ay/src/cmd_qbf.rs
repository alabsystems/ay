// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF Gallery command surface.

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use ay_qbf::{parse_qdimacs, QbfResult, QbfSolver};
use clap::Subcommand;

/// QBF solving commands.
#[derive(Subcommand)]
pub(crate) enum QbfCommand {
    /// Solve a QDIMACS instance with QBF Gallery exit codes.
    Solve(QbfSolveArgs),
}

/// Arguments for `ay qbf solve`.
#[derive(clap::Args)]
pub(crate) struct QbfSolveArgs {
    /// QDIMACS input file.
    pub file: PathBuf,
}

/// Run a QBF command and return the competition exit code.
pub(crate) fn run(cmd: &QbfCommand) -> Result<i32> {
    match cmd {
        QbfCommand::Solve(args) => solve(args),
    }
}

fn solve(args: &QbfSolveArgs) -> Result<i32> {
    let input = fs::read_to_string(&args.file)
        .with_context(|| format!("failed to read '{}'", args.file.display()))?;
    let formula = parse_qdimacs(&input)
        .with_context(|| format!("failed to parse '{}'", args.file.display()))?;
    let mut solver = QbfSolver::new(formula);

    match solver.solve() {
        QbfResult::Sat(_) => {
            println!("s TRUE");
            Ok(10)
        }
        QbfResult::Unsat(_) => {
            println!("s FALSE");
            Ok(20)
        }
        QbfResult::Unknown => {
            println!("s UNKNOWN");
            Ok(0)
        }
    }
}
