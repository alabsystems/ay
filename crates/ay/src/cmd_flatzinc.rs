// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay flatzinc` subcommand — FlatZinc / MiniZinc integration.
//!
//! Translates FlatZinc models to SMT-LIB2 and solves them using ay's
//! SMT or CP backends. Replaces the standalone fzn2smt binary.

use std::io::{self, Write};
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Subcommand;

/// FlatZinc subcommands for MiniZinc integration.
#[derive(Subcommand)]
pub(crate) enum FlatzincCommand {
    /// Translate FlatZinc to SMT-LIB2.
    Translate {
        /// FlatZinc input file
        file: PathBuf,
    },

    /// Solve a FlatZinc model (auto-selects CP or SMT backend).
    ///
    /// Prefers the CP backend when all constraints are supported.
    /// Falls back to SMT translation when CP reports unsupported constraints.
    Solve {
        /// FlatZinc input file
        file: PathBuf,

        /// Per check-sat timeout in milliseconds
        #[arg(short = 't', long, value_name = "MS")]
        timeout: Option<u64>,

        /// Force FD-track branching search
        #[arg(long)]
        fd_search: bool,

        /// Enumerate all solutions (satisfaction problems)
        #[arg(short = 'a', long)]
        all_solutions: bool,

        /// Ignore search annotations (disable auto-FD)
        #[arg(short = 'f', long)]
        free_search: bool,

        /// Parallel workers (CP satisfaction only)
        #[arg(short = 'p', value_name = "N")]
        parallel: Option<usize>,
    },

    /// Solve with CP engine directly.
    SolveCp {
        /// FlatZinc input file
        file: PathBuf,

        /// Per check-sat timeout in milliseconds
        #[arg(short = 't', long, value_name = "MS")]
        timeout: Option<u64>,

        /// Enumerate all solutions
        #[arg(short = 'a', long)]
        all_solutions: bool,

        /// Parallel workers
        #[arg(short = 'p', value_name = "N")]
        parallel: Option<usize>,
    },

    /// Print FlatZinc model statistics.
    Info {
        /// FlatZinc input file
        file: PathBuf,
    },
}

/// Run a FlatZinc subcommand.
pub(crate) fn run(cmd: &FlatzincCommand) -> Result<()> {
    match cmd {
        FlatzincCommand::Translate { file } => {
            let (_, result) = parse_and_translate(file)?;
            cmd_translate(&result)
        }
        FlatzincCommand::Info { file } => {
            let (model, result) = parse_and_translate(file)?;
            cmd_info(&model, &result)
        }
        FlatzincCommand::SolveCp {
            file,
            timeout,
            all_solutions,
            parallel,
        } => {
            let model = parse_model(file)?;
            ay_fzn2smt::solve_cp::cmd_solve_cp(
                &model,
                *timeout,
                *all_solutions,
                parallel.unwrap_or(1),
                None,
            )?;
            Ok(())
        }
        FlatzincCommand::Solve {
            file,
            timeout,
            fd_search,
            all_solutions,
            free_search,
            parallel,
        } => cmd_solve_portfolio(
            file,
            *timeout,
            *fd_search,
            *all_solutions,
            *free_search,
            parallel.unwrap_or(1),
        ),
    }
}

/// Portfolio solve: prefer CP backend, fall back to SMT.
///
/// Mirrors the logic from the original fzn2smt binary's main().
fn cmd_solve_portfolio(
    file: &PathBuf,
    timeout_ms: Option<u64>,
    mut fd_search: bool,
    all_solutions: bool,
    free_search: bool,
    parallel_workers: usize,
) -> Result<()> {
    let model = parse_model(file)?;

    // Probe the CP backend for unsupported constraints.
    let cp_unsupported = match ay_fzn2smt::solve_cp::unsupported_constraints(&model) {
        Ok(unsupported) => Some(unsupported),
        Err(err) => {
            eprintln!("warning: CP backend probe failed, falling back to SMT: {err}");
            None
        }
    };

    let use_cp = cp_unsupported.as_ref().is_some_and(Vec::is_empty);
    if use_cp {
        ay_fzn2smt::solve_cp::cmd_solve_cp(
            &model,
            timeout_ms,
            all_solutions,
            parallel_workers,
            cp_unsupported.as_deref(),
        )?;
        return Ok(());
    }

    // Fall back to SMT solve path.
    let result = ay_flatzinc_smt::translate(&model)
        .map_err(|e| anyhow::anyhow!("translation error: {e}"))?;

    // Auto-activate branching search when the model has search annotations
    // and the user didn't explicitly request free search with -f.
    if !free_search && !fd_search && !result.search_annotations.is_empty() {
        fd_search = true;
    }

    ay_fzn2smt::solve::cmd_solve(&result, timeout_ms, fd_search, all_solutions)?;
    Ok(())
}

/// Parse a FlatZinc file into an AST model.
fn parse_model(file: &PathBuf) -> Result<ay_flatzinc_parser::ast::FznModel> {
    let path = file.to_string_lossy();
    let input = std::fs::read_to_string(file).with_context(|| format!("failed to read {path}"))?;
    ay_flatzinc_parser::parse_flatzinc(&input).map_err(|e| anyhow::anyhow!("parse error: {e}"))
}

/// Parse a FlatZinc file and translate to SMT-LIB2.
fn parse_and_translate(
    file: &PathBuf,
) -> Result<(
    ay_flatzinc_parser::ast::FznModel,
    ay_flatzinc_smt::TranslationResult,
)> {
    let model = parse_model(file)?;
    let result = ay_flatzinc_smt::translate(&model)
        .map_err(|e| anyhow::anyhow!("translation error: {e}"))?;
    Ok((model, result))
}

/// Print the SMT-LIB2 translation to stdout.
fn cmd_translate(result: &ay_flatzinc_smt::TranslationResult) -> Result<()> {
    print!("{}", result.smtlib);
    io::stdout().flush()?;
    Ok(())
}

/// Print model statistics: variable count, constraint count, objective type.
fn cmd_info(
    model: &ay_flatzinc_parser::ast::FznModel,
    result: &ay_flatzinc_smt::TranslationResult,
) -> Result<()> {
    println!("=== FlatZinc Model Info ===");
    println!("Parameters:  {}", model.parameters.len());
    println!("Variables:   {}", model.variables.len());
    println!("Constraints: {}", model.constraints.len());
    println!("Output vars: {}", result.output_vars.len());
    match &result.objective {
        Some(obj) => {
            let dir = if obj.minimize { "minimize" } else { "maximize" };
            println!("Objective:   {dir} {}", obj.smt_expr);
        }
        None => println!("Objective:   satisfy"),
    }
    println!(
        "SMT-LIB2:   {} bytes, {} lines",
        result.smtlib.len(),
        result.smtlib.lines().count()
    );
    if result.search_annotations.is_empty() {
        println!("Search:      none (Free Search mode)");
    } else {
        println!(
            "Search:      {} annotation(s) (FD Search capable)",
            result.search_annotations.len()
        );
    }
    println!("Var domains: {} tracked", result.var_domains.len());
    Ok(())
}
