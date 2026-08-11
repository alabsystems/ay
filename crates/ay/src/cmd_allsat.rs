// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay allsat` subcommand — enumerate all satisfying assignments.
//!
//! Thin CLI wrapper over the `ay-allsat` crate's [`AllSatSolver`]. Accepts a
//! DIMACS CNF file, enumerates all models (optionally projected onto a subset
//! of variables), and prints each model in SMT-LIB-compatible format:
//!
//! ```text
//! (model
//!   (define-fun x1 () Bool true)
//!   (define-fun x2 () Bool false)
//! )
//!
//! (model
//!   (define-fun x1 () Bool false)
//!   (define-fun x2 () Bool true)
//! )
//!
//! ; 2 model(s) enumerated (exhaustive)
//! ```
//!
//! The trailing comment reports the total model count and whether enumeration
//! was `exhaustive` (all models found) or `capped` (hit `--max-models` limit).
//!
//! ## Scope
//!
//! DIMACS CNF input only. SMT-LIB input would require bit-blasting into the
//! Boolean skeleton that `ay-allsat` works on; that is out of scope for the
//! Tier-2 polish deliverable described in #8777.

use std::fs;
use std::path::PathBuf;

use anyhow::{bail, Context, Result};
use ay_allsat::{AllSatConfig, AllSatOutcome, AllSatSolver, Solution};
use ay_sat::parse_dimacs;
use clap::Args;

/// Arguments for `ay allsat FILE`.
#[derive(Args, Clone)]
pub(crate) struct AllSatArgs {
    /// Input file in DIMACS CNF format.
    #[arg(value_name = "FILE")]
    pub(crate) file: PathBuf,

    /// Maximum number of models to enumerate (0 = unlimited).
    ///
    /// When the cap is reached the final comment reports `capped`; otherwise
    /// `exhaustive`.
    #[arg(long, value_name = "N", default_value_t = 0)]
    pub(crate) max_models: usize,

    /// Comma-separated list of 1-indexed variables to project onto.
    ///
    /// When set, blocking clauses reference only these variables, so the
    /// enumerated models are distinct assignments to the projected subset.
    /// Non-projected variables still appear in each printed model with the
    /// value chosen by the underlying SAT solver, but duplicate projected
    /// cubes are never returned.
    ///
    /// Example: `--projected-vars 1,3,5` enumerates all distinct assignments
    /// to x1, x3, x5 that extend to a satisfying assignment of the formula.
    #[arg(long, value_name = "V1,V2,...", value_delimiter = ',')]
    pub(crate) projected_vars: Vec<u32>,
}

/// Entry point dispatched from `main.rs`.
pub(crate) fn run(args: &AllSatArgs) -> Result<()> {
    let content = fs::read_to_string(&args.file)
        .with_context(|| format!("failed to read {}", args.file.display()))?;

    let formula = parse_dimacs(&content).map_err(|e| anyhow::anyhow!("DIMACS parse error: {e}"))?;

    // Validate projected variable indices before building the solver.
    if !args.projected_vars.is_empty() {
        for &v in &args.projected_vars {
            if v == 0 {
                bail!("invalid --projected-vars entry 0: DIMACS variables are 1-indexed");
            }
            if (v as usize) > formula.num_vars {
                bail!(
                    "--projected-vars entry {v} exceeds formula variable count {}",
                    formula.num_vars
                );
            }
        }
    }

    // ay-allsat's Internal backend uses 1-indexed variables matching DIMACS,
    // so we can pass the projected variables through unchanged.
    let mut solver = AllSatSolver::new();
    solver
        .try_ensure_num_vars(formula.num_vars)
        .context("DIMACS variable count is unsupported by AllSAT")?;
    for clause in formula.clauses {
        // AllSatSolver::add_clause takes a SignedClause (Vec<i32>), so we map
        // each Literal through its DIMACS representation.
        let signed: Vec<i32> = clause.iter().map(|lit| lit.to_dimacs()).collect();
        solver
            .try_add_clause(signed)
            .context("DIMACS clause is unsupported by AllSAT")?;
    }

    let max_solutions = if args.max_models == 0 {
        None
    } else {
        Some(args.max_models)
    };
    let projection = if args.projected_vars.is_empty() {
        None
    } else {
        Some(args.projected_vars.clone())
    };
    let config = AllSatConfig {
        max_solutions,
        projection: projection.clone(),
    };

    // Variables to print in each model:
    //  - projected: just the projected vars (the solver only distinguishes
    //    models by these, so reporting non-projected vars is misleading).
    //  - unprojected: all formula variables 1..=num_vars.
    let print_vars: Vec<u32> = if let Some(proj) = &projection {
        proj.clone()
    } else {
        (1..=formula.num_vars as u32).collect()
    };

    let mut count: u64 = 0;
    let iter = solver.iter_with_config(config);
    let mut first = true;
    for solution in iter {
        if !first {
            println!();
        }
        first = false;
        print_solution(&solution, &print_vars)?;
        count = count
            .checked_add(1)
            .context("model count exceeds u64::MAX")?;
    }
    // After full consumption of the iterator, stats.outcome reflects whether
    // enumeration terminated naturally (Exhaustive) or hit the cap (Capped).
    let outcome_str = match solver.stats().outcome {
        AllSatOutcome::Exhaustive => "exhaustive",
        AllSatOutcome::Capped => "capped",
        AllSatOutcome::SolverUnknown => "solver-unknown",
        AllSatOutcome::InvalidInput => "invalid-input",
        AllSatOutcome::CallbackStopped => "callback-stopped",
        AllSatOutcome::IteratorDropped => "iterator-dropped",
        AllSatOutcome::CountOverflow => "count-overflow",
        AllSatOutcome::InProgress => "in-progress",
        // AllSatOutcome is non-exhaustive. A future termination reason must
        // never be mislabeled as an exhaustive enumeration.
        _ => "incomplete",
    };
    if !first {
        println!();
    }
    println!("; {count} model(s) enumerated ({outcome_str})");

    Ok(())
}

/// Print a single solution as an SMT-LIB `(model ...)` block.
///
/// Variables are rendered as `x<N>` where `<N>` is the 1-indexed DIMACS
/// variable number. Each variable is declared as a `Bool` with `true`/`false`.
fn print_solution(solution: &Solution, vars: &[u32]) -> Result<()> {
    let values = vars
        .iter()
        .map(|&variable| {
            solution
                .is_true(variable)
                .map(|value| (variable, value))
                .with_context(|| format!("solver model omitted variable x{variable}"))
        })
        .collect::<Result<Vec<_>>>()?;

    println!("(model");
    for (variable, value) in values {
        println!("  (define-fun x{variable} () Bool {value})");
    }
    println!(")");
    Ok(())
}
