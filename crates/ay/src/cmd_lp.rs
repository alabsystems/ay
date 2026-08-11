// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay lp solve FILE` subcommand.
//!
//! Parses an MPS or CPLEX LP file and runs the Phase 1 MIP/LP solver. The
//! format is inferred from the file extension and falls back to content
//! sniffing via [`ay_lp::detect_format`].

use std::fs;
use std::io::Read as _;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use ay_lp::{detect_format, parse_lp, parse_mps, solve, InputFormat, Problem, Sense, Solution};
use clap::Subcommand;

/// LP/MIP solver subcommands.
#[derive(Subcommand)]
pub(crate) enum LpCommand {
    /// Solve an MPS or CPLEX LP instance.
    Solve {
        /// Input file in MPS (`.mps`) or CPLEX LP (`.lp`) format.
        file: PathBuf,

        /// Force format detection (`mps` or `lp`). Auto-detected by default.
        #[arg(long, value_name = "FORMAT")]
        format: Option<String>,
    },
}

/// Exit code convention borrowed from MIPLIB conventions:
///
/// - `0`: optimal solution printed
/// - `10`: infeasible
/// - `11`: unbounded
/// - `1`: any other error
pub(crate) fn run(cmd: &LpCommand) -> Result<i32> {
    match cmd {
        LpCommand::Solve { file, format } => run_solve(file, format.as_deref()),
    }
}

/// Solve Z3's `-lp` mode and emit its compact optimization transcript.
pub(crate) fn run_z3_compat(
    path: Option<&Path>,
    use_stdin: bool,
    display_model: bool,
    display_stats: bool,
) -> Result<i32> {
    let input = if use_stdin {
        let mut input = String::new();
        std::io::stdin()
            .lock()
            .read_to_string(&mut input)
            .context("reading LP stdin")?;
        input
    } else {
        let path = path.context("input file was not specified")?;
        fs::read_to_string(path).with_context(|| format!("failed to read '{}'", path.display()))?
    };
    let problem = parse_lp(&input).context("parsing CPLEX LP input")?;
    match solve(&problem) {
        Ok(solution) => {
            println!("sat");
            if display_stats {
                println!("time:                0.00 secs");
            }
            if display_model {
                emit_z3_model(&problem, &solution);
            }
            println!("   {}", z3_number(solution.objective, false));
        }
        Err(ay_lp::LpError::Infeasible) => println!("unsat"),
        Err(ay_lp::LpError::Unbounded) => println!("unknown"),
        Err(error) => return Err(error.into()),
    }
    Ok(0)
}

fn emit_z3_model(problem: &Problem, solution: &Solution) {
    for (variable, value) in problem.variables.iter().zip(&solution.values) {
        let is_integer = variable.is_integral();
        let sort = if is_integer { "Int" } else { "Real" };
        println!("(define-fun {} () {sort}", variable.name);
        println!("  {})", z3_number(*value, !is_integer));
    }
}

fn z3_number(value: f64, force_real: bool) -> String {
    if value == 0.0 {
        return if force_real { "0.0" } else { "0" }.to_string();
    }
    if value.is_finite() && value.fract().abs() <= 1e-9 {
        let integer = format!("{value:.0}");
        return if force_real {
            format!("{integer}.0")
        } else {
            integer
        };
    }
    format!("{value:.15}")
        .trim_end_matches('0')
        .trim_end_matches('.')
        .to_string()
}

fn run_solve(file: &Path, forced_format: Option<&str>) -> Result<i32> {
    let input =
        fs::read_to_string(file).with_context(|| format!("failed to read '{}'", file.display()))?;

    let format = resolve_format(file, &input, forced_format)?;

    let problem = match format {
        InputFormat::Mps => parse_mps(&input)
            .with_context(|| format!("failed to parse MPS '{}'", file.display()))?,
        InputFormat::Lp => {
            parse_lp(&input).with_context(|| format!("failed to parse LP '{}'", file.display()))?
        }
        _ => anyhow::bail!("unsupported input format detected"),
    };

    emit_canonical(&problem);

    match solve(&problem) {
        Ok(sol) => {
            emit_solution(&problem, &sol);
            Ok(0)
        }
        Err(ay_lp::LpError::Infeasible) => {
            println!("s INFEASIBLE");
            Ok(10)
        }
        Err(ay_lp::LpError::Unbounded) => {
            println!("s UNBOUNDED");
            Ok(11)
        }
        Err(e) => {
            eprintln!("error: {e}");
            Ok(1)
        }
    }
}

fn resolve_format(file: &Path, input: &str, forced: Option<&str>) -> Result<InputFormat> {
    if let Some(f) = forced {
        return match f.to_ascii_lowercase().as_str() {
            "mps" => Ok(InputFormat::Mps),
            "lp" => Ok(InputFormat::Lp),
            other => Err(anyhow::anyhow!("unknown --format '{other}'")),
        };
    }
    if let Some(ext) = file.extension().and_then(|e| e.to_str()) {
        if ext.eq_ignore_ascii_case("mps") {
            return Ok(InputFormat::Mps);
        }
        if ext.eq_ignore_ascii_case("lp") {
            return Ok(InputFormat::Lp);
        }
    }
    Ok(detect_format(input))
}

fn emit_canonical(problem: &Problem) {
    let sense = match problem.sense {
        Sense::Min => "minimize",
        Sense::Max => "maximize",
    };
    println!("c format: parsed");
    println!("c sense: {sense}");
    println!("c variables: {}", problem.variables.len());
    println!("c constraints: {}", problem.constraints.len());
    if problem.has_integer_vars() {
        let n = problem.variables.iter().filter(|v| v.is_integral()).count();
        println!("c integer-variables: {n}");
    }
}

fn emit_solution(problem: &Problem, sol: &Solution) {
    println!("s OPTIMAL");
    println!("o {}", sol.objective);
    for (var, &val) in problem.variables.iter().zip(sol.values.iter()) {
        println!("v {} = {}", var.name, val);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_run_solve_mps_simple() {
        let mut f = NamedTempFile::new().expect("tmp");
        writeln!(
            f,
            "NAME TRIV
ROWS
 N OBJ
 G C1
COLUMNS
 X OBJ 1.0 C1 1.0
 Y OBJ 1.0 C1 1.0
RHS
 RHS C1 2.0
BOUNDS
ENDATA"
        )
        .unwrap();
        let code = run_solve(f.path(), Some("mps")).expect("run");
        assert_eq!(code, 0);
    }

    #[test]
    fn test_run_solve_detects_lp_via_extension() {
        let mut f = tempfile::Builder::new()
            .suffix(".lp")
            .tempfile()
            .expect("tmp");
        writeln!(
            f,
            "Minimize
 x + y
Subject To
 c1: x + y >= 4
Bounds
 x >= 0
 y >= 0
End"
        )
        .unwrap();
        let code = run_solve(f.path(), None).expect("run");
        assert_eq!(code, 0);
    }
}
