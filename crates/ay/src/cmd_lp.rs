// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay lp solve FILE` subcommand.
//!
//! MPS input uses the sparse MILP engine. CPLEX LP uses the dense simplex.

use std::fs;
use std::io::{Read as _, Write};
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result};
use ay_lp::{
    detect_format, parse_lp, parse_mps_exact, solve, solve_with_incumbents, InputFormat, Problem,
    Sense, Solution,
};
use clap::Subcommand;

mod sparse;

#[cfg(test)]
mod differential_tests;

/// LP/MIP solver subcommands.
#[derive(Subcommand)]
pub(crate) enum LpCommand {
    /// Solve an MPS or CPLEX LP instance.
    Solve {
        /// Input file in MPS (`.mps`) or CPLEX LP (`.lp`) format.
        file: PathBuf,

        /// Override the detected input format (`mps` or `lp`).
        #[arg(long, value_name = "FORMAT")]
        format: Option<String>,

        /// Wall-clock limit in seconds for the MPS (sparse) route. Without it
        /// the search runs until a proof or a signal; improving solutions are
        /// written as they are found either way.
        #[arg(long, value_name = "SECONDS")]
        time_limit: Option<f64>,
    },
}

/// Exit code convention borrowed from MIPLIB conventions:
///
/// - `0`: optimal solution printed, or a stop without a proof (`s FEASIBLE`
///   with the last `o`/`v` block as the answer, or `s UNKNOWN`)
/// - `10`: infeasible
/// - `11`: unbounded
/// - `1`: any other error
pub(crate) fn run(cmd: &LpCommand) -> Result<i32> {
    match cmd {
        LpCommand::Solve {
            file,
            format,
            time_limit,
        } => {
            let limit = match time_limit {
                None => None,
                Some(secs) => Some(
                    Duration::try_from_secs_f64(*secs)
                        .map_err(|_| anyhow::anyhow!("--time-limit {secs}: not a duration"))?,
                ),
            };
            // A SIGTERM during an incumbent block ends the run after the
            // block is whole (`write_block`).
            #[cfg(unix)]
            ay_sys::sigterm_defer::install();
            run_solve(file, format.as_deref(), limit, &mut std::io::stdout())
        }
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

/// Solves `file`. MPS input is read exactly and goes to AY's sparse MILP
/// engine ([`sparse::solve_sparse`]); CPLEX LP input goes to the dense
/// tableau solver, which refuses a model too large for it.
fn run_solve(
    file: &Path,
    forced_format: Option<&str>,
    time_limit: Option<Duration>,
    out: &mut dyn Write,
) -> Result<i32> {
    let input =
        fs::read_to_string(file).with_context(|| format!("failed to read '{}'", file.display()))?;

    let format = resolve_format(file, &input, forced_format)?;

    if format == InputFormat::Mps {
        // The one reading every route, check and printed number uses.
        let exact = parse_mps_exact(&input)
            .with_context(|| format!("failed to parse MPS '{}'", file.display()))?;
        let integers = exact.columns.iter().filter(|c| c.is_integral()).count();
        write_block(
            out,
            &canonical_lines(exact.sense, exact.columns.len(), exact.rows.len(), integers),
        )
        .context("writing to stdout")?;
        let (end, written) = sparse::solve_sparse(&exact, time_limit, out)?;
        return sparse_status(end, written, out);
    }
    let problem = match format {
        InputFormat::Lp => {
            parse_lp(&input).with_context(|| format!("failed to parse LP '{}'", file.display()))?
        }
        _ => anyhow::bail!("unsupported input format detected"),
    };
    let integers = problem.variables.iter().filter(|v| v.is_integral()).count();
    write_block(
        out,
        &canonical_lines(
            problem.sense,
            problem.variables.len(),
            problem.constraints.len(),
            integers,
        ),
    )
    .context("writing to stdout")?;
    let (result, incumbents) = solve_reporting_incumbents(&problem, out)?;
    final_status(&problem, &result, incumbents, out)
}

/// Runs the solver, writing each improving incumbent to `out` as one
/// complete `o`/`v` block as soon as it is found, so that a run stopped by
/// a signal or a limit leaves its best checked solution behind. Returns the
/// solver's result and the number of incumbent blocks written.
fn solve_reporting_incumbents(
    problem: &Problem,
    out: &mut dyn Write,
) -> Result<(Result<Solution, ay_lp::LpError>, usize)> {
    let mut written = 0usize;
    let mut write_error: Option<std::io::Error> = None;
    let result = solve_with_incumbents(problem, &mut |sol| {
        if write_error.is_none() {
            match write_block(out, &solution_block(problem, sol)) {
                Ok(()) => written += 1,
                Err(e) => write_error = Some(e),
            }
        }
    });
    if let Some(e) = write_error {
        return Err(anyhow::Error::new(e).context("writing an incumbent to stdout"));
    }
    Ok((result, written))
}

/// Prints the final status for `result` and returns the exit code. A proven
/// optimum is printed as `s OPTIMAL` followed by its `o`/`v` block (for a MIP
/// the same point as the last incumbent block).
///
/// A solve that stops without a conclusion (node or iteration limit, a model
/// too large for the dense tableau, a numerical failure) is not an error of
/// the run: it ends `s FEASIBLE` when an incumbent block was written (that
/// block is the answer) and `s UNKNOWN` otherwise, with the reason on a
/// `c stopped:` line, and exits 0.
fn final_status(
    problem: &Problem,
    result: &Result<Solution, ay_lp::LpError>,
    incumbents: usize,
    out: &mut dyn Write,
) -> Result<i32> {
    let (text, code) = match result {
        Ok(sol) => (format!("s OPTIMAL\n{}", solution_block(problem, sol)), 0),
        Err(ay_lp::LpError::Infeasible) => ("s INFEASIBLE\n".to_string(), 10),
        Err(ay_lp::LpError::Unbounded) => ("s UNBOUNDED\n".to_string(), 11),
        Err(e) => {
            let status = if incumbents > 0 {
                "FEASIBLE"
            } else {
                "UNKNOWN"
            };
            (format!("c stopped: {e}\ns {status}\n"), 0)
        }
    };
    write_block(out, &text).context("writing the final status to stdout")?;
    Ok(code)
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

fn canonical_lines(sense: Sense, variables: usize, constraints: usize, integers: usize) -> String {
    use std::fmt::Write as _;
    let sense = match sense {
        Sense::Min => "minimize",
        Sense::Max => "maximize",
    };
    let mut text = String::new();
    let _ = writeln!(text, "c format: parsed");
    let _ = writeln!(text, "c sense: {sense}");
    let _ = writeln!(text, "c variables: {variables}");
    let _ = writeln!(text, "c constraints: {constraints}");
    if integers > 0 {
        let _ = writeln!(text, "c integer-variables: {integers}");
    }
    text
}

/// Prints the final status of a sparse solve and returns the exit code
/// (the codes of [`run`]; a stop without a proof exits 0, see
/// [`final_status`]).
fn sparse_status(end: sparse::SparseEnd, written: usize, out: &mut dyn Write) -> Result<i32> {
    let (line, code) = match end {
        sparse::SparseEnd::Optimal => ("s OPTIMAL\n", 0),
        sparse::SparseEnd::Infeasible => ("s INFEASIBLE\n", 10),
        sparse::SparseEnd::Stopped if written > 0 => ("s FEASIBLE\n", 0),
        sparse::SparseEnd::Stopped => ("s UNKNOWN\n", 0),
    };
    write_block(out, line).context("writing the final status to stdout")?;
    Ok(code)
}

/// One `o <objective>` line, a `v <name> = <value>` line per variable
/// (`{}` prints each `f64` with full round-trip precision), and the block's
/// end line ([`block_end`]).
fn solution_block(problem: &Problem, sol: &Solution) -> String {
    use std::fmt::Write as _;
    let mut text = String::new();
    let _ = writeln!(text, "o {}", sol.objective);
    for (var, &val) in problem.variables.iter().zip(sol.values.iter()) {
        let _ = writeln!(text, "v {} = {}", var.name, val);
    }
    text.push_str(&block_end(problem.variables.len()));
    text
}

/// The line that ends a solution block of `values` `v` lines:
/// `c solution end <values>`. A reader takes a block as an answer only once
/// it has read this line with the count of `v` lines it collected, so a block
/// cut off by a kill that no signal handler sees (SIGKILL, the OOM killer) is
/// never taken for one; the `o` line stays first, where the MIPcc wrapper
/// starts a new answer.
fn block_end(values: usize) -> String {
    format!("c solution end {values}\n")
}

/// Writes `text` with one `write_all` and flushes, so that the block reaches
/// the output file whole before the solver goes on. A SIGTERM that arrives
/// meanwhile ends the run only once the block is flushed
/// (`ay_sys::sigterm_defer`, installed by `ay lp solve`), so a stopped run
/// never leaves a cut-off last block.
fn write_block(out: &mut dyn Write, text: &str) -> std::io::Result<()> {
    #[cfg(unix)]
    let _whole = ay_sys::sigterm_defer::begin_block();
    out.write_all(text.as_bytes())?;
    out.flush()
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
        let code = run_solve(f.path(), Some("mps"), None, &mut Vec::new()).expect("run");
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
        let code = run_solve(f.path(), None, None, &mut Vec::new()).expect("run");
        assert_eq!(code, 0);
    }

    fn knapsack() -> Problem {
        parse_lp(
            "Maximize
 3 x + 4 y
Subject To
 cap: 2 x + 3 y <= 6
Bounds
 0 <= x <= 2
 0 <= y <= 2
General
 x y
End",
        )
        .expect("parse")
    }

    /// Each incumbent is written as one complete `o`/`v` block before the
    /// final status, so a run stopped part-way leaves its last checked point.
    #[test]
    fn test_incumbent_blocks_precede_final_status() {
        let problem = knapsack();
        let mut out: Vec<u8> = Vec::new();
        let (result, incumbents) = solve_reporting_incumbents(&problem, &mut out).expect("solve");
        assert!(incumbents >= 1);
        let code = final_status(&problem, &result, incumbents, &mut out).expect("status");
        assert_eq!(code, 0);
        let text = String::from_utf8(out).expect("utf8");
        let first_o = text.find("o ").expect("o line");
        let status = text.find("s OPTIMAL").expect("status");
        assert!(first_o < status, "{text}");
        assert!(
            text.ends_with("o 8\nv x = 0\nv y = 2\nc solution end 2\n"),
            "{text}"
        );
    }

    /// AY-N6: a solve that stops without a conclusion ends with a status
    /// line and exit 0 instead of an error: `s UNKNOWN` without an incumbent,
    /// `s FEASIBLE` after one (whose block is the answer).
    #[test]
    fn test_stopped_solve_reports_unknown_or_feasible() {
        let problem = knapsack();
        let stopped: Result<Solution, ay_lp::LpError> =
            Err(ay_lp::LpError::ResourceLimit("too big".into()));
        let mut out: Vec<u8> = Vec::new();
        assert_eq!(
            final_status(&problem, &stopped, 0, &mut out).expect("status"),
            0
        );
        assert_eq!(
            String::from_utf8(out).expect("utf8"),
            "c stopped: resource limit: too big\ns UNKNOWN\n"
        );
        let mut out: Vec<u8> = Vec::new();
        assert_eq!(
            final_status(&problem, &stopped, 2, &mut out).expect("status"),
            0
        );
        assert!(String::from_utf8(out)
            .expect("utf8")
            .ends_with("s FEASIBLE\n"));
        let mut out: Vec<u8> = Vec::new();
        let infeasible: Result<Solution, ay_lp::LpError> = Err(ay_lp::LpError::Infeasible);
        assert_eq!(
            final_status(&problem, &infeasible, 0, &mut out).expect("status"),
            10
        );
    }

    /// Review finding (200554215): on these four files the two MPS readers
    /// built different models and the route printed the engine's verdict
    /// (`s OPTIMAL` with `o 0`, `o -1`, `s INFEASIBLE`, `s UNBOUNDED`),
    /// contradicting `ay-lp`'s reading. Readers in common use (and the MIPLIB
    /// checker) disagree on each construct, so `ay-lp` now refuses them and
    /// no verdict is printed.
    #[test]
    fn test_files_readers_disagree_on_get_no_verdict() {
        let cases = [
            (
                "dupobj",
                "NAME DUPOBJ\nROWS\n N OBJ\n L C1\nCOLUMNS\n    M 'MARKER' 'INTORG'\n    X OBJ -3 C1 1\n    X OBJ 2\n    M 'MARKER' 'INTEND'\nRHS\n    RHS C1 10\nBOUNDS\n UP BND X 10\nENDATA\n",
            ),
            (
                "lcmarker",
                "NAME LCMARK\nROWS\n N OBJ\n L C1\nCOLUMNS\n    M 'MARKER' 'intorg'\n    X OBJ -1 C1 2\n    M 'MARKER' 'intend'\n    Y OBJ 0 C1 0\nRHS\n    RHS C1 3\nBOUNDS\n UP BND X 10\nENDATA\n",
            ),
            (
                "lcmarker_eq",
                "NAME LCMARKEQ\nROWS\n N OBJ\n E C1\nCOLUMNS\n    M 'MARKER' 'intorg'\n    X OBJ 1 C1 2\n    M 'MARKER' 'intend'\n    Y OBJ 1 C1 0\nRHS\n    RHS C1 3\nBOUNDS\n UP BND X 10\n UP BND Y 1\nENDATA\n",
            ),
            (
                "negup",
                "NAME NEGUP\nROWS\n N OBJ\n L C1\nCOLUMNS\n    X OBJ 1 C1 1\nRHS\n    RHS C1 10\nBOUNDS\n UP BND X -1\nENDATA\n",
            ),
        ];
        for (name, text) in cases {
            let mut f = tempfile::Builder::new()
                .suffix(".mps")
                .tempfile()
                .expect("tmp");
            f.write_all(text.as_bytes()).expect("write");
            let mut out: Vec<u8> = Vec::new();
            let result = run_solve(f.path(), None, None, &mut out);
            let printed = String::from_utf8(out).expect("utf8");
            assert!(result.is_err(), "{name}: {result:?}\n{printed}");
            assert!(!printed.contains("\ns "), "{name}: {printed}");
        }
    }

    /// Runs `ay lp solve` on `text` as an `.mps` file with a 60 s limit:
    /// (exit code, stdout, or the parse error).
    fn solve_mps(text: &str) -> (Result<i32, String>, String) {
        let mut f = tempfile::Builder::new()
            .suffix(".mps")
            .tempfile()
            .expect("tmp");
        f.write_all(text.as_bytes()).expect("write");
        let mut out: Vec<u8> = Vec::new();
        let code = run_solve(f.path(), None, Some(Duration::from_secs(60)), &mut out)
            .map_err(|e| format!("{e:#}"));
        (code, String::from_utf8(out).expect("utf8"))
    }

    /// The last `o`/`v` block of `text`, `o` line first.
    fn last_block(text: &str) -> String {
        let start = text.rfind("\no ").map_or(0, |i| i + 1);
        let mut block = String::new();
        for line in text[start..]
            .lines()
            .take_while(|l| l.starts_with("o ") || l.starts_with("v "))
        {
            block.push_str(line);
            block.push('\n');
        }
        block
    }

    /// The reviewers' six exactly feasible files (AY-N11: `bound-loss`,
    /// `rhs-loss`, `range-sum-loss`, `coefficient-sum-loss`,
    /// `decimal-exponent-loss`, `cancel-sat`), verbatim. Each needs a number
    /// an `f64` cannot hold; the dense route of ay's main and the branch's
    /// sparse route both answered `s INFEASIBLE`. The organizers' checker
    /// accepts the witness of each with zero violation.
    const SIX: [(&str, &str, &str); 6] = [
        (
            "bound-loss",
            "NAME          EXACT\nROWS\n N  OBJ\n E  MATCH\nCOLUMNS\n    X         OBJ       0         MATCH     1\n    Y         MATCH     1\nRHS\n    RHS1      MATCH     1\nBOUNDS\n FX BND1      X         9007199254740993\n FX BND1      Y         -9007199254740992\nENDATA\n",
            "o 0\nv X = 9007199254740993\nv Y = -9007199254740992\n",
        ),
        (
            "rhs-loss",
            "NAME          EXACT\nROWS\n N  OBJ\n E  MATCH\nCOLUMNS\n    X         OBJ       0         MATCH     1\n    Y         MATCH     1\nRHS\n    RHS1      MATCH     9007199254740993\nBOUNDS\n FX BND1      X         9007199254740992\n FX BND1      Y         1\nENDATA\n",
            "o 0\nv X = 9007199254740992\nv Y = 1\n",
        ),
        (
            "range-sum-loss",
            "NAME          EXACT\nROWS\n N  OBJ\n G  MATCH\nCOLUMNS\n    X         OBJ       0         MATCH     1\n    Y         MATCH     1\nRHS\n    RHS1      MATCH     9007199254740992\nRANGES\n    RNG       MATCH     1\nBOUNDS\n FX BND1      X         9007199254740992\n FX BND1      Y         1\nENDATA\n",
            "o 0\nv X = 9007199254740992\nv Y = 1\n",
        ),
        (
            "coefficient-sum-loss",
            "NAME          EXACT\nROWS\n N  OBJ\n E  MATCH\nCOLUMNS\n    X         OBJ       0         MATCH     9007199254740992\n    X         MATCH     1\n    Y         MATCH     -9007199254740992\nRHS\n    RHS1      MATCH     1\nBOUNDS\n FX BND1      X         1\n FX BND1      Y         1\nENDATA\n",
            "o 0\nv X = 1\nv Y = 1\n",
        ),
        (
            "decimal-exponent-loss",
            "NAME          EXACT\nROWS\n N  OBJ\n E  MATCH\nCOLUMNS\n    X         OBJ       0         MATCH     9.007199254740993e15\n    Y         MATCH     -9007199254740992\nRHS\n    RHS1      MATCH     1\nBOUNDS\n FX BND1      X         1\n FX BND1      Y         1\nENDATA\n",
            "o 0\nv X = 1\nv Y = 1\n",
        ),
        (
            "cancel-sat",
            "NAME          EXACT\nROWS\n N  OBJ\n E  MATCH\nCOLUMNS\n    X         OBJ       1        MATCH     9007199254740993\n    Y         MATCH     -9007199254740992\nRHS\n    RHS1      MATCH     1\nBOUNDS\n FX BND1      X         1\n FX BND1      Y         1\nENDATA\n",
            "o 1\nv X = 1\nv Y = 1\n",
        ),
    ];

    /// AY-N11: the six files end `s OPTIMAL` with their witness, never
    /// `s INFEASIBLE`.
    #[test]
    fn test_six_exactly_feasible_files_are_solved_not_called_infeasible() {
        for (name, text, block) in SIX {
            let (code, out) = solve_mps(text);
            assert_eq!(code, Ok(0), "{name}\n{out}");
            assert!(out.ends_with("s OPTIMAL\n"), "{name}\n{out}");
            assert_eq!(last_block(&out), block, "{name}\n{out}");
        }
    }

    /// The reviewers' `cancel-bad`: with X = Y = 1 fixed the row
    /// 9007199254740993 X - 9007199254740992 Y = 0 has activity 1, so the
    /// model is infeasible. Through `f64` the coefficients cancel and ay
    /// printed `o 1` and `s OPTIMAL`.
    #[test]
    fn test_cancel_bad_is_not_called_optimal() {
        let text = "NAME          EXACT\nROWS\n N  OBJ\n E  MATCH\nCOLUMNS\n    X         OBJ       1        MATCH     9007199254740993\n    Y         MATCH     -9007199254740992\nRHS\n    RHS1      MATCH     0\nBOUNDS\n FX BND1      X         1\n FX BND1      Y         1\nENDATA\n";
        let (code, out) = solve_mps(text);
        assert!(!out.contains("\no "), "{out}");
        assert!(!out.contains("s OPTIMAL"), "{out}");
        assert_eq!(code, Ok(10), "{out}");
        assert!(out.ends_with("s INFEASIBLE\n"), "{out}");
    }

    /// Review findings on the sparse route (2460ba614): each file is read
    /// as the organizers' checker reads it.
    #[test]
    fn test_reviewers_counterexample_kinds() {
        // `OBJSENSE MAX` on the header line: a maximisation (it was
        // minimised, `o 0`).
        let (code, out) = solve_mps(
            "NAME S\nOBJSENSE MAX\nROWS\n N OBJ\n L C1\nCOLUMNS\n    X OBJ 1 C1 1\nRHS\n    RHS C1 5\nENDATA\n",
        );
        assert_eq!(code, Ok(0), "{out}");
        assert_eq!(last_block(&out), "o 5\nv X = 5\n", "{out}");
        assert!(out.ends_with("s OPTIMAL\n"), "{out}");
        // A constraint row sharing its name with a second N row: refused (it
        // was dropped, and the free row's entries ignored).
        let (code, out) = solve_mps(
            "NAME D\nROWS\n N OBJ\n N SPARE\n L SPARE\nCOLUMNS\n    X OBJ -1 SPARE 1\nRHS\n    RHS SPARE 3\nBOUNDS\n UP BND X 10\nENDATA\n",
        );
        assert!(code.is_err() && !out.contains("\ns "), "{code:?}\n{out}");
        // A marker integer column with `UP 1` and then `LO 2`: the checker's
        // model is x in [2, +inf) (the later entry resets the upper bound);
        // max x with x <= 5 is 5. It was read as [2, 1], `s INFEASIBLE`.
        let (code, out) = solve_mps(
            "NAME B\nOBJSENSE\n    MAX\nROWS\n N OBJ\n L C1\nCOLUMNS\n    M 'MARKER' 'INTORG'\n    X OBJ 1 C1 1\n    M 'MARKER' 'INTEND'\nRHS\n    RHS C1 5\nBOUNDS\n UP BND X 1\n LO BND X 2\nENDATA\n",
        );
        assert_eq!(code, Ok(0), "{out}");
        assert_eq!(last_block(&out), "o 5\nv X = 5\n", "{out}");
        assert!(out.ends_with("s OPTIMAL\n"), "{out}");
        // `BV` intersects the bounds with [0, 1]: x <= 0.5 then BV leaves
        // x = 0 the only value; it was reset to [0, 1] (max 1).
        let (code, out) = solve_mps(
            "NAME V\nOBJSENSE\n    MAX\nROWS\n N OBJ\n L C1\nCOLUMNS\n    X OBJ 1 C1 1\nRHS\n    RHS C1 5\nBOUNDS\n UP BND X 0.5\n BV BND X\nENDATA\n",
        );
        assert_eq!(code, Ok(0), "{out}");
        assert_eq!(last_block(&out), "o 0\nv X = 0\n", "{out}");
        assert!(out.ends_with("s OPTIMAL\n"), "{out}");
        // The objective constant (minus the objective row's RHS) is in `o`.
        let (code, out) = solve_mps(
            "NAME O\nROWS\n N OBJ\n G C1\nCOLUMNS\n    X OBJ 2 C1 1\nRHS\n    RHS OBJ -3 C1 0.1\nENDATA\n",
        );
        assert_eq!(code, Ok(0), "{out}");
        assert_eq!(last_block(&out), "o 3.2\nv X = 0.1\n", "{out}");
        assert!(out.ends_with("s OPTIMAL\n"), "{out}");
    }

    /// The answer a reader following the proposed MIPcc wrapper rule takes
    /// from `text`: the last block whose `c solution end <n>` line came with
    /// `n` `v` lines.
    fn complete_answer(text: &str) -> Option<(String, Vec<String>)> {
        let mut answer = None;
        let mut pending: Option<(String, Vec<String>)> = None;
        // A cut file's last line is read as it is, cut, as Python does.
        for line in text.lines() {
            if let Some(obj) = line.strip_prefix("o ") {
                pending = Some((obj.to_string(), Vec::new()));
            } else if let Some(v) = line.strip_prefix("v ") {
                if let Some((_, values)) = pending.as_mut() {
                    values.push(v.to_string());
                }
            } else if let Some(n) = line.strip_prefix("c solution end ") {
                if let Some(block) = pending.take() {
                    if n.parse::<usize>().ok() == Some(block.1.len()) {
                        answer = Some(block);
                    }
                }
            }
        }
        answer
    }

    /// A run's output cut at any byte gives, to that reader, either no
    /// answer or one of the complete blocks written, never a cut one. (The
    /// same output read the old way, the last `o` and the `v` lines after
    /// it, takes a cut block as the answer.)
    #[test]
    fn test_a_cut_block_is_never_taken_for_an_answer() {
        let problem = knapsack();
        let mut out: Vec<u8> = Vec::new();
        let (result, incumbents) = solve_reporting_incumbents(&problem, &mut out).expect("solve");
        final_status(&problem, &result, incumbents, &mut out).expect("status");
        let text = String::from_utf8(out).expect("utf8");
        assert!(text.contains("c solution end 2\n"), "{text}");
        let blocks: Vec<(String, Vec<String>)> = format!("\n{text}")
            .split("\no ")
            .skip(1)
            .map(|b| {
                let mut lines = b.lines();
                let obj = lines.next().unwrap_or_default().to_string();
                let values = lines
                    .take_while(|l| l.starts_with("v "))
                    .map(|l| l["v ".len()..].to_string())
                    .collect();
                (obj, values)
            })
            .collect();
        let mut cut_taken_the_old_way = 0;
        for end in 0..=text.len() {
            let cut = &text[..end];
            if let Some(answer) = complete_answer(cut) {
                assert!(blocks.contains(&answer), "cut at {end}: {answer:?}");
                assert_eq!(answer.1.len(), 2);
            }
            let start = cut.rfind("\no ");
            if start.is_some_and(|s| cut[s..].matches("\nv ").count() < 2) {
                cut_taken_the_old_way += 1;
            }
        }
        assert!(cut_taken_the_old_way > 0);
        assert_eq!(complete_answer(&text).map(|a| a.0), Some("8".to_string()));
    }
}
