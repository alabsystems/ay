// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay lp solve FILE` subcommand.
//!
//! Reads an MPS or CPLEX LP file exactly and solves it with AY's sparse MILP
//! engine, printing only verdicts confirmed on the exact model
//! ([`sparse`]). The format is inferred from the file extension and falls
//! back to content sniffing via [`ay_lp::detect_format`].

use std::fs;
use std::io::{Read as _, Write};
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result};
use ay_lp::{detect_format, parse_lp_exact, parse_mps_exact, InputFormat, Sense};
use clap::Subcommand;

mod sparse;

#[cfg(test)]
mod differential_tests;
#[cfg(test)]
mod lp_differential_tests;

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

        /// Wall-clock limit in seconds. Without it
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
    z3_transcript(
        &input,
        display_model,
        display_stats,
        &mut std::io::stdout().lock(),
    )
}

/// Z3's `-lp` transcript for `input`, from the route `ay lp solve` takes:
/// the exact reading ([`parse_lp_exact`]) solved by [`sparse::solve_sparse`].
/// `sat` and the optimum only when the optimum was confirmed exactly,
/// `unsat` only when the infeasibility was, `unknown` otherwise.
fn z3_transcript(
    input: &str,
    display_model: bool,
    display_stats: bool,
    out: &mut dyn Write,
) -> Result<i32> {
    let exact = parse_lp_exact(input).context("parsing CPLEX LP input")?;
    let mut transcript: Vec<u8> = Vec::new();
    let (end, _) = sparse::solve_sparse(&exact, None, &mut transcript)?;
    let transcript = String::from_utf8_lossy(&transcript);
    let mut text = String::new();
    match (end, last_block(&transcript, exact.columns.len())) {
        (sparse::SparseEnd::Optimal, Some((objective, values))) => {
            text.push_str("sat\n");
            if display_stats {
                text.push_str("time:                0.00 secs\n");
            }
            if display_model {
                for (column, value) in exact.columns.iter().zip(&values) {
                    let integral = column.is_integral();
                    let sort = if integral { "Int" } else { "Real" };
                    text.push_str(&format!(
                        "(define-fun {} () {sort}\n  {})\n",
                        column.name,
                        z3_number(value, !integral)
                    ));
                }
            }
            text.push_str(&format!("   {}\n", z3_number(&objective, false)));
        }
        (sparse::SparseEnd::Infeasible, _) => text.push_str("unsat\n"),
        _ => text.push_str("unknown\n"),
    }
    out.write_all(text.as_bytes())
        .and_then(|()| out.flush())
        .context("writing to stdout")?;
    Ok(0)
}

/// The objective text and the `n` value texts of the last whole `o`/`v`
/// block of a transcript of [`sparse::solve_sparse`].
fn last_block(transcript: &str, n: usize) -> Option<(String, Vec<String>)> {
    let start = transcript.rfind("\no ").map_or(0, |i| i + 1);
    let mut lines = transcript[start..].lines();
    let objective = lines.next()?.strip_prefix("o ")?.to_string();
    let values: Vec<String> = lines
        .take(n)
        .map(|l| l.split_once(" = ").map(|(_, v)| v.to_string()))
        .collect::<Option<_>>()?;
    (values.len() == n).then_some((objective, values))
}

/// A checked decimal text as Z3 prints it: a Real that is an integer gets
/// `.0`.
fn z3_number(text: &str, force_real: bool) -> String {
    let integer = !text.contains(['.', 'e', 'E']);
    if force_real && integer {
        format!("{text}.0")
    } else {
        text.to_string()
    }
}

/// Solves `file`. MPS and CPLEX LP input are both read exactly
/// ([`parse_mps_exact`], [`parse_lp_exact`]) and go to AY's sparse MILP
/// engine ([`sparse::solve_sparse`]), which prints a verdict only when it is
/// confirmed on the exact model.
fn run_solve(
    file: &Path,
    forced_format: Option<&str>,
    time_limit: Option<Duration>,
    out: &mut dyn Write,
) -> Result<i32> {
    let input =
        fs::read_to_string(file).with_context(|| format!("failed to read '{}'", file.display()))?;

    // The one reading every route, check and printed number uses.
    let exact = match resolve_format(file, &input, forced_format)? {
        InputFormat::Mps => parse_mps_exact(&input)
            .with_context(|| format!("failed to parse MPS '{}'", file.display()))?,
        InputFormat::Lp => parse_lp_exact(&input)
            .with_context(|| format!("failed to parse LP '{}'", file.display()))?,
        _ => anyhow::bail!("unsupported input format detected"),
    };
    let integers = exact.columns.iter().filter(|c| c.is_integral()).count();
    write_block(
        out,
        &canonical_lines(exact.sense, exact.columns.len(), exact.rows.len(), integers),
    )
    .context("writing to stdout")?;
    let (end, written) = sparse::solve_sparse(&exact, time_limit, out)?;
    sparse_status(end, written, out)
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
/// (the codes of [`run`]): a stop without a confirmed verdict is not an
/// error of the run; it ends `s FEASIBLE` when a checked point was written
/// (that block is the answer) and `s UNKNOWN` otherwise, and exits 0.
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

    const KNAPSACK_LP: &str = "Maximize
 3 x + 4 y
Subject To
 cap: 2 x + 3 y <= 6
Bounds
 0 <= x <= 2
 0 <= y <= 2
General
 x y
End
";

    /// Runs `ay lp solve` on `text` as a file with `suffix` and a 60 s
    /// limit: (exit code, stdout, or the parse error).
    fn solve_text(text: &str, suffix: &str) -> (Result<i32, String>, String) {
        let mut f = tempfile::Builder::new()
            .suffix(suffix)
            .tempfile()
            .expect("tmp");
        f.write_all(text.as_bytes()).expect("write");
        let mut out: Vec<u8> = Vec::new();
        let code = run_solve(f.path(), None, Some(Duration::from_secs(60)), &mut out)
            .map_err(|e| format!("{e:#}"));
        (code, String::from_utf8(out).expect("utf8"))
    }

    /// Each checked point is written as one complete `o`/`v` block before
    /// the final status; the optimum of an LP-format file is confirmed on
    /// the exact model like that of an MPS file.
    #[test]
    fn test_incumbent_blocks_precede_final_status() {
        let (code, text) = solve_text(KNAPSACK_LP, ".lp");
        assert_eq!(code, Ok(0), "{text}");
        let first_o = text.find("\no ").expect("o line");
        let status = text.find("s OPTIMAL").expect("status");
        assert!(first_o < status, "{text}");
        assert!(
            text.contains("o 8\nv x = 0\nv y = 2\nc solution end 2\nc optimal: "),
            "{text}"
        );
        assert!(text.ends_with("s OPTIMAL\n"), "{text}");
    }

    /// AY-N6: a solve that stops without a confirmed verdict ends with a
    /// status line and exit 0 instead of an error: `s UNKNOWN` without a
    /// written point, `s FEASIBLE` after one (whose block is the answer).
    #[test]
    fn test_stopped_solve_reports_unknown_or_feasible() {
        let mut out: Vec<u8> = Vec::new();
        assert_eq!(
            sparse_status(sparse::SparseEnd::Stopped, 0, &mut out).expect("status"),
            0
        );
        assert_eq!(String::from_utf8(out).expect("utf8"), "s UNKNOWN\n");
        let mut out: Vec<u8> = Vec::new();
        assert_eq!(
            sparse_status(sparse::SparseEnd::Stopped, 2, &mut out).expect("status"),
            0
        );
        assert_eq!(String::from_utf8(out).expect("utf8"), "s FEASIBLE\n");
        let mut out: Vec<u8> = Vec::new();
        assert_eq!(
            sparse_status(sparse::SparseEnd::Infeasible, 0, &mut out).expect("status"),
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

    fn solve_mps(text: &str) -> (Result<i32, String>, String) {
        solve_text(text, ".mps")
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
        let (_, text) = solve_text(KNAPSACK_LP, ".lp");
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

    /// AY-N12: the six AY-N11 models written in CPLEX LP format, with the
    /// witness each must end with. ay's main read LP numbers as `f64` and
    /// printed the dense simplex's `s INFEASIBLE` on all six.
    const SIX_LP: [(&str, &str, &str); 6] = [
        (
            "bound-loss",
            "Minimize\n obj: 0 X\nSubject To\n MATCH: X + Y = 1\nBounds\n X = 9007199254740993\n Y = -9007199254740992\nEnd\n",
            "o 0\nv X = 9007199254740993\nv Y = -9007199254740992\n",
        ),
        (
            "rhs-loss",
            "Minimize\n obj: 0 X\nSubject To\n MATCH: X + Y = 9007199254740993\nBounds\n X = 9007199254740992\n Y = 1\nEnd\n",
            "o 0\nv X = 9007199254740992\nv Y = 1\n",
        ),
        (
            "range-sum-loss",
            "Minimize\n obj: 0 X\nSubject To\n MATCH: X + Y >= 9007199254740992\n MATCH_rng: X + Y <= 9007199254740993\nBounds\n X = 9007199254740992\n Y = 1\nEnd\n",
            "o 0\nv X = 9007199254740992\nv Y = 1\n",
        ),
        (
            "coefficient-sum-loss",
            "Minimize\n obj: 0 X\nSubject To\n MATCH: 9007199254740992 X + X - 9007199254740992 Y = 1\nBounds\n X = 1\n Y = 1\nEnd\n",
            "o 0\nv X = 1\nv Y = 1\n",
        ),
        (
            "decimal-exponent-loss",
            "Minimize\n obj: 0 X\nSubject To\n MATCH: 9.007199254740993e15 X - 9007199254740992 Y = 1\nBounds\n X = 1\n Y = 1\nEnd\n",
            "o 0\nv X = 1\nv Y = 1\n",
        ),
        (
            "cancel-sat",
            "Minimize\n obj: X\nSubject To\n MATCH: 9007199254740993 X - 9007199254740992 Y = 1\nBounds\n X = 1\n Y = 1\nEnd\n",
            "o 1\nv X = 1\nv Y = 1\n",
        ),
    ];

    /// `cancel-bad` in LP format: infeasible (activity 1, side 0); main
    /// printed `o 1` and `s OPTIMAL`.
    const CANCEL_BAD_LP: &str = "Minimize\n obj: X\nSubject To\n MATCH: 9007199254740993 X - 9007199254740992 Y = 0\nBounds\n X = 1\n Y = 1\nEnd\n";

    /// AY-N12: the six LP files end `s OPTIMAL` with their witness, and
    /// `cancel-bad` ends `s INFEASIBLE` without a point.
    #[test]
    fn test_six_exactly_feasible_lp_files_are_solved_not_called_infeasible() {
        for (name, text, block) in SIX_LP {
            let (code, out) = solve_text(text, ".lp");
            assert_eq!(code, Ok(0), "{name}\n{out}");
            assert!(out.ends_with("s OPTIMAL\n"), "{name}\n{out}");
            assert_eq!(last_block(&out), block, "{name}\n{out}");
        }
        let (code, out) = solve_text(CANCEL_BAD_LP, ".lp");
        assert!(!out.contains("\no "), "{out}");
        assert_eq!(code, Ok(10), "{out}");
        assert!(out.ends_with("s INFEASIBLE\n"), "{out}");
    }

    /// AY-N12: LP input gets no verdict the exact route cannot confirm, and
    /// constructs readers disagree on are refused before anything is
    /// printed.
    #[test]
    fn test_lp_constructs_readers_disagree_on_get_no_verdict() {
        for (name, text) in [
            (
                "binary with bounds",
                "Maximize\n x\nBounds\n x >= 2\nBinary\n x\nEnd\n",
            ),
            (
                "negative upper bound",
                "Minimize\n x\nBounds\n x <= -1\nEnd\n",
            ),
            (
                "bound in [1e20, 1e30)",
                "Maximize\n x\nBounds\n x <= 1e25\nEnd\n",
            ),
            ("no End", "Minimize\n x\nSubject To\n c: x >= 1\n"),
            (
                "semi-continuous",
                "Minimize\n x\nSubject To\n c: x >= 1\nSemi-continuous\n x\nEnd\n",
            ),
        ] {
            let (code, out) = solve_text(text, ".lp");
            assert!(code.is_err(), "{name}: {code:?}\n{out}");
            assert!(!out.contains("s "), "{name}: {out}");
        }
    }

    /// The z3-compatible `-lp` transcript comes from the same confirmed
    /// route: `sat` with the exact optimum, `unsat` only when confirmed.
    #[test]
    fn test_z3_lp_transcript_is_confirmed_exactly() {
        let transcript = |text: &str, model: bool| {
            let mut out: Vec<u8> = Vec::new();
            let code = z3_transcript(text, model, false, &mut out).expect("transcript");
            assert_eq!(code, 0);
            String::from_utf8(out).expect("utf8")
        };
        assert_eq!(transcript(SIX_LP[0].1, false), "sat\n   0\n");
        assert_eq!(
            transcript(SIX_LP[5].1, true),
            "sat\n(define-fun X () Real\n  1.0)\n(define-fun Y () Real\n  1.0)\n   1\n"
        );
        assert_eq!(transcript(CANCEL_BAD_LP, false), "unsat\n");
        assert_eq!(
            transcript("minimize\nx\nsubject to\nx >= 2\nend\n", false),
            "sat\n   2\n"
        );
    }
}
