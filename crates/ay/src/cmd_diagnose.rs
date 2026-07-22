// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay diagnose` subcommand — "why is ay wrong on this input?"
//!
//! One-shot verdict-dispute diagnostic. Runs ay with model validation enabled,
//! differentially compares against z3 when available, dumps the assertions
//! and models that disagree, and prints a one-paragraph plain-English summary.
//!
//! This wires existing transparency surfaces (`--validate`, `--explain`,
//! `--stats-json`, `--proof`, `(get-model)`, `(get-assertions)`) behind a
//! single entry point. It does NOT add new debug channels or a new solver
//! pipeline.
//!
//! Example:
//!
//! ```text
//! $ ay diagnose failing.smt2
//! ...
//! $ ay diagnose failing.smt2 --expected sat
//! ...
//! $ ay diagnose failing.smt2 --reference z3
//! ```
//!
//! Exit codes:
//!   0 — no definite verdict dispute was found
//!   1 — tooling failure (couldn't spawn ay / parse input / etc.)
//!   2 — ay's definite verdict disagrees with a declared expectation or reference
//!   3 — ay returned `unknown` where a declared or reference verdict was available

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use anyhow::{Context, Result};
use clap::{Args, ValueEnum};

use crate::cmd_bisect::{
    DIAGNOSE_SAT_EXPECTATION_CONFLICT_SUMMARY as SAT_EXPECTATION_CONFLICT_SUMMARY,
    DIAGNOSE_UNSAT_EXPECTATION_CONFLICT_SUMMARY as UNSAT_EXPECTATION_CONFLICT_SUMMARY,
};

#[derive(Debug, Clone, Default)]
struct BinaryIdentity {
    path: String,
    version: Option<String>,
    increment: Option<String>,
    commit: Option<String>,
    datetime_utc: Option<String>,
    stamp: Option<String>,
    summary: Option<String>,
}

impl BinaryIdentity {
    fn probe(path: &Path) -> Self {
        let mut identity = Self {
            path: canonical_display_path(path),
            ..Self::default()
        };

        let output = match Command::new(path).arg("--version").output() {
            Ok(output) if output.status.success() => output,
            _ => return identity,
        };
        let text = preferred_version_output(&output);
        if text.trim().is_empty() {
            return identity;
        }

        identity.version = extract_build_field(&text, "build.version");
        identity.increment = extract_build_field(&text, "build.increment");
        identity.commit = extract_build_field(&text, "build.commit");
        identity.datetime_utc = extract_build_field(&text, "build.datetime_utc");
        identity.stamp = extract_build_field(&text, "build.stamp");
        identity.summary = identity
            .stamp
            .clone()
            .or_else(|| first_nonempty_version_line(&text));
        identity
    }

    fn display_build(&self) -> &str {
        self.summary
            .as_deref()
            .unwrap_or("(unavailable from --version)")
    }
}

/// Arguments for `ay diagnose FILE`.
#[derive(Args, Debug)]
pub(crate) struct DiagnoseCommand {
    /// Input SMT-LIB2 or DIMACS CNF file.
    pub(crate) file: PathBuf,

    /// Declared expected verdict. If omitted, uses `(set-info :status ...)`
    /// from the input file when present. A reference result remains a
    /// cross-check and is never promoted to an expected verdict.
    #[arg(long, value_enum)]
    pub(crate) expected: Option<ExpectedArg>,

    /// Reference solver binary to cross-check against (must accept the same
    /// input file and print `sat`/`unsat`/`unknown`). Use `none` to skip.
    /// Defaults to `z3` if found on PATH, else `none`.
    #[arg(long, value_name = "BIN")]
    pub(crate) reference: Option<String>,

    /// Per-solve timeout in seconds.
    #[arg(long, default_value_t = 30)]
    pub(crate) timeout: u64,

    /// Explicit ay binary path. Defaults to the currently-executing ay binary.
    #[arg(long, value_name = "PATH")]
    pub(crate) ay_binary: Option<PathBuf>,

    /// Emit machine-readable JSON on stdout instead of the text report.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
pub(crate) enum ExpectedArg {
    Sat,
    Unsat,
}

impl ExpectedArg {
    fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

/// Per-solver invocation result.
#[derive(Debug, Clone)]
struct SolveRun {
    verdict: Verdict,
    stdout: String,
    #[allow(dead_code)]
    stderr: String,
    timed_out: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
    Error,
}

impl Verdict {
    fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
            Self::Error => "error",
        }
    }

    fn definitive(self) -> Option<Self> {
        match self {
            Self::Sat | Self::Unsat => Some(self),
            Self::Unknown | Self::Error => None,
        }
    }

    fn disagrees_with(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Sat, Self::Unsat) | (Self::Unsat, Self::Sat)
        )
    }

    #[allow(dead_code)] // Used in tests; kept as public-ish helper on the Verdict enum.
    fn matches_expected(self, expected: ExpectedArg) -> bool {
        matches!(
            (self, expected),
            (Self::Sat, ExpectedArg::Sat) | (Self::Unsat, ExpectedArg::Unsat)
        )
    }
}

pub(crate) fn run(cmd: &DiagnoseCommand) -> Result<i32> {
    if !cmd.file.exists() {
        anyhow::bail!("input file not found: {}", cmd.file.display());
    }

    let ay_binary = match cmd.ay_binary.clone() {
        Some(p) => p,
        None => std::env::current_exe().context("locating the current ay executable")?,
    };
    let ay_identity = BinaryIdentity::probe(&ay_binary);

    let timeout = Duration::from_secs(cmd.timeout);
    let input_text = fs::read_to_string(&cmd.file).unwrap_or_default();
    let expected = cmd
        .expected
        .or_else(|| parse_status_annotation(&input_text));

    // 1. Run ay with --validate to force model checking.
    let ay_run = run_ay_with_validate(&ay_binary, &cmd.file, timeout)?;

    // 2. Optionally run reference solver.
    let reference_binary = resolve_reference_binary(cmd.reference.as_deref());
    let reference_run = match reference_binary.as_deref() {
        Some(bin) => Some(run_reference(bin, &cmd.file, timeout)?),
        None => None,
    };

    // 3. Keep declared expectations and reference evidence separate. Neither a
    // benchmark :status field nor a second solver is a proof by itself.
    let declared_expected: Option<Verdict> = expected.map(|e| match e {
        ExpectedArg::Sat => Verdict::Sat,
        ExpectedArg::Unsat => Verdict::Unsat,
    });
    let reference_verdict = reference_run
        .as_ref()
        .and_then(|run| run.verdict.definitive());
    let expected_dispute =
        declared_expected.is_some_and(|expected| ay_run.verdict.disagrees_with(expected));
    let reference_dispute =
        reference_verdict.is_some_and(|reference| ay_run.verdict.disagrees_with(reference));

    // 4. Decide exit code.
    let exit_code: i32 = if expected_dispute || reference_dispute {
        2
    } else if ay_run.verdict == Verdict::Unknown
        && (declared_expected.is_some() || reference_verdict.is_some())
    {
        3
    } else if ay_run.verdict == Verdict::Error {
        1
    } else {
        0
    };

    // 5. If ay said SAT and we want to check its model, fetch --explain output.
    // Run --explain for any SAT or UNSAT verdict — the output is immediately
    // useful whether or not there's a disagreement.
    let explain_output: Option<String> = if matches!(ay_run.verdict, Verdict::Sat | Verdict::Unsat)
    {
        run_ay_explain(&ay_binary, &cmd.file, timeout).ok()
    } else {
        None
    };

    // 6. Render report.
    if cmd.json {
        let report = build_json_report(
            &cmd.file,
            &ay_identity,
            &ay_run,
            reference_binary.as_deref(),
            reference_run.as_ref(),
            expected,
            declared_expected,
            explain_output.as_deref(),
            exit_code,
        );
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print_text_report(
            &cmd.file,
            &ay_identity,
            &ay_run,
            reference_binary.as_deref(),
            reference_run.as_ref(),
            expected,
            declared_expected,
            explain_output.as_deref(),
            exit_code,
        );
    }

    Ok(exit_code)
}

/// Parse `(set-info :status sat)` / `(set-info :status unsat)` from SMT-LIB input.
///
/// Returns `None` for `:status unknown`, missing annotations, or non-SMT-LIB
/// input (DIMACS CNF doesn't carry a status annotation we care about here).
fn parse_status_annotation(text: &str) -> Option<ExpectedArg> {
    // Cheap substring scan; we don't need a full parser for this.
    let mut idx = 0;
    while let Some(pos) = text[idx..].find(":status") {
        let after = &text[idx + pos + ":status".len()..];
        let trimmed = after.trim_start();
        if let Some(rest) = trimmed.strip_prefix("sat") {
            if rest.starts_with(|c: char| c.is_whitespace() || c == ')') {
                return Some(ExpectedArg::Sat);
            }
        }
        if let Some(rest) = trimmed.strip_prefix("unsat") {
            if rest.starts_with(|c: char| c.is_whitespace() || c == ')') {
                return Some(ExpectedArg::Unsat);
            }
        }
        idx = idx + pos + ":status".len();
    }
    None
}

/// Locate a reference solver on PATH. Returns `None` when disabled.
fn resolve_reference_binary(requested: Option<&str>) -> Option<String> {
    match requested {
        Some("none") => None,
        Some(bin) => Some(bin.to_string()),
        None => {
            // Auto-detect z3.
            if let Ok(output) = Command::new("which").arg("z3").output() {
                if output.status.success() {
                    let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
                    if !path.is_empty() {
                        return Some("z3".to_string());
                    }
                }
            }
            None
        }
    }
}

/// Run ay with `--validate --stats-json` on the input file and capture verdict.
///
/// Passes `--no-verify-proof` to defeat the debug-build default that would
/// otherwise synthesize a DRAT proof path and reject SMT input with
/// "SMT-LIB mode requires Alethe output" (crates/ay/src/main.rs:1893).
fn run_ay_with_validate(ay: &Path, file: &Path, timeout: Duration) -> Result<SolveRun> {
    let mut cmd = Command::new(ay);
    cmd.arg("solve")
        .arg("--validate")
        .arg("--no-verify-proof")
        .arg("--stats-json")
        .arg(file);
    spawn_and_parse(&mut cmd, timeout)
}

/// Run ay with `--explain` on the input file to get human-readable constraint
/// verification for SAT and a core summary for UNSAT.
///
/// Passes `--no-verify-proof` for the same reason as `run_ay_with_validate`.
fn run_ay_explain(ay: &Path, file: &Path, timeout: Duration) -> Result<String> {
    let mut cmd = Command::new(ay);
    cmd.arg("solve")
        .arg("--explain")
        .arg("--no-verify-proof")
        .arg(file);
    let run = spawn_and_parse(&mut cmd, timeout)?;
    Ok(run.stdout)
}

/// Run a reference solver and capture verdict.
fn run_reference(bin: &str, file: &Path, timeout: Duration) -> Result<SolveRun> {
    let mut cmd = Command::new(bin);
    cmd.arg(file);
    spawn_and_parse(&mut cmd, timeout)
}

fn spawn_and_parse(cmd: &mut Command, timeout: Duration) -> Result<SolveRun> {
    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = cmd
        .spawn()
        .with_context(|| format!("failed to spawn {cmd:?}"))?;

    // Cooperative polling keeps timeout handling platform-neutral.
    let deadline = std::time::Instant::now() + timeout;
    let mut timed_out = false;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                if std::time::Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    timed_out = true;
                    break;
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => return Err(anyhow::anyhow!("wait failed: {e}")),
        }
    }

    let mut stdout = String::new();
    if let Some(mut pipe) = child.stdout.take() {
        let _ = pipe.read_to_string(&mut stdout);
    }
    let mut stderr = String::new();
    if let Some(mut pipe) = child.stderr.take() {
        let _ = pipe.read_to_string(&mut stderr);
    }

    let verdict = if timed_out {
        Verdict::Unknown
    } else {
        parse_verdict(&stdout)
    };

    Ok(SolveRun {
        verdict,
        stdout,
        stderr,
        timed_out,
    })
}

/// Parse `sat`/`unsat`/`unknown` lines from solver output. Last verdict wins.
fn parse_verdict(stdout: &str) -> Verdict {
    let mut last: Option<Verdict> = None;
    for line in stdout.lines() {
        match line.trim() {
            "sat" | "s SATISFIABLE" => last = Some(Verdict::Sat),
            "unsat" | "s UNSATISFIABLE" => last = Some(Verdict::Unsat),
            "unknown" | "s UNKNOWN" => last = Some(Verdict::Unknown),
            _ => {}
        }
    }
    last.unwrap_or(Verdict::Error)
}

fn canonical_display_path(path: &Path) -> String {
    path.canonicalize()
        .unwrap_or_else(|_| path.to_path_buf())
        .display()
        .to_string()
}

fn preferred_version_output(output: &std::process::Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if !stdout.is_empty() {
        return stdout;
    }
    String::from_utf8_lossy(&output.stderr).trim().to_string()
}

fn extract_build_field(text: &str, key: &str) -> Option<String> {
    let prefix = format!("{key}=");
    text.lines()
        .map(str::trim)
        .find_map(|line| line.strip_prefix(&prefix).map(str::to_owned))
}

fn first_nonempty_version_line(text: &str) -> Option<String> {
    text.lines()
        .map(str::trim)
        .find(|line| {
            !line.is_empty()
                && !line.contains('=')
                && !matches!(*line, "sat" | "unsat" | "unknown" | "error")
        })
        .map(str::to_owned)
}

// ---------------------------------------------------------------------------
// Text report
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn print_text_report(
    file: &Path,
    ay_identity: &BinaryIdentity,
    ay_run: &SolveRun,
    reference_bin: Option<&str>,
    reference_run: Option<&SolveRun>,
    expected: Option<ExpectedArg>,
    declared_expected: Option<Verdict>,
    explain_output: Option<&str>,
    exit_code: i32,
) {
    println!("=== ay diagnose: {} ===", file.display());
    println!();
    println!("  ay binary:       {}", ay_identity.path);
    println!("  ay build:        {}", ay_identity.display_build());
    println!(
        "  ay verdict:      {}{}",
        ay_run.verdict.as_str(),
        if ay_run.timed_out { " (timeout)" } else { "" }
    );
    if let Some(exp) = expected {
        println!(
            "  expected:        {} (from --expected or :status)",
            exp.as_str()
        );
    }
    if let Some(bin) = reference_bin {
        if let Some(r) = reference_run {
            println!(
                "  reference ({}): {}{}",
                bin,
                r.verdict.as_str(),
                if r.timed_out { " (timeout)" } else { "" }
            );
        }
    } else {
        println!("  reference:       (none — pass --reference z3 or install z3)");
    }
    println!();

    // 1. Verdict mismatch.
    if let Some(expected_v) = declared_expected {
        if ay_run.verdict.disagrees_with(expected_v) {
            println!(
                "DECLARED MISMATCH: ay returned {} but the declared expectation is {}.",
                ay_run.verdict.as_str(),
                expected_v.as_str()
            );
            println!();
        } else if ay_run.verdict == expected_v {
            println!("DECLARED MATCH: ay matches the declared expectation.");
            println!();
        } else {
            println!(
                "DECLARED INCONCLUSIVE: ay returned {}; the declared expectation is {}.",
                ay_run.verdict.as_str(),
                expected_v.as_str()
            );
            println!();
        }
    } else if let Some(reference_v) = reference_run.and_then(|run| run.verdict.definitive()) {
        if ay_run.verdict.disagrees_with(reference_v) {
            println!(
                "REFERENCE DISPUTE: ay returned {} and the reference returned {}.",
                ay_run.verdict.as_str(),
                reference_v.as_str()
            );
            println!("  This comparison does not establish which result is correct.");
            println!();
        } else if ay_run.verdict == reference_v {
            println!(
                "REFERENCE AGREEMENT: both solvers returned {}.",
                reference_v.as_str()
            );
            println!("  Agreement is a cross-check, not independent proof of the verdict.");
            println!();
        } else {
            println!(
                "REFERENCE INCONCLUSIVE: ay returned {}; the reference returned {}.",
                ay_run.verdict.as_str(),
                reference_v.as_str()
            );
            println!();
        }
    } else {
        println!("UNSCORED: no declared expectation or definite reference result.");
        println!("  Provide --expected sat|unsat or a trusted :status annotation to");
        println!("  record an expected verdict; use --reference only as a cross-check.");
        println!();
    }
    if let (Some(expected_v), Some(reference_v)) = (
        declared_expected,
        reference_run.and_then(|run| run.verdict.definitive()),
    ) {
        if expected_v.disagrees_with(reference_v) {
            println!(
                "EVIDENCE CONFLICT: declared expectation is {}; reference returned {}.",
                expected_v.as_str(),
                reference_v.as_str()
            );
            println!("  Resolve the label/reference conflict before classifying AY.");
            println!();
        }
    }

    // 2. ay --explain output (constraint verification).
    if let Some(explain) = explain_output {
        // The --explain block starts with "=== Explanation".
        if let Some(start) = explain.find("=== Explanation") {
            println!("--- ay --explain output ---");
            println!("{}", explain[start..].trim_end());
            println!();
        }
    }

    // 3. ay stats JSON (from --stats-json on stderr).
    if let Some(stats) = extract_stats_json(&ay_run.stderr) {
        println!("--- ay stats ---");
        println!("  {stats}");
        println!();
    }

    // 4. Plain-English summary.
    println!("--- diagnosis ---");
    let summary = plain_english_summary(ay_run, reference_run, declared_expected);
    println!("{summary}");
    println!();

    // 5. Next steps.
    println!("--- next steps ---");
    print_next_steps(file, ay_run, reference_run, declared_expected, exit_code);
}

fn extract_stats_json(stderr: &str) -> Option<&str> {
    // --stats-json dumps a single JSON line to stderr. Pick the first line
    // that looks like `{"...`. This is a best-effort surface.
    for line in stderr.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("{\"") && trimmed.ends_with('}') {
            return Some(trimmed);
        }
    }
    None
}

fn plain_english_summary(
    ay_run: &SolveRun,
    reference_run: Option<&SolveRun>,
    declared_expected: Option<Verdict>,
) -> String {
    if ay_run.timed_out {
        return "ay exceeded the configured timeout. Either increase --timeout or \
        look for a performance regression — run with --stats to see decisions, \
        conflicts, and time spent per phase."
            .to_string();
    }

    if let (Some(expected), Some(reference)) = (
        declared_expected,
        reference_run.and_then(|run| run.verdict.definitive()),
    ) {
        if expected.disagrees_with(reference) {
            return format!(
                "The declared expectation is {} but the reference returned {}. \
                The evidence sources conflict, so this run cannot identify a \
                wrong solver; resolve the label/reference dispute first.",
                expected.as_str(),
                reference.as_str()
            );
        }
    }

    match (ay_run.verdict, declared_expected) {
        (Verdict::Sat, Some(Verdict::Unsat)) => SAT_EXPECTATION_CONFLICT_SUMMARY.to_string(),
        (Verdict::Unsat, Some(Verdict::Sat)) => UNSAT_EXPECTATION_CONFLICT_SUMMARY.to_string(),
        (Verdict::Unknown, Some(_)) => {
            "AY returned UNKNOWN where a verdict exists. The stats above should \
            show whether the timeout fired or a theory returned unknown. Common \
            causes: (a) non-linear arithmetic / quantifier instantiation gave up; \
            (b) a theory combination hit max-fixpoint-rounds (raise with \
            `--max-fixpoint-rounds 500`); (c) memory limit was hit. Run with \
            `--debug theory,sync` to see which solver bailed."
                .to_string()
        }
        (Verdict::Error, _) => "AY crashed or produced unparseable output. Check stderr above for \
            the panic / parse error. Re-run with `--verbose` to get the tracing \
            subscriber, and build in debug mode (`cargo build`) for full verification \
            assertions. File a bug with the stderr trace."
            .to_string(),
        (v, Some(expected)) if v == expected => {
            format!(
                "AY matches the declared {} expectation. That checks this run \
                against the supplied label; it does not independently validate \
                the label.",
                v.as_str()
            )
        }
        _ => match reference_run.and_then(|run| run.verdict.definitive()) {
            Some(reference) if ay_run.verdict.disagrees_with(reference) => format!(
                "AY returned {} and the reference returned {}. Treat this as \
                    a dispute: preserve both runs and use a trusted benchmark \
                    label, model validation, or proof checker to resolve it.",
                ay_run.verdict.as_str(),
                reference.as_str()
            ),
            Some(reference) if ay_run.verdict == reference => format!(
                "AY and the reference both returned {}. This is useful \
                    differential evidence, but agreement between solvers is not \
                    an independent correctness proof.",
                reference.as_str()
            ),
            _ => format!(
                "AY returned {} with no declared expectation or definite \
                    reference result. Record a trusted expected verdict or check \
                    a model/proof before classifying correctness.",
                ay_run.verdict.as_str()
            ),
        },
    }
}

fn print_next_steps(
    file: &Path,
    ay_run: &SolveRun,
    reference_run: Option<&SolveRun>,
    declared_expected: Option<Verdict>,
    exit_code: i32,
) {
    let f = file.display();
    match (ay_run.verdict, declared_expected) {
        (Verdict::Sat, Some(Verdict::Unsat)) | (Verdict::Unsat, Some(Verdict::Sat)) => {
            print_disagreement_next_steps(file, declared_expected);
        }
        (Verdict::Unknown, _) => {
            println!("  1. Check timeout / memory limit:");
            println!("       ay solve --stats --timeout 60000 {f}");
            println!("  2. Raise fixpoint round cap:");
            println!("       ay solve --max-fixpoint-rounds 500 {f}");
            println!("  3. Enable theory tracing:");
            println!("       ay solve --debug theory,sync {f}");
        }
        (Verdict::Error, _) => {
            println!("  1. Get full tracing and stderr:");
            println!("       ay solve --verbose {f} 2>&1 | tail -50");
            println!("  2. Parse input with z3 to rule out a frontend bug:");
            println!("       z3 {f}");
        }
        _ if reference_run
            .and_then(|run| run.verdict.definitive())
            .is_some_and(|reference| ay_run.verdict.disagrees_with(reference)) =>
        {
            println!("  1. Preserve both solver outputs and binary versions.");
            println!("  2. Check a model or proof with an independent implementation.");
            println!("  3. Add a trusted --expected verdict only after resolving the dispute.");
        }
        _ if exit_code == 0 && declared_expected.is_some() => {
            println!("  (no further action — ay matches the declared expectation)");
        }
        _ if exit_code == 0 && reference_run.is_some() => {
            println!("  (no dispute found; reference agreement remains a cross-check)");
        }
        _ => {
            println!("  1. Provide a trusted --expected sat|unsat when one is available.");
            println!("  2. Use --reference z3 for differential evidence only.");
        }
    }
}

fn print_disagreement_next_steps(file: &Path, declared_expected: Option<Verdict>) {
    let expected_flag = match declared_expected {
        Some(Verdict::Sat) => "sat",
        Some(Verdict::Unsat) => "unsat",
        _ => "sat",
    };
    crate::cmd_bisect::print_diagnose_next_steps(file, expected_flag);
}

// ---------------------------------------------------------------------------
// JSON report
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn build_json_report(
    file: &Path,
    ay_identity: &BinaryIdentity,
    ay_run: &SolveRun,
    reference_bin: Option<&str>,
    reference_run: Option<&SolveRun>,
    expected: Option<ExpectedArg>,
    declared_expected: Option<Verdict>,
    explain_output: Option<&str>,
    exit_code: i32,
) -> serde_json::Value {
    let ref_json = reference_run.map(|r| {
        serde_json::json!({
            "binary": reference_bin,
            "verdict": r.verdict.as_str(),
            "timed_out": r.timed_out,
        })
    });

    let expected_dispute =
        declared_expected.is_some_and(|expected| ay_run.verdict.disagrees_with(expected));
    let reference_dispute = reference_run
        .and_then(|run| run.verdict.definitive())
        .is_some_and(|reference| ay_run.verdict.disagrees_with(reference));
    let evidence_conflict = match (
        declared_expected,
        reference_run.and_then(|run| run.verdict.definitive()),
    ) {
        (Some(expected), Some(reference)) => expected.disagrees_with(reference),
        _ => false,
    };

    serde_json::json!({
        "file": file.display().to_string(),
        "ay": {
            "binary": ay_identity.path.as_str(),
            "build": {
                "summary": ay_identity.display_build(),
                "version": ay_identity.version.as_deref(),
                "increment": ay_identity.increment.as_deref(),
                "commit": ay_identity.commit.as_deref(),
                "datetime_utc": ay_identity.datetime_utc.as_deref(),
                "stamp": ay_identity.stamp.as_deref(),
            },
            "verdict": ay_run.verdict.as_str(),
            "timed_out": ay_run.timed_out,
            "stats": extract_stats_json(&ay_run.stderr),
        },
        "reference": ref_json,
        "expected": expected.map(ExpectedArg::as_str),
        "declared_expected": declared_expected.map(Verdict::as_str),
        "exit_code": exit_code,
        "expected_dispute": expected_dispute,
        "reference_dispute": reference_dispute,
        "evidence_conflict": evidence_conflict,
        "disagreement": expected_dispute || reference_dispute,
        "explain_output": explain_output,
        "summary": plain_english_summary(ay_run, reference_run, declared_expected),
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_status_sat() {
        let text = "(set-info :status sat)\n(set-logic QF_LIA)";
        assert!(matches!(
            parse_status_annotation(text),
            Some(ExpectedArg::Sat)
        ));
    }

    #[test]
    fn test_parse_status_unsat() {
        let text = "(set-info :status unsat)\n(set-logic QF_LIA)";
        assert!(matches!(
            parse_status_annotation(text),
            Some(ExpectedArg::Unsat)
        ));
    }

    #[test]
    fn test_parse_status_unknown_is_none() {
        let text = "(set-info :status unknown)";
        assert!(parse_status_annotation(text).is_none());
    }

    #[test]
    fn test_parse_status_missing() {
        let text = "(set-logic QF_LIA)\n(assert true)";
        assert!(parse_status_annotation(text).is_none());
    }

    #[test]
    fn test_parse_verdict_sat_line() {
        assert_eq!(parse_verdict("sat\n"), Verdict::Sat);
    }

    #[test]
    fn test_parse_verdict_unsat_line() {
        assert_eq!(parse_verdict("unsat\n"), Verdict::Unsat);
    }

    #[test]
    fn test_parse_verdict_dimacs_sat() {
        assert_eq!(parse_verdict("s SATISFIABLE\nv 1 -2 0\n"), Verdict::Sat);
    }

    #[test]
    fn test_parse_verdict_dimacs_unsat() {
        assert_eq!(parse_verdict("s UNSATISFIABLE\n"), Verdict::Unsat);
    }

    #[test]
    fn test_parse_verdict_last_wins() {
        assert_eq!(parse_verdict("unknown\nsat\n"), Verdict::Sat);
    }

    #[test]
    fn test_parse_verdict_no_output() {
        assert_eq!(parse_verdict(""), Verdict::Error);
    }

    #[test]
    fn test_verdict_matches_expected() {
        assert!(Verdict::Sat.matches_expected(ExpectedArg::Sat));
        assert!(Verdict::Unsat.matches_expected(ExpectedArg::Unsat));
        assert!(!Verdict::Unknown.matches_expected(ExpectedArg::Sat));
        assert!(!Verdict::Sat.matches_expected(ExpectedArg::Unsat));
    }

    #[test]
    fn test_extract_stats_json() {
        let stderr = "some line\n{\"conflicts\":0,\"decisions\":4}\nother";
        let stats = extract_stats_json(stderr);
        assert!(stats.is_some());
        assert!(stats.unwrap().contains("conflicts"));
    }

    #[test]
    fn test_extract_stats_json_absent() {
        let stderr = "just some noise\nnothing here";
        assert!(extract_stats_json(stderr).is_none());
    }

    #[test]
    fn test_plain_english_summary_sat_expectation_conflict() {
        let ay_run = SolveRun {
            verdict: Verdict::Sat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
        };
        let summary = plain_english_summary(&ay_run, None, Some(Verdict::Unsat));
        assert!(summary.contains("evidence conflict"));
    }

    #[test]
    fn test_plain_english_summary_unsat_expectation_conflict() {
        let ay_run = SolveRun {
            verdict: Verdict::Unsat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
        };
        let summary = plain_english_summary(&ay_run, None, Some(Verdict::Sat));
        assert!(summary.contains("evidence conflict"));
    }

    #[test]
    fn test_plain_english_summary_agree() {
        let ay_run = SolveRun {
            verdict: Verdict::Sat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
        };
        let summary = plain_english_summary(&ay_run, None, Some(Verdict::Sat));
        assert!(summary.contains("matches the declared"));
    }

    #[test]
    fn test_reference_dispute_is_not_called_a_wrong_answer() {
        let ay_run = SolveRun {
            verdict: Verdict::Sat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
        };
        let reference_run = SolveRun {
            verdict: Verdict::Unsat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
        };
        let summary = plain_english_summary(&ay_run, Some(&reference_run), None);
        assert!(summary.contains("Treat this as a dispute"));
        assert!(!summary.contains("wrong answer"));
    }

    #[test]
    fn test_declared_and_reference_conflict_prevents_blame() {
        let ay_run = SolveRun {
            verdict: Verdict::Sat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
        };
        let reference_run = SolveRun {
            verdict: Verdict::Unsat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
        };
        let summary = plain_english_summary(&ay_run, Some(&reference_run), Some(Verdict::Sat));
        assert!(summary.contains("evidence sources conflict"));
        assert!(summary.contains("cannot identify a wrong solver"));
    }

    #[test]
    fn test_extract_build_field() {
        let text = "ay-build\nbuild.version=0.9.0\nbuild.commit=abc123";
        assert_eq!(
            extract_build_field(text, "build.version").as_deref(),
            Some("0.9.0")
        );
        assert_eq!(
            extract_build_field(text, "build.commit").as_deref(),
            Some("abc123")
        );
        assert!(extract_build_field(text, "build.stamp").is_none());
    }

    #[test]
    fn test_first_nonempty_version_line_ignores_verdict_words() {
        assert!(first_nonempty_version_line("sat\n").is_none());
        assert_eq!(
            first_nonempty_version_line(
                "ay-0.9.0+build\nbuild.version=0.9.0\nbuild.stamp=ay-0.9.0+build"
            )
            .as_deref(),
            Some("ay-0.9.0+build")
        );
    }
}
