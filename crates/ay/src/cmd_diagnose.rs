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
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use anyhow::{Context, Result};
use ay_sys::metadata_capture::{capture, CaptureLimits, DEFAULT_OUTPUT_BYTES};
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
    fn probe(path: &Path, mut limits: CaptureLimits) -> Self {
        let mut identity = Self {
            path: canonical_display_path(path),
            ..Self::default()
        };

        limits.timeout = limits.timeout.min(Duration::from_secs(5));
        let mut command = Command::new(path);
        command.arg("--version");
        let output = match capture(command, limits, "diagnostic binary identity") {
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
    /// Defaults to `z3` when a real z3 resolves, else `none`. `z3` means the
    /// z3 oracle: `Z3_PATH`, else the first z3 on PATH that proves it is z3,
    /// run by its path.
    #[arg(long, value_name = "BIN")]
    pub(crate) reference: Option<String>,

    /// Per-solve timeout in seconds.
    #[arg(long, default_value_t = 30)]
    pub(crate) timeout: u64,

    /// Per-child sampled resident memory ceiling in MiB. The default uses AY's
    /// governed/available-memory budget. Kernel bounds still restrict it.
    #[arg(long, value_parser = clap::value_parser!(u64).range(1..))]
    pub(crate) memory_mb: Option<u64>,

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
    memout: bool,
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
    let timeout = Duration::from_secs(cmd.timeout);
    anyhow::ensure!(!timeout.is_zero(), "diagnostic timeout must be positive");
    let native_budget = ay_sys::default_standalone_memory_limit();
    anyhow::ensure!(
        native_budget > 0,
        "no positive diagnostic memory budget is available"
    );
    // The native default already incorporates its peer share. Restrict it by
    // current kernel bounds without dividing that same share a second time.
    let native_budget = ay_sys::memory_ceiling::limit_under_ceiling_from(
        native_budget,
        ay_sys::memory_ceiling::KernelMemoryBounds::detect(),
        1,
    )
    .bound_bytes;
    let resident_bytes = match cmd.memory_mb {
        Some(mib) => {
            let bytes = mib
                .checked_mul(1024 * 1024)
                .and_then(|bytes| usize::try_from(bytes).ok())
                .context("diagnostic memory ceiling exceeds this platform's range")?;
            anyhow::ensure!(bytes > 0, "diagnostic memory ceiling must be positive");
            bytes.min(native_budget)
        }
        None => native_budget,
    };
    anyhow::ensure!(
        resident_bytes > 0,
        "no positive diagnostic memory budget is available"
    );
    let limits = CaptureLimits {
        timeout,
        output_bytes: DEFAULT_OUTPUT_BYTES,
        resident_bytes: Some(u64::try_from(resident_bytes).context("diagnostic memory range")?),
    };
    let ay_identity = BinaryIdentity::probe(&ay_binary, limits);
    let input_text = fs::read_to_string(&cmd.file).unwrap_or_default();
    let expected = cmd
        .expected
        .or_else(|| parse_status_annotation(&input_text));

    // 1. Run ay with --validate to force model checking.
    let ay_run = run_ay_with_validate(&ay_binary, &cmd.file, limits)?;

    // 2. Optionally run reference solver.
    let reference = resolve_reference_binary(cmd.reference.as_deref())?;
    let reference_run = match &reference {
        Some(reference) => Some(run_reference(&reference.program, &cmd.file, limits)?),
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
        match run_ay_explain(&ay_binary, &cmd.file, limits) {
            Ok(output) => Some(output),
            Err(error) => {
                eprintln!("ay diagnose: explanation unavailable: {error:#}");
                None
            }
        }
    } else {
        None
    };

    // 6. Render report.
    if cmd.json {
        let report = build_json_report(
            &cmd.file,
            &ay_identity,
            &ay_run,
            reference.as_ref(),
            reference_run.as_ref(),
            expected,
            declared_expected,
            explain_output.as_deref(),
            exit_code,
            limits,
        );
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print_text_report(
            &cmd.file,
            &ay_identity,
            &ay_run,
            reference.as_ref(),
            reference_run.as_ref(),
            expected,
            declared_expected,
            explain_output.as_deref(),
            exit_code,
            limits,
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

/// The reference solver a diagnosis runs: the program, and how reports name it.
struct Reference {
    program: String,
    label: String,
}

/// Locate the reference solver; `None` when disabled, or when auto-detection
/// finds no z3. `z3` (the default, or named) is the z3 oracle: resolved by
/// path and identity-checked (`ay_sys::z3_oracle`), never spawned by name —
/// under a sandbox the name can reach a refusing stub, whose silence would read
/// as "no reference verdict", and a drop-in install can make it AY itself.
fn resolve_reference_binary(requested: Option<&str>) -> Result<Option<Reference>> {
    let z3 = |oracle: &ay_sys::z3_oracle::Z3Oracle| Reference {
        program: oracle.path().display().to_string(),
        label: oracle.identity(),
    };
    match requested {
        Some("none") => Ok(None),
        None => Ok(ay_sys::z3_oracle::z3_oracle().ok().map(z3)),
        Some("z3") => ay_sys::z3_oracle::z3_oracle()
            .map(|oracle| Some(z3(oracle)))
            .map_err(|reason| anyhow::anyhow!("--reference z3: no usable z3: {reason}")),
        Some(bin) => Ok(Some(Reference {
            program: bin.to_string(),
            label: bin.to_string(),
        })),
    }
}

/// Run ay with `--validate --stats-json` on the input file and capture verdict.
///
/// Passes `--no-verify-proof` to defeat the debug-build default that would
/// otherwise synthesize a DRAT proof path and reject SMT input with
/// "SMT-LIB mode requires Alethe output" (crates/ay/src/main.rs:1893).
fn run_ay_with_validate(ay: &Path, file: &Path, limits: CaptureLimits) -> Result<SolveRun> {
    let mut cmd = Command::new(ay);
    cmd.arg("solve")
        .arg("--validate")
        .arg("--no-verify-proof")
        .arg("--stats-json")
        .arg(file);
    spawn_and_parse(cmd, limits)
}

/// Run ay with `--explain` on the input file to get human-readable constraint
/// verification for SAT and a core summary for UNSAT.
///
/// Passes `--no-verify-proof` for the same reason as `run_ay_with_validate`.
fn run_ay_explain(ay: &Path, file: &Path, limits: CaptureLimits) -> Result<String> {
    let mut cmd = Command::new(ay);
    cmd.arg("solve")
        .arg("--explain")
        .arg("--no-verify-proof")
        .arg(file);
    let run = spawn_and_parse(cmd, limits)?;
    anyhow::ensure!(
        matches!(run.verdict, Verdict::Sat | Verdict::Unsat),
        "explanation child did not supply a definite result (timeout={}, memout={}): {}",
        run.timed_out,
        run.memout,
        run.stderr
    );
    Ok(run.stdout)
}

/// Run a reference solver and capture verdict.
fn run_reference(bin: &str, file: &Path, limits: CaptureLimits) -> Result<SolveRun> {
    let mut cmd = Command::new(bin);
    cmd.arg(file);
    spawn_and_parse(cmd, limits)
}

fn spawn_and_parse(cmd: Command, limits: CaptureLimits) -> Result<SolveRun> {
    // The shared native capture drains both pipes while the original child
    // runs, bounds retained output/RSS and retires that original isolated
    // group. These restrictions are not machine admission or a reservation.
    let output = match capture(cmd, limits, "diagnostic solver") {
        Ok(output) => output,
        Err(error) if error.kind() == std::io::ErrorKind::TimedOut => {
            return Ok(SolveRun {
                verdict: Verdict::Unknown,
                stdout: String::new(),
                stderr: error.to_string(),
                timed_out: true,
                memout: false,
            });
        }
        Err(error) if ay_sys::metadata_capture::is_resident_limit(&error) => {
            return Ok(SolveRun {
                verdict: Verdict::Unknown,
                stdout: String::new(),
                stderr: error.to_string(),
                timed_out: false,
                memout: true,
            });
        }
        Err(error) => return Err(error).context("capturing diagnostic solver"),
    };
    parse_captured_run(output)
}

fn parse_captured_run(output: std::process::Output) -> Result<SolveRun> {
    let stdout = String::from_utf8(output.stdout).context("diagnostic stdout is not UTF-8")?;
    let stderr = String::from_utf8(output.stderr).context("diagnostic stderr is not UTF-8")?;
    // A failed executable cannot supply a definite reference verdict even
    // when it printed a plausible answer before failing.
    let parsed = parse_verdict(&stdout);
    let verdict = match (output.status.code(), parsed) {
        (Some(0), verdict) => verdict,
        (Some(10), Verdict::Sat) => Verdict::Sat,
        (Some(20), Verdict::Unsat) => Verdict::Unsat,
        _ => Verdict::Error,
    };
    Ok(SolveRun {
        verdict,
        stdout,
        stderr,
        timed_out: false,
        memout: false,
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
    reference: Option<&Reference>,
    reference_run: Option<&SolveRun>,
    expected: Option<ExpectedArg>,
    declared_expected: Option<Verdict>,
    explain_output: Option<&str>,
    exit_code: i32,
    limits: CaptureLimits,
) {
    println!("=== ay diagnose: {} ===", file.display());
    println!();
    println!("  ay binary:       {}", ay_identity.path);
    println!("  ay build:        {}", ay_identity.display_build());
    println!(
        "  child limits:    {:.3}s, {} bytes sampled group RSS, {} bytes/stream retained",
        limits.timeout.as_secs_f64(),
        limits.resident_bytes.unwrap_or(0),
        limits.output_bytes,
    );
    println!(
        "  ay verdict:      {}{}",
        ay_run.verdict.as_str(),
        if ay_run.memout {
            " (memory limit)"
        } else if ay_run.timed_out {
            " (timeout)"
        } else {
            ""
        }
    );
    if let Some(exp) = expected {
        println!(
            "  expected:        {} (from --expected or :status)",
            exp.as_str()
        );
    }
    if let Some(reference) = reference {
        if let Some(r) = reference_run {
            println!(
                "  reference ({}): {}{}",
                reference.label,
                r.verdict.as_str(),
                if r.memout {
                    " (memory limit)"
                } else if r.timed_out {
                    " (timeout)"
                } else {
                    ""
                }
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
    if ay_run.memout {
        return "ay exceeded the diagnostic sampled process-group RSS restriction. \
        Its original child group was retired without accepting a verdict; \
        any reference result is reported separately."
            .to_string();
    }
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
    reference: Option<&Reference>,
    reference_run: Option<&SolveRun>,
    expected: Option<ExpectedArg>,
    declared_expected: Option<Verdict>,
    explain_output: Option<&str>,
    exit_code: i32,
    limits: CaptureLimits,
) -> serde_json::Value {
    let ref_json = reference_run.map(|r| {
        serde_json::json!({
            "binary": reference.map(|reference| &reference.program),
            "identity": reference.map(|reference| &reference.label),
            "verdict": r.verdict.as_str(),
            "timed_out": r.timed_out,
            "memout": r.memout,
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
        "restrictions": {
            "timeout_seconds_per_child": limits.timeout.as_secs_f64(),
            "sampled_group_resident_bytes_per_child": limits.resident_bytes,
            "retained_output_bytes_per_stream": limits.output_bytes,
        },
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
            "memout": ay_run.memout,
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

    #[cfg(unix)]
    #[test]
    fn failed_or_non_utf8_output_cannot_supply_a_reference_verdict() {
        use std::os::unix::process::ExitStatusExt as _;
        for (code, stdout, expected) in [
            (1, "sat\n", Verdict::Error),
            (0, "sat\n", Verdict::Sat),
            (10, "s SATISFIABLE\n", Verdict::Sat),
            (20, "s UNSATISFIABLE\n", Verdict::Unsat),
            (10, "unsat\n", Verdict::Error),
            (20, "sat\n", Verdict::Error),
        ] {
            let output = std::process::Output {
                status: std::process::ExitStatus::from_raw(code << 8),
                stdout: stdout.as_bytes().to_vec(),
                stderr: Vec::new(),
            };
            assert_eq!(parse_captured_run(output).unwrap().verdict, expected);
        }
        let malformed = std::process::Output {
            status: std::process::ExitStatus::from_raw(0),
            stdout: vec![0xff, b'\n', b's', b'a', b't', b'\n'],
            stderr: Vec::new(),
        };
        assert!(parse_captured_run(malformed).is_err());
    }

    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    #[test]
    fn diagnostic_capture_drains_output_larger_than_a_pipe_while_the_child_runs() {
        let mut command = Command::new("/usr/bin/seq");
        command.args(["1", "50000"]);
        let run = spawn_and_parse(
            command,
            CaptureLimits {
                timeout: Duration::from_secs(5),
                output_bytes: 1 << 20,
                resident_bytes: Some(256 << 20),
            },
        )
        .unwrap();
        assert!(!run.timed_out);
        assert!(run.stdout.len() > 64 * 1024);
        assert_eq!(run.stdout.lines().count(), 50000);
        assert_eq!(run.stdout.lines().last(), Some("50000"));
        assert_eq!(run.verdict, Verdict::Error);
    }

    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    #[test]
    fn diagnostic_memory_stop_is_unknown_but_spawn_failure_stays_an_error() {
        let limits = CaptureLimits {
            timeout: Duration::from_secs(5),
            output_bytes: DEFAULT_OUTPUT_BYTES,
            resident_bytes: Some(1),
        };
        let mut command = Command::new("/bin/sleep");
        command.arg("10");
        let run = spawn_and_parse(command, limits).unwrap();
        assert_eq!(run.verdict, Verdict::Unknown);
        assert!(run.memout);
        assert!(!run.timed_out);
        assert!(run.stdout.is_empty());
        assert!(
            spawn_and_parse(Command::new("/no-such-ay-diagnostic-executable"), limits,).is_err()
        );
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
            memout: false,
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
            memout: false,
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
            memout: false,
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
            memout: false,
        };
        let reference_run = SolveRun {
            verdict: Verdict::Unsat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
            memout: false,
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
            memout: false,
        };
        let reference_run = SolveRun {
            verdict: Verdict::Unsat,
            stdout: String::new(),
            stderr: String::new(),
            timed_out: false,
            memout: false,
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
