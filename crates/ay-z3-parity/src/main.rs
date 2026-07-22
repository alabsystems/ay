// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay-z3-parity` — a mechanistic compatibility auditor.
//!
//! It measures named compatibility surfaces between the AY SMT solver
//! (`libay_ffi`) and Z3 (`libz3`):
//!
//! * `symbols` audits exported-symbol coverage — whether each `Z3_*` symbol
//!   found live via `nm -gU` is `dlsym`-able in the AY library.
//! * `diff` audits verdict agreement on a supplied SMT-LIB2 corpus by running
//!   it through both libraries via `Z3_eval_smtlib2_string`.
//!
//! Both libraries are `dlopen`ed at runtime; nothing is linked at build time,
//! so the tool works against ANY two Z3-ABI shared objects.

mod behavior;
mod bench;
mod diff;
mod inprocess;
mod loader;
mod symbols;

use std::path::PathBuf;
use std::process::ExitCode;

const DEFAULT_AY: &str = "target/debug/libay_ffi.dylib";
const DEFAULT_Z3: &str = "/opt/homebrew/lib/libz3.dylib";
const DEFAULT_DIFF_TIMEOUT_SECS: u64 = 10;
const DEFAULT_BENCH_TIMEOUT_SECS: u64 = 20;
const DEFAULT_BENCH_JSON: &str = "ay-z3-bench.json";
const DEFAULT_BENCH_REPORT: &str = "ay-z3-bench.md";

fn usage() -> &'static str {
    "\
ay-z3-parity — audit named AY/Z3 compatibility surfaces

USAGE:
  ay-z3-parity symbols [--ay <path>] [--z3 <path>] [--json]
      Audit SYMBOL coverage: nm -gU the libz3 reference set, dlsym each in AY.
      Exit 0 iff no libz3 symbol is missing from AY.

  ay-z3-parity diff <corpus-dir-or-file>... [--ay <path>] [--z3 <path>]
                     [--timeout <secs>] [--json] [--oracle declared]
      Audit verdict agreement: run every .smt2 script through BOTH libs and
      compare verdicts. Unknowns and timeouts are reported; exit non-zero iff
      any sat-vs-unsat DISAGREE.

      With --oracle declared: HERMETIC mode — needs NO z3. Run every .smt2
      through the AY lib ONLY and compare AY's verdict against the file's own
      (set-info :status sat|unsat) ground truth. A sat where the file declares
      unsat (or vice-versa) is a SOUNDNESS FAIL; unknown/timeout is tolerated;
      files without a decided :status are skipped. Exit non-zero iff any WRONG.

  ay-z3-parity classify <corpus-dir-or-file>... [--timeout <secs>] [--json]
      IN-PROCESS differential oracle (extracted from deductive-checks at R1 of the
      two-language design): replay every .smt2 through ay AS A LIBRARY
      (ay_frontend::parse + ay_dpll::Executor, catch_unwind, wall deadline)
      and classify against the file's own (set-info :status sat|unsat)
      ground truth. HERMETIC — needs no z3 and no dylib build. Buckets:
      agree / ay_incomplete (UnknownReason-coded histogram) / timeout /
      parse_error / UNSOUND-DISAGREE. Exit non-zero iff any UNSOUND-DISAGREE.

  ay-z3-parity bench <corpus-root>... [--ay <path>] [--z3 <path>]
                     [--timeout <secs>] [--jobs <n>] [--json]
                     [--json-out <path>] [--report <path>]
      Benchmark CAMPAIGN: run every .smt2 under each corpus root through BOTH
      libs, per division (= <root-name>/<top-level-subdir>). Each (file,
      solver) pair runs in an isolated child process with eval-only wall
      timing and a hard-kill timebox. Emits a per-division table, a JSON
      certificate (--json-out) and a markdown report (--report) with an
      auto-populated \"where z3 wins\" section. Exit non-zero iff any
      sat-vs-unsat DISAGREE.

  ay-z3-parity behavior [--ay <path>] [--z3 <path>] [--json]
      Audit behavior on the honest-divergence surface: drive the same
      minimal inputs through BOTH libs (char↔BV, transitive closure,
      on_clause, Spacer extras, relation getters, polymorphic instantiation,
      HO-seq solving) and compare outcome CLASSES (ok-value / error / inert /
      verdict). Prints the honest residue where libz3 is more capable.
      Exit non-zero iff any pair of produced values/verdicts CONFLICTS.

DEFAULTS:
  --ay        target/debug/libay_ffi.dylib
  --z3        /opt/homebrew/lib/libz3.dylib
  --timeout   10 (diff) / 20 (bench)   per-(file,solver) wall-clock seconds
  --jobs      1    (bench only; parallel worker count)
  --json-out  ay-z3-bench.json (bench only)
  --report    ay-z3-bench.md   (bench only)
"
}

struct Parsed {
    ay: PathBuf,
    z3: PathBuf,
    json: bool,
    timeout: Option<u64>,
    jobs: usize,
    json_out: PathBuf,
    report: PathBuf,
    oracle: Option<String>,
    positionals: Vec<PathBuf>,
}

fn parse(rest: &[String]) -> Result<Parsed, String> {
    let mut ay = PathBuf::from(DEFAULT_AY);
    let mut z3 = PathBuf::from(DEFAULT_Z3);
    let mut json = false;
    let mut timeout = None;
    let mut jobs = 1usize;
    let mut json_out = PathBuf::from(DEFAULT_BENCH_JSON);
    let mut report = PathBuf::from(DEFAULT_BENCH_REPORT);
    let mut oracle = None;
    let mut positionals = Vec::new();

    let mut it = rest.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--ay" => ay = PathBuf::from(it.next().ok_or("--ay needs a path")?),
            "--z3" => z3 = PathBuf::from(it.next().ok_or("--z3 needs a path")?),
            "--json" => json = true,
            "--json-out" => {
                json_out = PathBuf::from(it.next().ok_or("--json-out needs a path")?);
            }
            "--report" => report = PathBuf::from(it.next().ok_or("--report needs a path")?),
            "--oracle" => {
                let val = it.next().ok_or("--oracle needs a value (declared)")?;
                if val != "declared" {
                    return Err(format!("unknown --oracle value: {val} (only `declared`)"));
                }
                oracle = Some(val.clone());
            }
            "--timeout" => {
                timeout = Some(
                    it.next()
                        .ok_or("--timeout needs a number")?
                        .parse()
                        .map_err(|_| "--timeout must be an integer number of seconds")?,
                );
            }
            "--jobs" => {
                jobs = it
                    .next()
                    .ok_or("--jobs needs a number")?
                    .parse()
                    .map_err(|_| "--jobs must be a positive integer")?;
                if jobs == 0 {
                    return Err("--jobs must be at least 1".to_string());
                }
            }
            other if other.starts_with("--") => return Err(format!("unknown flag: {other}")),
            other => positionals.push(PathBuf::from(other)),
        }
    }
    Ok(Parsed {
        ay,
        z3,
        json,
        timeout,
        jobs,
        json_out,
        report,
        oracle,
        positionals,
    })
}

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().collect();
    let (cmd, rest) = match argv.split_first().and_then(|(_, tail)| tail.split_first()) {
        Some((c, r)) => (c.as_str(), r),
        None => {
            print!("{}", usage());
            return ExitCode::from(2);
        }
    };

    if matches!(cmd, "-h" | "--help" | "help") {
        print!("{}", usage());
        return ExitCode::SUCCESS;
    }

    let parsed = match parse(rest) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: {e}\n\n{}", usage());
            return ExitCode::from(2);
        }
    };

    let code = match cmd {
        "symbols" => symbols::run(&parsed.ay, &parsed.z3, parsed.json),
        "behavior" => behavior::run(&parsed.ay, &parsed.z3, parsed.json),
        "diff" => {
            if parsed.positionals.is_empty() {
                eprintln!(
                    "error: `diff` needs at least one corpus dir or .smt2 file\n\n{}",
                    usage()
                );
                2
            } else if parsed.oracle.as_deref() == Some("declared") {
                // Hermetic mode: AY vs each file's own (set-info :status ...).
                diff::run_declared(
                    &parsed.ay,
                    &parsed.positionals,
                    parsed.timeout.unwrap_or(DEFAULT_DIFF_TIMEOUT_SECS),
                    parsed.json,
                )
            } else {
                diff::run(
                    &parsed.ay,
                    &parsed.z3,
                    &parsed.positionals,
                    parsed.timeout.unwrap_or(DEFAULT_DIFF_TIMEOUT_SECS),
                    parsed.json,
                )
            }
        }
        "classify" => {
            if parsed.positionals.is_empty() {
                eprintln!(
                    "error: `classify` needs at least one corpus dir or .smt2 file\n\n{}",
                    usage()
                );
                2
            } else {
                inprocess::run_classify(
                    &parsed.positionals,
                    parsed.timeout.unwrap_or(DEFAULT_DIFF_TIMEOUT_SECS),
                    parsed.json,
                )
            }
        }
        "bench" => {
            if parsed.positionals.is_empty() {
                eprintln!(
                    "error: `bench` needs at least one corpus root\n\n{}",
                    usage()
                );
                2
            } else {
                bench::run(&bench::BenchConfig {
                    ay: parsed.ay,
                    z3: parsed.z3,
                    roots: parsed.positionals,
                    timeout_secs: parsed.timeout.unwrap_or(DEFAULT_BENCH_TIMEOUT_SECS),
                    jobs: parsed.jobs,
                    json_stdout: parsed.json,
                    json_out: parsed.json_out,
                    report_out: parsed.report,
                })
            }
        }
        // Hidden child mode used by `bench`: evaluate ONE file in ONE library
        // and print `AYZ3_WALL_NS <ns>` followed by the raw solver output.
        "bench-one" => {
            if parsed.positionals.len() != 2 {
                eprintln!("error: `bench-one` needs exactly <lib> <file>");
                2
            } else {
                bench::run_child(&parsed.positionals[0], &parsed.positionals[1])
            }
        }
        other => {
            eprintln!("error: unknown subcommand `{other}`\n\n{}", usage());
            2
        }
    };

    ExitCode::from(code as u8)
}
