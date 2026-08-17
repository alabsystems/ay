// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

// Dedicated Z3 dynamic-loader/C-ABI boundary.
#![allow(unsafe_code)]
// The per-division scoreboard record is one flat `serde_json::json!` literal
// with ~45 keys; `json_internal!` recurses once per key and overruns the
// default 128-deep limit. Raising it is the fix the compiler itself suggests,
// and it keeps the record flat — nesting the speed statistics to dodge the
// limit would change the published JSON shape for every existing reader.
#![recursion_limit = "256"]

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
mod fetch;
mod inprocess;
mod loader;
mod scoreboard;
mod smtlib_conformance;
mod symbols;
mod z3_abi_500;

use std::path::PathBuf;
use std::process::ExitCode;

const DEFAULT_AY: &str = "target/debug/libay_ffi.dylib";
const DEFAULT_Z3: &str = "/opt/homebrew/lib/python3.14/site-packages/z3/lib/libz3.dylib";
const DEFAULT_DIFF_TIMEOUT_SECS: u64 = 10;
const DEFAULT_BENCH_TIMEOUT_SECS: u64 = 20;
const DEFAULT_BENCH_JSON: &str = "ay-z3-bench.json";
const DEFAULT_BENCH_REPORT: &str = "ay-z3-bench.md";
const DEFAULT_SCOREBOARD_JSON: &str = "ay-z3-scoreboard.json";

fn usage() -> &'static str {
    include_str!("usage.txt")
}

struct Parsed {
    ay: PathBuf,
    ay_cli: Option<PathBuf>,
    z3: PathBuf,
    json: bool,
    timeout: Option<u64>,
    jobs: usize,
    json_out: PathBuf,
    json_out_set: bool,
    report: PathBuf,
    oracle: Option<String>,
    baseline: Option<PathBuf>,
    divisions: Option<Vec<String>>,
    checkpoint: Option<PathBuf>,
    resume: bool,
    sample: Option<usize>,
    seed: u64,
    progress: Option<PathBuf>,
    positionals: Vec<PathBuf>,
}

fn parse(rest: &[String]) -> Result<Parsed, String> {
    let mut ay = PathBuf::from(DEFAULT_AY);
    let mut ay_cli = None;
    let mut z3 = PathBuf::from(DEFAULT_Z3);
    let mut json = false;
    let mut timeout = None;
    let mut jobs = 1usize;
    let mut json_out = PathBuf::from(DEFAULT_BENCH_JSON);
    let mut json_out_set = false;
    let mut report = PathBuf::from(DEFAULT_BENCH_REPORT);
    let mut oracle = None;
    let mut baseline = None;
    let mut divisions = None;
    let mut checkpoint = None;
    let mut resume = false;
    let mut sample = None;
    let mut seed = 0u64;
    let mut progress = None;
    let mut positionals = Vec::new();

    let mut it = rest.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--ay" => ay = PathBuf::from(it.next().ok_or("--ay needs a path")?),
            "--ay-cli" => ay_cli = Some(PathBuf::from(it.next().ok_or("--ay-cli needs a path")?)),
            "--z3" => z3 = PathBuf::from(it.next().ok_or("--z3 needs a path")?),
            "--json" => json = true,
            "--json-out" => {
                json_out = PathBuf::from(it.next().ok_or("--json-out needs a path")?);
                json_out_set = true;
            }
            "--report" => report = PathBuf::from(it.next().ok_or("--report needs a path")?),
            "--baseline" => {
                baseline = Some(PathBuf::from(it.next().ok_or("--baseline needs a path")?));
            }
            "--checkpoint" => {
                checkpoint = Some(PathBuf::from(it.next().ok_or("--checkpoint needs a path")?));
            }
            "--resume" => resume = true,
            "--sample-per-division" => {
                sample = Some(
                    it.next()
                        .ok_or("--sample-per-division needs a count")?
                        .parse()
                        .map_err(|_| "--sample-per-division must be a positive integer")?,
                );
            }
            "--seed" => {
                seed = it
                    .next()
                    .ok_or("--seed needs an integer")?
                    .parse()
                    .map_err(|_| "--seed must be a u64")?;
            }
            "--progress" => {
                progress = Some(PathBuf::from(it.next().ok_or("--progress needs a path")?));
            }
            "--divisions" => {
                let list = it
                    .next()
                    .ok_or("--divisions needs a comma-separated list")?;
                divisions = Some(
                    list.split(',')
                        .map(str::trim)
                        .filter(|s| !s.is_empty())
                        .map(str::to_string)
                        .collect(),
                );
            }
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
        ay_cli,
        z3,
        json,
        timeout,
        jobs,
        json_out,
        json_out_set,
        report,
        oracle,
        baseline,
        divisions,
        checkpoint,
        resume,
        sample,
        seed,
        progress,
        positionals,
    })
}

fn main() -> ExitCode {
    // FIRST statement of main: arm() re-execs this process under a kernel-held
    // memory bound, so anything above it is discarded work, and it sets an env
    // var (sound only while single-threaded). See crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();

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

    // `fetch` has a divergent flag set (--sample/--all/--max-mb/--record/--list)
    // and needs no dylibs, so it parses its own args ahead of the shared parser.
    if cmd == "fetch" {
        return ExitCode::from(fetch::run(rest) as u8);
    }
    if cmd == "z3-abi-probe" {
        return ExitCode::from(z3_abi_500::run_probe_child(rest) as u8);
    }
    if matches!(cmd, "smtlib-conformance" | "smtlib") {
        return ExitCode::from(smtlib_conformance::run(rest) as u8);
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
        "scoreboard" => {
            if parsed.positionals.is_empty() {
                eprintln!("error: `scoreboard` needs a corpus root\n\n{}", usage());
                2
            } else if parsed.positionals.len() > 1 {
                eprintln!(
                    "error: `scoreboard` takes exactly one corpus root (got {})\n\n{}",
                    parsed.positionals.len(),
                    usage()
                );
                2
            } else {
                let json_out = if parsed.json_out_set {
                    parsed.json_out
                } else {
                    PathBuf::from(DEFAULT_SCOREBOARD_JSON)
                };
                scoreboard::run(&scoreboard::ScoreboardConfig {
                    ay: parsed.ay,
                    ay_cli: parsed.ay_cli,
                    z3: parsed.z3,
                    root: parsed
                        .positionals
                        .into_iter()
                        .next()
                        .expect("one positional"),
                    timeout_secs: parsed.timeout.unwrap_or(DEFAULT_BENCH_TIMEOUT_SECS),
                    jobs: parsed.jobs,
                    json_out,
                    baseline: parsed.baseline,
                    divisions: parsed.divisions,
                    checkpoint: parsed.checkpoint,
                    resume: parsed.resume,
                    sample: parsed.sample,
                    seed: parsed.seed,
                    progress: parsed.progress,
                })
            }
        }
        // Hidden child mode used by `bench`: evaluate ONE file in ONE library
        // and print strict wall/RSS headers followed by the raw solver output.
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
