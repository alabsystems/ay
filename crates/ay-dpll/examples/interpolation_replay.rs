// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded replay tool for captured QF_LIA interpolation queries.
//!
//! The first `--a-count` assertions form partition A; the remaining assertions
//! form partition B.  The tool runs every production interpolation strength,
//! prints each interpolant, and independently checks all three Craig
//! conditions: `A /\ not(I)` and `I /\ B` are both UNSAT, and the interpolant
//! mentions no symbol exclusive to either partition.
//!
//! ```text
//! cargo run -p ay-dpll --release --example interpolation_replay -- \
//!   --file capture.smt2 --a-count 40
//! ```
//!
//! Each solve has a 30-second default timeout, input is capped at 16 MiB, and
//! solver/term memory have fixed 2 GiB/512 MiB ceilings.  The timeout and input
//! cap can be adjusted explicitly without relying on process environment.

use std::collections::HashSet;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::Duration;

use ay_dpll::api::{
    InterpolantStrength, Logic, Solver, SolverConfig, SolverError, Term, VerifiedSolveResult,
};
use ay_frontend::Command;

const DEFAULT_TIMEOUT_SECONDS: u64 = 30;
const DEFAULT_MAX_INPUT_BYTES: usize = 16 * 1024 * 1024;
const SOLVER_MEMORY_LIMIT_BYTES: usize = 2 * 1024 * 1024 * 1024;
const TERM_MEMORY_LIMIT_BYTES: usize = 512 * 1024 * 1024;

struct Args {
    file: PathBuf,
    a_count: usize,
    timeout_seconds: u64,
    max_input_bytes: usize,
}

struct Candidate {
    name: &'static str,
    term: Term,
    text: String,
    shared_symbols_only: bool,
}

fn usage() -> &'static str {
    "usage: interpolation_replay --file FILE --a-count N \
     [--timeout-seconds N] [--max-input-bytes N]"
}

fn next_value(args: &mut impl Iterator<Item = String>, option: &str) -> Result<String, String> {
    args.next()
        .ok_or_else(|| format!("missing value for {option}\n{}", usage()))
}

fn parse_args() -> Result<Option<Args>, String> {
    let mut file = None;
    let mut a_count = None;
    let mut timeout_seconds = DEFAULT_TIMEOUT_SECONDS;
    let mut max_input_bytes = DEFAULT_MAX_INPUT_BYTES;
    let mut args = std::env::args().skip(1);

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--file" => file = Some(PathBuf::from(next_value(&mut args, "--file")?)),
            "--a-count" => {
                let raw = next_value(&mut args, "--a-count")?;
                a_count = Some(
                    raw.parse()
                        .map_err(|_| format!("invalid --a-count value `{raw}`"))?,
                );
            }
            "--timeout-seconds" => {
                let raw = next_value(&mut args, "--timeout-seconds")?;
                timeout_seconds = raw
                    .parse()
                    .map_err(|_| format!("invalid --timeout-seconds value `{raw}`"))?;
            }
            "--max-input-bytes" => {
                let raw = next_value(&mut args, "--max-input-bytes")?;
                max_input_bytes = raw
                    .parse()
                    .map_err(|_| format!("invalid --max-input-bytes value `{raw}`"))?;
            }
            "-h" | "--help" => {
                println!("{}", usage());
                return Ok(None);
            }
            _ => return Err(format!("unknown argument `{arg}`\n{}", usage())),
        }
    }

    if timeout_seconds == 0 {
        return Err("--timeout-seconds must be positive".to_string());
    }
    if max_input_bytes == 0 {
        return Err("--max-input-bytes must be positive".to_string());
    }

    Ok(Some(Args {
        file: file.ok_or_else(|| format!("--file is required\n{}", usage()))?,
        a_count: a_count.ok_or_else(|| format!("--a-count is required\n{}", usage()))?,
        timeout_seconds,
        max_input_bytes,
    }))
}

fn read_bounded(path: &Path, max_bytes: usize) -> Result<String, Box<dyn std::error::Error>> {
    let read_limit = max_bytes
        .checked_add(1)
        .ok_or("--max-input-bytes is too large")?;
    let read_limit = u64::try_from(read_limit).map_err(|_| "--max-input-bytes is too large")?;
    let mut bytes = Vec::new();
    File::open(path)?.take(read_limit).read_to_end(&mut bytes)?;
    if bytes.len() > max_bytes {
        return Err(format!(
            "{} exceeds the configured {}-byte input limit",
            path.display(),
            max_bytes
        )
        .into());
    }
    Ok(String::from_utf8(bytes)?)
}

fn check_conjunction(
    solver: &mut Solver,
    partition: &[Term],
    extra: Term,
) -> Result<VerifiedSolveResult, SolverError> {
    solver.try_reset_assertions()?;
    for &term in partition {
        solver.try_assert_term(term)?;
    }
    solver.try_assert_term(extra)?;
    Ok(solver.check_sat())
}

fn declared_value_names(source: &str) -> Result<HashSet<String>, Box<dyn std::error::Error>> {
    let mut names = HashSet::new();
    for command in ay_frontend::parse(source)? {
        match command {
            Command::DeclareFun(name, ..)
            | Command::DeclareConst(name, ..)
            | Command::DeclareVar(name, ..)
            | Command::DeclareRel(name, ..)
            | Command::DefineFun(name, ..)
            | Command::DefineFunRec(name, ..) => {
                names.insert(name);
            }
            _ => {}
        }
    }
    Ok(names)
}

fn partition_exclusive_names(
    solver: &Solver,
    a_terms: &[Term],
    b_terms: &[Term],
    declared_names: HashSet<String>,
) -> HashSet<String> {
    declared_names
        .into_iter()
        .filter(|name| {
            let singleton = HashSet::from([name.clone()]);
            solver.terms_mention_names(a_terms, &singleton)
                != solver.terms_mention_names(b_terms, &singleton)
        })
        .collect()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let Some(args) = parse_args()? else {
        return Ok(());
    };
    let source = read_bounded(&args.file, args.max_input_bytes)?;
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(args.timeout_seconds))
        .with_memory_limit(SOLVER_MEMORY_LIMIT_BYTES)
        .with_term_memory_limit(TERM_MEMORY_LIMIT_BYTES);
    let mut solver = Solver::try_new_with_config(Logic::QfLia, config)?;
    let assertions = solver.parse_smtlib2(&source)?;
    // Reassert the proof settings after parsing so capture-local options
    // cannot disable the production interpolation path.
    solver.set_produce_proofs(true);
    solver.set_option(":ay-proof-no-varsubst", "true");
    if args.a_count == 0 || args.a_count >= assertions.len() {
        return Err(format!(
            "--a-count must split {} assertions into nonempty A and B partitions",
            assertions.len()
        )
        .into());
    }
    let a_terms = assertions[..args.a_count].to_vec();
    let b_terms = assertions[args.a_count..].to_vec();
    let exclusive_names =
        partition_exclusive_names(&solver, &a_terms, &b_terms, declared_value_names(&source)?);

    let result = solver.check_sat();
    if !result.is_unsat() {
        return Err(format!("interpolation input must be UNSAT, got {result:?}").into());
    }

    let mut candidates = Vec::new();
    let mut failures = Vec::new();
    for (name, strength) in [
        ("weakest", InterpolantStrength::Weakest),
        ("default", InterpolantStrength::Default),
        ("strongest", InterpolantStrength::Strongest),
    ] {
        match solver.get_interpolant_with_strength(&a_terms, &b_terms, strength) {
            Some(interpolant) => {
                let term = interpolant.interpolant();
                candidates.push(Candidate {
                    name,
                    term,
                    text: solver.format_term(term),
                    shared_symbols_only: !solver.terms_mention_names(&[term], &exclusive_names),
                });
            }
            None => failures.push(format!("{name}: interpolation returned no candidate")),
        }
    }

    // Verification solves do not need to record new proofs.
    solver.set_produce_proofs(false);
    for candidate in candidates {
        let not_interpolant = solver.try_not(candidate.term)?;
        let a_result = check_conjunction(&mut solver, &a_terms, not_interpolant)?;
        let b_result = check_conjunction(&mut solver, &b_terms, candidate.term)?;
        let verified = a_result.is_unsat() && b_result.is_unsat() && candidate.shared_symbols_only;
        println!(
            "{}: A&!I={a_result:?} I&B={b_result:?} shared-symbols={} verified={verified}",
            candidate.name, candidate.shared_symbols_only
        );
        println!("{}: I = {}", candidate.name, candidate.text);
        if !verified {
            failures.push(format!(
                "{}: Craig verification failed (A&!I={a_result:?}, I&B={b_result:?}, \
                 shared-symbols={})",
                candidate.name, candidate.shared_symbols_only
            ));
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("; ").into())
    }
}
