// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded replay of one captured QF_LIA proof-interpolation script.
//!
//! This is the explicit replacement for environment-driven replay branches in
//! ordinary tests. All paths and resource envelopes are command-line inputs:
//!
//! ```text
//! proof_interpolant_replay INPUT PROVENANCE A_COUNT MAX_FILES \
//!     MAX_INPUT_BYTES PER_CASE_MS TOTAL_MS MEMORY_MIB
//! ```
//!
//! `MAX_FILES` must be `1`; spelling the fixed cap in the invocation keeps
//! recorded campaign envelopes self-contained.

use std::collections::{BTreeSet, HashSet};
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use ay_dpll::api::{Logic, Solver, Term, TermKind};
use sha2::{Digest, Sha256};

const USAGE: &str = "usage: proof_interpolant_replay INPUT PROVENANCE A_COUNT MAX_FILES \
                     MAX_INPUT_BYTES PER_CASE_MS TOTAL_MS MEMORY_MIB";

#[derive(Debug)]
struct ReplayError(String);

impl fmt::Display for ReplayError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for ReplayError {}

struct Args {
    input: PathBuf,
    provenance: String,
    a_count: usize,
    max_input_bytes: u64,
    per_case: Duration,
    total: Duration,
    memory_bytes: usize,
}

impl Args {
    fn parse() -> Result<Self, ReplayError> {
        let mut values = std::env::args().skip(1);
        let input = PathBuf::from(required(&mut values, "INPUT")?);
        let provenance = required(&mut values, "PROVENANCE")?;
        if provenance.trim().is_empty() || provenance.chars().any(char::is_control) {
            return Err(ReplayError(
                "PROVENANCE must be non-empty and contain no control characters".to_string(),
            ));
        }
        let a_count = positive(&required(&mut values, "A_COUNT")?, "A_COUNT")?;
        let max_files: usize = positive(&required(&mut values, "MAX_FILES")?, "MAX_FILES")?;
        if max_files != 1 {
            return Err(ReplayError(
                "MAX_FILES must be 1 for a single-script replay".to_string(),
            ));
        }
        let max_input_bytes = positive(
            &required(&mut values, "MAX_INPUT_BYTES")?,
            "MAX_INPUT_BYTES",
        )?;
        let per_case_ms = positive(&required(&mut values, "PER_CASE_MS")?, "PER_CASE_MS")?;
        let total_ms = positive(&required(&mut values, "TOTAL_MS")?, "TOTAL_MS")?;
        let memory_mib: usize = positive(&required(&mut values, "MEMORY_MIB")?, "MEMORY_MIB")?;
        if values.next().is_some() {
            return Err(ReplayError(format!("too many arguments\n{USAGE}")));
        }
        let per_case = Duration::from_millis(per_case_ms);
        let total = Duration::from_millis(total_ms);
        if per_case > total {
            return Err(ReplayError(
                "PER_CASE_MS must not exceed TOTAL_MS".to_string(),
            ));
        }
        let memory_bytes = memory_mib
            .checked_mul(1024 * 1024)
            .ok_or_else(|| ReplayError("MEMORY_MIB is too large".to_string()))?;
        Ok(Self {
            input,
            provenance,
            a_count,
            max_input_bytes,
            per_case,
            total,
            memory_bytes,
        })
    }
}

fn required(values: &mut impl Iterator<Item = String>, name: &str) -> Result<String, ReplayError> {
    values
        .next()
        .ok_or_else(|| ReplayError(format!("missing {name}\n{USAGE}")))
}

fn positive<T>(value: &str, name: &str) -> Result<T, ReplayError>
where
    T: std::str::FromStr + PartialEq + Default,
{
    let parsed = value
        .parse::<T>()
        .map_err(|_| ReplayError(format!("{name} must be a positive integer")))?;
    if parsed == T::default() {
        return Err(ReplayError(format!("{name} must be greater than zero")));
    }
    Ok(parsed)
}

fn read_regular_file(path: &Path, max_bytes: u64) -> Result<Vec<u8>, ReplayError> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| ReplayError(format!("cannot inspect {}: {error}", path.display())))?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(ReplayError(format!(
            "INPUT must be one regular, non-symlink file: {}",
            path.display()
        )));
    }
    let limit = max_bytes
        .checked_add(1)
        .ok_or_else(|| ReplayError("MAX_INPUT_BYTES is too large".to_string()))?;
    let file = File::open(path)
        .map_err(|error| ReplayError(format!("cannot open {}: {error}", path.display())))?;
    let mut bytes = Vec::new();
    file.take(limit)
        .read_to_end(&mut bytes)
        .map_err(|error| ReplayError(format!("cannot read {}: {error}", path.display())))?;
    if u64::try_from(bytes.len()).map_or(true, |length| length > max_bytes) {
        return Err(ReplayError(format!(
            "INPUT exceeds MAX_INPUT_BYTES={max_bytes}"
        )));
    }
    Ok(bytes)
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use std::fmt::Write as _;
        write!(encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    encoded
}

fn remaining(deadline: Instant, phase: &str) -> Result<Duration, ReplayError> {
    let budget = deadline.saturating_duration_since(Instant::now());
    if budget.is_zero() {
        return Err(ReplayError(format!("budget expired before {phase}")));
    }
    Ok(budget)
}

fn reset_assertions(solver: &mut Solver, phase: &str) -> Result<(), ReplayError> {
    solver
        .try_reset_assertions()
        .map_err(|error| ReplayError(format!("{phase}: reset assertions: {error}")))
}

fn assert_terms(solver: &mut Solver, terms: &[Term], phase: &str) -> Result<(), ReplayError> {
    for &term in terms {
        solver
            .try_assert_term(term)
            .map_err(|error| ReplayError(format!("{phase}: assert term: {error}")))?;
    }
    Ok(())
}

fn variable_names(solver: &Solver, roots: &[Term]) -> BTreeSet<String> {
    let mut pending = roots.to_vec();
    let mut seen = HashSet::new();
    let mut variables = BTreeSet::new();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::Var { name } = solver.term_kind(term) {
            variables.insert(name);
        }
        pending.extend(solver.term_children(term));
    }
    variables
}

fn validate_craig(
    solver: &mut Solver,
    a_terms: &[Term],
    b_terms: &[Term],
    interpolant: Term,
    deadline: Instant,
) -> Result<(), ReplayError> {
    let a_variables = variable_names(solver, a_terms);
    let b_variables = variable_names(solver, b_terms);
    let shared_variables: BTreeSet<_> = a_variables.intersection(&b_variables).cloned().collect();
    let interpolant_variables = variable_names(solver, &[interpolant]);
    let unexpected_variables: Vec<_> = interpolant_variables
        .difference(&shared_variables)
        .cloned()
        .collect();
    if !unexpected_variables.is_empty() {
        return Err(ReplayError(format!(
            "interpolant contains non-shared variables: {unexpected_variables:?}"
        )));
    }

    reset_assertions(solver, "A-implies-I check")?;
    assert_terms(solver, a_terms, "A-implies-I check")?;
    let not_interpolant = solver
        .try_not(interpolant)
        .map_err(|error| ReplayError(format!("A-implies-I check: negate interpolant: {error}")))?;
    solver
        .try_assert_term(not_interpolant)
        .map_err(|error| ReplayError(format!("A-implies-I check: assert negation: {error}")))?;
    solver.set_timeout(Some(remaining(deadline, "A-implies-I check")?));
    let left = solver.check_sat();
    if !left.is_unsat() {
        return Err(ReplayError(format!(
            "interpolant failed A => I validation: {left:?}"
        )));
    }

    reset_assertions(solver, "I-and-B check")?;
    solver
        .try_assert_term(interpolant)
        .map_err(|error| ReplayError(format!("I-and-B check: assert interpolant: {error}")))?;
    assert_terms(solver, b_terms, "I-and-B check")?;
    solver.set_timeout(Some(remaining(deadline, "I-and-B check")?));
    let right = solver.check_sat();
    if !right.is_unsat() {
        return Err(ReplayError(format!(
            "interpolant failed I /\\ B unsat validation: {right:?}"
        )));
    }
    Ok(())
}

fn run() -> Result<(), ReplayError> {
    let args = Args::parse()?;
    ay_sys::set_process_memory_limit(args.memory_bytes);
    let started = Instant::now();
    let total_deadline = started
        .checked_add(args.total)
        .ok_or_else(|| ReplayError("TOTAL_MS is too large".to_string()))?;
    let input_metadata = std::fs::symlink_metadata(&args.input).map_err(|error| {
        ReplayError(format!("cannot inspect {}: {error}", args.input.display()))
    })?;
    if input_metadata.file_type().is_symlink() || !input_metadata.is_file() {
        return Err(ReplayError(format!(
            "INPUT must be one regular, non-symlink file: {}",
            args.input.display()
        )));
    }
    let canonical_input = std::fs::canonicalize(&args.input).map_err(|error| {
        ReplayError(format!(
            "cannot canonicalize {}: {error}",
            args.input.display()
        ))
    })?;
    let bytes = read_regular_file(&canonical_input, args.max_input_bytes)?;
    let input_sha256 = sha256_hex(&bytes);
    let script = String::from_utf8(bytes)
        .map_err(|error| ReplayError(format!("INPUT is not UTF-8: {error}")))?;

    println!("campaign=ay-proof-interpolant-replay-v1");
    println!("ay_chc_version={}", env!("CARGO_PKG_VERSION"));
    println!("provenance={}", args.provenance);
    println!("proof_mode=ay-dpll-proof-producing");
    println!("checker=two-sided-ay-dpll-craig-validation");
    println!("input={}", canonical_input.display());
    println!("input_sha256={input_sha256}");
    println!("a_count={}", args.a_count);
    println!("max_files=1");
    println!("max_input_bytes={}", args.max_input_bytes);
    println!("per_case_ms={}", args.per_case.as_millis());
    println!("total_ms={}", args.total.as_millis());
    println!("memory_bytes={}", args.memory_bytes);
    println!("memory_enforcement=process-rss-and-solver-terms");

    let case_deadline = started
        .checked_add(args.per_case)
        .ok_or_else(|| ReplayError("PER_CASE_MS is too large".to_string()))?
        .min(total_deadline);
    let mut solver =
        Solver::try_new(Logic::QfLia).map_err(|error| ReplayError(format!("solver: {error}")))?;
    solver.set_produce_proofs(true);
    solver.set_option(":ay-proof-no-varsubst", "true");
    solver.set_memory_limit(Some(args.memory_bytes));
    solver.set_term_memory_limit(Some(args.memory_bytes));
    let assertions = solver
        .parse_smtlib2(&script)
        .map_err(|error| ReplayError(format!("parse replay script: {error}")))?;
    if args.a_count >= assertions.len() {
        return Err(ReplayError(format!(
            "A_COUNT={} must leave a non-empty B group (assertions={})",
            args.a_count,
            assertions.len()
        )));
    }
    solver.set_timeout(Some(remaining(case_deadline, "the proof solve")?));
    let (a_terms, b_terms) = assertions.split_at(args.a_count);
    let a_terms = a_terms.to_vec();
    let b_terms = b_terms.to_vec();
    let result = solver.check_sat();
    if !result.is_unsat() {
        return Err(ReplayError(format!(
            "replay conjunction must be unsatisfiable, got {result:?}"
        )));
    }

    match solver.get_interpolant(&a_terms, &b_terms) {
        Some(interpolant) => {
            let interpolant_text = solver.format_term(interpolant.interpolant());
            validate_craig(
                &mut solver,
                &a_terms,
                &b_terms,
                interpolant.interpolant(),
                case_deadline,
            )?;
            println!("status=interpolant");
            println!("strength={}", interpolant.strength());
            println!("craig_validation=passed");
            println!("interpolant={interpolant_text}");
        }
        None => println!("status=proof-extraction-fallback"),
    }
    if Instant::now() > case_deadline {
        return Err(ReplayError(
            "budget expired during proof extraction or validation".to_string(),
        ));
    }
    println!("wrong_or_invalid=0");
    println!("elapsed_ms={}", started.elapsed().as_millis());
    println!("total_budget_respected=true");
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(2);
    }
}
