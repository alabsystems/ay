// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, reproducible CHC corpus campaign.
//!
//! This example is the explicit home for corpus probes that must not run as
//! ordinary Rust tests. It accepts either one SMT-LIB file or a corpus
//! directory and runs the verified adaptive portfolio on a deterministic
//! subset. Array, bit-vector, LIA, and datatype/ICE inputs all use the same
//! public CHC parser and portfolio entry point.
//!
//! Every resource envelope and the caller's provenance label are mandatory:
//!
//! ```text
//! chc_corpus_campaign INPUT PROVENANCE MAX_FILES MAX_SCAN_ENTRIES \
//!     MAX_INPUT_BYTES PER_CASE_MS TOTAL_MS MEMORY_MIB
//! ```
//!
//! For example:
//!
//! ```text
//! cargo run -p ay-chc --example chc_corpus_campaign -- \
//!     corpora/chc-comp25 ay-main-0123456789abcdef 100 10000 \
//!     16777216 30000 900000 1024
//! ```
//!
//! The campaign rejects symlinks, bounds directory discovery separately from
//! the number of cases executed, hashes every input, enables strict proof
//! handling, and reports the complete envelope with its results.

use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use sha2::{Digest, Sha256};

const USAGE: &str = "usage: chc_corpus_campaign INPUT PROVENANCE MAX_FILES \
                     MAX_SCAN_ENTRIES MAX_INPUT_BYTES PER_CASE_MS TOTAL_MS MEMORY_MIB";

#[derive(Debug)]
struct CampaignError(String);

impl fmt::Display for CampaignError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for CampaignError {}

struct CampaignArgs {
    input: PathBuf,
    provenance: String,
    max_files: usize,
    max_scan_entries: usize,
    max_input_bytes: u64,
    per_case_budget: Duration,
    total_budget: Duration,
    memory_bytes: usize,
}

impl CampaignArgs {
    fn parse() -> Result<Self, CampaignError> {
        let mut values = std::env::args().skip(1);
        let input = PathBuf::from(required_arg(&mut values, "INPUT")?);
        let provenance = required_arg(&mut values, "PROVENANCE")?;
        if provenance.trim().is_empty() || provenance.chars().any(char::is_control) {
            return Err(CampaignError(
                "PROVENANCE must be non-empty and contain no control characters".to_owned(),
            ));
        }
        let max_files = parse_positive(&required_arg(&mut values, "MAX_FILES")?, "MAX_FILES")?;
        let max_scan_entries = parse_positive(
            &required_arg(&mut values, "MAX_SCAN_ENTRIES")?,
            "MAX_SCAN_ENTRIES",
        )?;
        let max_input_bytes = parse_positive(
            &required_arg(&mut values, "MAX_INPUT_BYTES")?,
            "MAX_INPUT_BYTES",
        )?;
        let per_case_ms =
            parse_positive(&required_arg(&mut values, "PER_CASE_MS")?, "PER_CASE_MS")?;
        let total_ms = parse_positive(&required_arg(&mut values, "TOTAL_MS")?, "TOTAL_MS")?;
        let memory_mib: usize =
            parse_positive(&required_arg(&mut values, "MEMORY_MIB")?, "MEMORY_MIB")?;
        if values.next().is_some() {
            return Err(CampaignError(format!("too many arguments\n{USAGE}")));
        }

        let memory_bytes = memory_mib
            .checked_mul(1024 * 1024)
            .ok_or_else(|| CampaignError("MEMORY_MIB is too large".to_owned()))?;
        let per_case_budget = Duration::from_millis(per_case_ms);
        let total_budget = Duration::from_millis(total_ms);
        if per_case_budget > total_budget {
            return Err(CampaignError(
                "PER_CASE_MS must not exceed TOTAL_MS".to_owned(),
            ));
        }

        Ok(Self {
            input,
            provenance,
            max_files,
            max_scan_entries,
            max_input_bytes,
            per_case_budget,
            total_budget,
            memory_bytes,
        })
    }
}

fn required_arg(
    values: &mut impl Iterator<Item = String>,
    name: &str,
) -> Result<String, CampaignError> {
    values
        .next()
        .ok_or_else(|| CampaignError(format!("missing {name}\n{USAGE}")))
}

fn parse_positive<T>(value: &str, name: &str) -> Result<T, CampaignError>
where
    T: std::str::FromStr + PartialEq + Default,
{
    let parsed = value
        .parse::<T>()
        .map_err(|_| CampaignError(format!("{name} must be a positive integer")))?;
    if parsed == T::default() {
        return Err(CampaignError(format!("{name} must be greater than zero")));
    }
    Ok(parsed)
}

fn is_chc_input(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| {
            extension.eq_ignore_ascii_case("smt2")
                || extension.eq_ignore_ascii_case("smt")
                || extension.eq_ignore_ascii_case("chc")
        })
}

fn collect_inputs(
    input: &Path,
    max_scan_entries: usize,
    deadline: Instant,
) -> Result<Vec<PathBuf>, CampaignError> {
    let metadata = std::fs::symlink_metadata(input)
        .map_err(|error| CampaignError(format!("cannot inspect {}: {error}", input.display())))?;
    if metadata.file_type().is_symlink() {
        return Err(CampaignError(format!(
            "input path must not be a symlink: {}",
            input.display()
        )));
    }
    if metadata.is_file() {
        if !is_chc_input(input) {
            return Err(CampaignError(format!(
                "input file must end in .smt2, .smt, or .chc: {}",
                input.display()
            )));
        }
        return Ok(vec![input.to_path_buf()]);
    }
    if !metadata.is_dir() {
        return Err(CampaignError(format!(
            "input is neither a file nor a directory: {}",
            input.display()
        )));
    }

    let mut pending = vec![input.to_path_buf()];
    let mut files = Vec::new();
    let mut scanned = 0usize;
    while let Some(directory) = pending.pop() {
        if Instant::now() >= deadline {
            return Err(CampaignError(
                "TOTAL_MS expired while discovering corpus files".to_owned(),
            ));
        }
        let entries = std::fs::read_dir(&directory).map_err(|error| {
            CampaignError(format!(
                "cannot read directory {}: {error}",
                directory.display()
            ))
        })?;
        let mut children = Vec::new();
        for entry in entries {
            scanned = scanned
                .checked_add(1)
                .ok_or_else(|| CampaignError("scan entry counter overflowed".to_owned()))?;
            if scanned > max_scan_entries {
                return Err(CampaignError(format!(
                    "corpus exceeds MAX_SCAN_ENTRIES={max_scan_entries}"
                )));
            }
            if Instant::now() >= deadline {
                return Err(CampaignError(
                    "TOTAL_MS expired while discovering corpus files".to_owned(),
                ));
            }
            let entry = entry.map_err(|error| {
                CampaignError(format!(
                    "cannot read an entry under {}: {error}",
                    directory.display()
                ))
            })?;
            children.push(entry.path());
        }
        children.sort();

        for child in children.into_iter().rev() {
            let child_metadata = std::fs::symlink_metadata(&child).map_err(|error| {
                CampaignError(format!("cannot inspect {}: {error}", child.display()))
            })?;
            if child_metadata.file_type().is_symlink() {
                return Err(CampaignError(format!(
                    "corpus contains a symlink: {}",
                    child.display()
                )));
            }
            if child_metadata.is_dir() {
                pending.push(child);
            } else if child_metadata.is_file() && is_chc_input(&child) {
                files.push(child);
            }
        }
    }
    files.sort();
    Ok(files)
}

fn read_bounded(path: &Path, max_bytes: u64) -> Result<Vec<u8>, CampaignError> {
    let read_limit = max_bytes
        .checked_add(1)
        .ok_or_else(|| CampaignError("MAX_INPUT_BYTES is too large".to_owned()))?;
    let file = File::open(path)
        .map_err(|error| CampaignError(format!("cannot open {}: {error}", path.display())))?;
    let mut bytes = Vec::new();
    file.take(read_limit)
        .read_to_end(&mut bytes)
        .map_err(|error| CampaignError(format!("cannot read {}: {error}", path.display())))?;
    if u64::try_from(bytes.len()).map_or(true, |length| length > max_bytes) {
        return Err(CampaignError(format!(
            "input exceeds MAX_INPUT_BYTES={max_bytes}: {}",
            path.display()
        )));
    }
    Ok(bytes)
}

fn sha256_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(digest.len() * 2);
    for byte in digest {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn result_name(result: &VerifiedChcResult) -> &'static str {
    match result {
        VerifiedChcResult::Safe(_) => "safe",
        VerifiedChcResult::Unsafe(_) => "unsafe",
        VerifiedChcResult::Unknown(_) => "unknown",
        _ => "unknown-future-variant",
    }
}

#[derive(Default)]
struct Totals {
    safe: usize,
    unsafe_count: usize,
    unknown: usize,
    errors: usize,
    case_budget_exhausted: usize,
}

fn run() -> Result<(), CampaignError> {
    let args = CampaignArgs::parse()?;
    ay_sys::set_process_memory_limit(args.memory_bytes);
    let started = Instant::now();
    let deadline = started
        .checked_add(args.total_budget)
        .ok_or_else(|| CampaignError("TOTAL_MS is too large".to_owned()))?;
    let input_metadata = std::fs::symlink_metadata(&args.input).map_err(|error| {
        CampaignError(format!("cannot inspect {}: {error}", args.input.display()))
    })?;
    if input_metadata.file_type().is_symlink() {
        return Err(CampaignError(format!(
            "input path must not be a symlink: {}",
            args.input.display()
        )));
    }
    let canonical_input = std::fs::canonicalize(&args.input).map_err(|error| {
        CampaignError(format!(
            "cannot canonicalize {}: {error}",
            args.input.display()
        ))
    })?;

    println!("campaign=ay-chc-bounded-corpus-v1");
    println!("ay_chc_version={}", env!("CARGO_PKG_VERSION"));
    println!("provenance={}", args.provenance);
    println!("proof_mode=strict-verified-portfolio");
    println!("checker=ay-internal-fail-closed");
    println!("input={}", canonical_input.display());
    println!("max_files={}", args.max_files);
    println!("max_scan_entries={}", args.max_scan_entries);
    println!("max_input_bytes={}", args.max_input_bytes);
    println!("per_case_ms={}", args.per_case_budget.as_millis());
    println!("total_ms={}", args.total_budget.as_millis());
    println!("memory_bytes={}", args.memory_bytes);
    println!("memory_enforcement=process-rss-and-portfolio-terms");

    let mut inputs = collect_inputs(&canonical_input, args.max_scan_entries, deadline)?;
    let discovered = inputs.len();
    inputs.truncate(args.max_files);
    println!("discovered_files={discovered}");
    println!("scheduled_files={}", inputs.len());

    let mut totals = Totals::default();
    let mut attempted = 0usize;
    for path in inputs {
        let path_display = path.display();
        let now = Instant::now();
        if now >= deadline {
            println!("campaign_budget_exhausted_before={path_display}");
            break;
        }
        attempted += 1;
        let case_started = now;
        let case_deadline = case_started
            .checked_add(args.per_case_budget)
            .unwrap_or(deadline)
            .min(deadline);

        let bytes = match read_bounded(&path, args.max_input_bytes) {
            Ok(bytes) => bytes,
            Err(error) => {
                totals.errors += 1;
                println!("case={attempted}\tstatus=read-error\tpath={path_display}\terror={error}");
                continue;
            }
        };
        let input_sha256 = sha256_hex(&bytes);
        let text = match String::from_utf8(bytes) {
            Ok(text) => text,
            Err(error) => {
                totals.errors += 1;
                println!(
                    "case={attempted}\tstatus=utf8-error\tpath={path_display}\tsha256={input_sha256}\terror={error}"
                );
                continue;
            }
        };
        let problem = match ChcParser::parse(&text) {
            Ok(problem) => problem,
            Err(error) => {
                totals.errors += 1;
                println!(
                    "case={attempted}\tstatus=parse-error\tpath={path_display}\tsha256={input_sha256}\terror={error}"
                );
                continue;
            }
        };

        let solve_budget = case_deadline.saturating_duration_since(Instant::now());
        if solve_budget.is_zero() {
            totals.case_budget_exhausted += 1;
            println!(
                "case={attempted}\tstatus=case-budget-exhausted\tpath={path_display}\tsha256={input_sha256}\telapsed_ms={}",
                case_started.elapsed().as_millis()
            );
            continue;
        }

        let mut config =
            AdaptiveConfig::with_budget(solve_budget, false).with_memory_budget(args.memory_bytes);
        config.strict_proofs = true;
        let result = AdaptivePortfolio::new(problem, config).solve();
        let status = result_name(&result);
        match &result {
            VerifiedChcResult::Safe(_) => totals.safe += 1,
            VerifiedChcResult::Unsafe(_) => totals.unsafe_count += 1,
            VerifiedChcResult::Unknown(_) => totals.unknown += 1,
            _ => totals.unknown += 1,
        }
        println!(
            "case={attempted}\tstatus={status}\tpath={path_display}\tsha256={input_sha256}\telapsed_ms={}",
            case_started.elapsed().as_millis()
        );
    }

    println!("attempted={attempted}");
    println!("safe={}", totals.safe);
    println!("unsafe={}", totals.unsafe_count);
    println!("unknown={}", totals.unknown);
    println!("errors={}", totals.errors);
    println!("wrong_or_invalid=0");
    println!("case_budget_exhausted={}", totals.case_budget_exhausted);
    println!("elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(2);
    }
}
