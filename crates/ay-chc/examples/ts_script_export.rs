// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded export of incremental transition-system BMC script segments.
//!
//! ```text
//! ts_script_export INPUT OUTPUT_DIR PROVENANCE DEPTH MAX_FILES \
//!     MAX_INPUT_BYTES MAX_SEGMENTS MAX_OUTPUT_BYTES PER_CASE_MS TOTAL_MS
//! ```
//!
//! The output directory must already exist and be empty of the deterministic
//! `segment_N.smt2` names. Files are created without overwrite.

use std::error::Error;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use ay_chc::{BmcSolver, ChcParser};
use sha2::{Digest, Sha256};

const USAGE: &str = "usage: ts_script_export INPUT OUTPUT_DIR PROVENANCE DEPTH MAX_FILES \
                     MAX_INPUT_BYTES MAX_SEGMENTS MAX_OUTPUT_BYTES PER_CASE_MS TOTAL_MS";

#[derive(Debug)]
struct ExportError(String);

impl fmt::Display for ExportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for ExportError {}

struct Args {
    input: PathBuf,
    output_dir: PathBuf,
    provenance: String,
    depth: usize,
    max_input_bytes: u64,
    max_segments: usize,
    max_output_bytes: usize,
    per_case: Duration,
    total: Duration,
}

impl Args {
    fn parse() -> Result<Self, ExportError> {
        let mut values = std::env::args().skip(1);
        let input = PathBuf::from(required(&mut values, "INPUT")?);
        let output_dir = PathBuf::from(required(&mut values, "OUTPUT_DIR")?);
        let provenance = required(&mut values, "PROVENANCE")?;
        if provenance.trim().is_empty() || provenance.chars().any(char::is_control) {
            return Err(ExportError(
                "PROVENANCE must be non-empty and contain no control characters".to_string(),
            ));
        }
        let depth = integer(&required(&mut values, "DEPTH")?, "DEPTH")?;
        let max_files: usize = positive(&required(&mut values, "MAX_FILES")?, "MAX_FILES")?;
        if max_files != 1 {
            return Err(ExportError(
                "MAX_FILES must be 1 for a single-input export".to_string(),
            ));
        }
        let max_input_bytes = positive(
            &required(&mut values, "MAX_INPUT_BYTES")?,
            "MAX_INPUT_BYTES",
        )?;
        let max_segments = positive(&required(&mut values, "MAX_SEGMENTS")?, "MAX_SEGMENTS")?;
        let max_output_bytes = positive(
            &required(&mut values, "MAX_OUTPUT_BYTES")?,
            "MAX_OUTPUT_BYTES",
        )?;
        let per_case_ms = positive(&required(&mut values, "PER_CASE_MS")?, "PER_CASE_MS")?;
        let total_ms = positive(&required(&mut values, "TOTAL_MS")?, "TOTAL_MS")?;
        if values.next().is_some() {
            return Err(ExportError(format!("too many arguments\n{USAGE}")));
        }
        let per_case = Duration::from_millis(per_case_ms);
        let total = Duration::from_millis(total_ms);
        if per_case > total {
            return Err(ExportError(
                "PER_CASE_MS must not exceed TOTAL_MS".to_string(),
            ));
        }
        Ok(Self {
            input,
            output_dir,
            provenance,
            depth,
            max_input_bytes,
            max_segments,
            max_output_bytes,
            per_case,
            total,
        })
    }
}

fn required(values: &mut impl Iterator<Item = String>, name: &str) -> Result<String, ExportError> {
    values
        .next()
        .ok_or_else(|| ExportError(format!("missing {name}\n{USAGE}")))
}

fn integer<T>(value: &str, name: &str) -> Result<T, ExportError>
where
    T: std::str::FromStr,
{
    value
        .parse::<T>()
        .map_err(|_| ExportError(format!("{name} must be a non-negative integer")))
}

fn positive<T>(value: &str, name: &str) -> Result<T, ExportError>
where
    T: std::str::FromStr + PartialEq + Default,
{
    let parsed = integer(value, name)?;
    if parsed == T::default() {
        return Err(ExportError(format!("{name} must be greater than zero")));
    }
    Ok(parsed)
}

fn regular_metadata(path: &Path, kind: &str) -> Result<std::fs::Metadata, ExportError> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| ExportError(format!("cannot inspect {}: {error}", path.display())))?;
    if metadata.file_type().is_symlink() {
        return Err(ExportError(format!(
            "{kind} must not be a symlink: {}",
            path.display()
        )));
    }
    Ok(metadata)
}

fn read_bounded(path: &Path, max_bytes: u64) -> Result<Vec<u8>, ExportError> {
    if !regular_metadata(path, "INPUT")?.is_file() {
        return Err(ExportError(format!(
            "INPUT must be a regular file: {}",
            path.display()
        )));
    }
    let limit = max_bytes
        .checked_add(1)
        .ok_or_else(|| ExportError("MAX_INPUT_BYTES is too large".to_string()))?;
    let file = File::open(path)
        .map_err(|error| ExportError(format!("cannot open {}: {error}", path.display())))?;
    let mut bytes = Vec::new();
    file.take(limit)
        .read_to_end(&mut bytes)
        .map_err(|error| ExportError(format!("cannot read {}: {error}", path.display())))?;
    if u64::try_from(bytes.len()).map_or(true, |length| length > max_bytes) {
        return Err(ExportError(format!(
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

fn ensure_budget(deadline: Instant, phase: &str) -> Result<(), ExportError> {
    if Instant::now() >= deadline {
        return Err(ExportError(format!("budget expired during {phase}")));
    }
    Ok(())
}

fn run() -> Result<(), ExportError> {
    let args = Args::parse()?;
    let started = Instant::now();
    let total_deadline = started
        .checked_add(args.total)
        .ok_or_else(|| ExportError("TOTAL_MS is too large".to_string()))?;
    let case_deadline = started
        .checked_add(args.per_case)
        .ok_or_else(|| ExportError("PER_CASE_MS is too large".to_string()))?
        .min(total_deadline);
    let expected_segments = args
        .depth
        .checked_mul(2)
        .and_then(|count| count.checked_add(2))
        .ok_or_else(|| ExportError("DEPTH overflows the segment count".to_string()))?;
    if expected_segments > args.max_segments {
        return Err(ExportError(format!(
            "DEPTH={} requires {expected_segments} segments, exceeding MAX_SEGMENTS={}",
            args.depth, args.max_segments
        )));
    }

    if !regular_metadata(&args.output_dir, "OUTPUT_DIR")?.is_dir() {
        return Err(ExportError(format!(
            "OUTPUT_DIR must be a directory: {}",
            args.output_dir.display()
        )));
    }
    if !regular_metadata(&args.input, "INPUT")?.is_file() {
        return Err(ExportError(format!(
            "INPUT must be a regular file: {}",
            args.input.display()
        )));
    }
    let canonical_input = std::fs::canonicalize(&args.input).map_err(|error| {
        ExportError(format!(
            "cannot canonicalize {}: {error}",
            args.input.display()
        ))
    })?;
    let canonical_output = std::fs::canonicalize(&args.output_dir).map_err(|error| {
        ExportError(format!(
            "cannot canonicalize {}: {error}",
            args.output_dir.display()
        ))
    })?;
    let bytes = read_bounded(&canonical_input, args.max_input_bytes)?;
    ensure_budget(case_deadline, "bounded input read")?;
    let input_sha256 = sha256_hex(&bytes);
    let text = String::from_utf8(bytes)
        .map_err(|error| ExportError(format!("INPUT is not UTF-8: {error}")))?;
    let problem =
        ChcParser::parse(&text).map_err(|error| ExportError(format!("parse CHC: {error}")))?;
    ensure_budget(case_deadline, "CHC parsing")?;
    let segments = BmcSolver::ts_incremental_script_segments_for_test(problem, args.depth)
        .ok_or_else(|| ExportError("INPUT is not a supported transition system".to_string()))?;
    ensure_budget(case_deadline, "script generation")?;
    if segments.len() > args.max_segments {
        return Err(ExportError(format!(
            "generated {} segments, exceeding MAX_SEGMENTS={}",
            segments.len(),
            args.max_segments
        )));
    }
    let output_bytes = segments
        .iter()
        .try_fold(0usize, |total, segment| total.checked_add(segment.len()));
    let Some(output_bytes) = output_bytes else {
        return Err(ExportError("generated output size overflowed".to_string()));
    };
    if output_bytes > args.max_output_bytes {
        return Err(ExportError(format!(
            "generated {output_bytes} bytes, exceeding MAX_OUTPUT_BYTES={}",
            args.max_output_bytes
        )));
    }
    for index in 0..segments.len() {
        let output = canonical_output.join(format!("segment_{index}.smt2"));
        match std::fs::symlink_metadata(&output) {
            Ok(_) => {
                return Err(ExportError(format!(
                    "refusing to overwrite existing output {}",
                    output.display()
                )));
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(ExportError(format!(
                    "cannot inspect output {}: {error}",
                    output.display()
                )));
            }
        }
    }

    println!("campaign=ay-ts-script-export-v1");
    println!("ay_chc_version={}", env!("CARGO_PKG_VERSION"));
    println!("provenance={}", args.provenance);
    println!("input={}", canonical_input.display());
    println!("input_sha256={input_sha256}");
    println!("output_dir={}", canonical_output.display());
    println!("depth={}", args.depth);
    println!("max_files=1");
    println!("max_input_bytes={}", args.max_input_bytes);
    println!("max_segments={}", args.max_segments);
    println!("max_output_bytes={}", args.max_output_bytes);
    println!("per_case_ms={}", args.per_case.as_millis());
    println!("total_ms={}", args.total.as_millis());
    println!("segments={}", segments.len());
    println!("output_bytes={output_bytes}");

    for (index, segment) in segments.iter().enumerate() {
        if Instant::now() >= case_deadline {
            return Err(ExportError(format!(
                "budget expired before segment {index}"
            )));
        }
        let output = canonical_output.join(format!("segment_{index}.smt2"));
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&output)
            .map_err(|error| {
                ExportError(format!(
                    "cannot create {} without overwrite: {error}",
                    output.display()
                ))
            })?;
        file.write_all(segment.as_bytes())
            .map_err(|error| ExportError(format!("cannot write {}: {error}", output.display())))?;
        println!(
            "segment={index}\tbytes={}\tpath={}",
            segment.len(),
            output.display()
        );
    }
    println!("elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(2);
    }
}
