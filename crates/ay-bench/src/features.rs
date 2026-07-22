// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Feature extraction adapter between `ay-proof-complexity` and `ay-bench`.
//!
//! This module is the *only* entry point the rest of `ay-bench` uses to
//! obtain a per-instance structural feature vector. It:
//!
//! 1. Reads a benchmark file (currently DIMACS CNF; other formats return
//!    an error, which the caller treats as "no features available").
//! 2. Delegates feature computation to
//!    [`ay_proof_complexity::ProofComplexityFeatures`].
//! 3. Wraps the result in an owning struct that the sqlite store layer
//!    can persist.
//!
//! Only DIMACS is wired up for now. SMT-LIB feature extraction requires
//! bit-blasting first and is tracked in the development design notes.

use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::time::Instant;

use ay_proof_complexity::{Cnf, ProofComplexityFeatures};

use crate::error::{BenchError, Result, WithContext};

/// Features plus the time it took to extract them, ready to be attached
/// to a `ResultRow`.
#[derive(Debug, Clone)]
pub struct ExtractedFeatures {
    pub features: ProofComplexityFeatures,
    /// Optional structural family tag. Set by corpus-driven runs; `None`
    /// when the instance came from an on-disk benchmark without family
    /// metadata.
    pub family: Option<String>,
    /// Wall-clock time spent in `extract_*` in milliseconds.
    pub extract_ms: i64,
}

/// Extract features from a benchmark file on disk.
///
/// Supports only DIMACS CNF (`.cnf`, `.dimacs`) for now; other extensions
/// return an error so callers can skip feature attachment without
/// aborting the run.
pub fn extract_from_file(path: &Path) -> Result<ExtractedFeatures> {
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .map(str::to_ascii_lowercase)
        .unwrap_or_default();
    match ext.as_str() {
        "cnf" | "dimacs" => extract_dimacs(path),
        other => Err(BenchError::UnsupportedFeatureFormat {
            extension: other.to_string(),
        }),
    }
}

fn extract_dimacs(path: &Path) -> Result<ExtractedFeatures> {
    let start = Instant::now();
    let cnf = read_dimacs(path)
        .with_bench_context(|| format!("reading DIMACS from {}", path.display()))?;
    let features = ProofComplexityFeatures::from_cnf(&cnf);
    let extract_ms = start.elapsed().as_millis() as i64;
    Ok(ExtractedFeatures {
        features,
        family: None,
        extract_ms,
    })
}

/// Minimal DIMACS reader. Tolerates `c ...` comments, `p cnf N M` header,
/// and whitespace-separated signed ints terminated by `0`. Clauses that
/// reference variables larger than `N` grow `num_vars` implicitly — the
/// header is a hint, not a hard cap, matching the behaviour most SAT
/// solvers ship.
fn read_dimacs(path: &Path) -> Result<Cnf> {
    let file = std::fs::File::open(path)?;
    let reader = BufReader::new(file);

    let mut header_vars: u32 = 0;
    let mut max_seen_var: u32 = 0;
    let mut current: Vec<i32> = Vec::new();
    let mut clauses: Vec<Vec<i32>> = Vec::new();

    for line in reader.lines() {
        let line = line?;
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('c') || trimmed.starts_with('%') {
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("p ") {
            // "p cnf N M"
            let parts: Vec<&str> = rest.split_whitespace().collect();
            if parts.len() >= 3 && parts[0].eq_ignore_ascii_case("cnf") {
                header_vars = parts[1].parse().unwrap_or(0);
            }
            continue;
        }
        for tok in trimmed.split_whitespace() {
            let x: i32 = match tok.parse() {
                Ok(v) => v,
                Err(_) => continue,
            };
            if x == 0 {
                clauses.push(std::mem::take(&mut current));
                continue;
            }
            let v = x.unsigned_abs();
            if v > max_seen_var {
                max_seen_var = v;
            }
            current.push(x);
        }
    }
    // If the final clause wasn't zero-terminated, accept it anyway.
    if !current.is_empty() {
        clauses.push(current);
    }

    let num_vars = header_vars.max(max_seen_var);
    // The clauses have already been read, so reserving from the untrusted
    // header provides no benefit and lets a tiny over-declared file request an
    // enormous allocation. Preserve the declared variable count for feature
    // semantics while sizing storage from the data actually present.
    let mut cnf = Cnf::new_with_capacity(num_vars, clauses.len());
    for c in clauses {
        cnf.add_clause_from_dimacs(&c);
    }
    Ok(cnf)
}

/// Entry point for the `ay bench features <FILE>` subcommand. Prints the
/// feature vector as pretty JSON to stdout.
pub fn cmd_features(file: PathBuf) -> Result<()> {
    let extracted = extract_from_file(&file)?;
    let payload = serde_json::json!({
        "file": file.display().to_string(),
        "extract_ms": extracted.extract_ms,
        "family": extracted.family,
        "features": extracted.features,
    });
    println!("{}", serde_json::to_string_pretty(&payload)?);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_tmp(dir: &tempfile::TempDir, name: &str, body: &str) -> PathBuf {
        let p = dir.path().join(name);
        let mut f = std::fs::File::create(&p).expect("create tmp file");
        f.write_all(body.as_bytes()).expect("write tmp body");
        p
    }

    #[test]
    fn test_extract_from_dimacs_parity3() {
        // parity(3) encoded by hand: x1 XOR x2 XOR x3 = 1. The 4
        // forbidden assignments have even positive-literal count.
        let body = "\
c parity 3
p cnf 3 4
 1  2  3 0
 1 -2 -3 0
-1  2 -3 0
-1 -2  3 0
";
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = write_tmp(&tmp, "p3.cnf", body);
        let ef = extract_from_file(&path).expect("extract ok");
        assert_eq!(ef.features.num_vars, 3);
        assert_eq!(ef.features.num_clauses, 4);
        assert_eq!(ef.features.clause_width_max, 3);
        assert!((ef.features.xor_density - 1.0).abs() < 1e-9);
        assert!(ef.extract_ms >= 0);
    }

    #[test]
    fn test_extract_unknown_extension_errors() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = write_tmp(&tmp, "x.smt2", "(set-logic QF_LIA)");
        let err = extract_from_file(&path).expect_err("should error on smt2");
        let msg = format!("{err:#}");
        assert!(msg.contains("not implemented"), "got: {msg}");
    }

    #[test]
    fn overdeclared_header_does_not_drive_dense_allocations() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = write_tmp(
            &tmp,
            "overdeclared.cnf",
            "p cnf 4000000000 4000000000\n1 0\n",
        );
        let ef = extract_from_file(&path).expect("extract over-declared DIMACS");

        assert_eq!(ef.features.num_vars, 4_000_000_000);
        assert_eq!(ef.features.num_clauses, 1);
        assert_eq!(ef.features.clause_width_max, 1);
    }
}
