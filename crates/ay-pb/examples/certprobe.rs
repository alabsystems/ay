// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MEASUREMENT harness (not a shipped surface): reports which OPT-LIN
//! certificate route fires for a given instance + known optimum + incumbent,
//! so certificate coverage can be censused per ROUTE instead of inferred from
//! whichever route happens to rescue the instance.
//!
//!     cargo run --release -p ay-pb --example certprobe -- FILE.opb OPT "v x1 -x2 ..."
//!
//! Prints one TSV line: file, optimum, then the first route (in the production
//! chain's order) that returns a proof, and the proof's byte size. The two
//! refutation routes are deliberately NOT probed here — they are general
//! fallbacks whose success says nothing about the floor emitters' shape
//! coverage, which is what this measures.

use std::fs;
use std::io::{self, Write};
use std::num::{ParseIntError, TryFromIntError};
use std::path::PathBuf;
use std::process::ExitCode;

use thiserror::Error;

#[derive(Debug, Error)]
enum CertprobeError {
    #[error("invalid optimum {value:?}: {source}")]
    InvalidOptimum {
        value: String,
        #[source]
        source: ParseIntError,
    },
    #[error("failed to read OPB file {path:?}: {source}")]
    ReadOpb {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    #[error("failed to parse OPB file {path:?}: {source}")]
    ParseOpb {
        path: PathBuf,
        #[source]
        source: ay_pb::ParseError,
    },
    #[error("bad literal token {token:?}: {source}")]
    InvalidLiteral {
        token: String,
        #[source]
        source: ParseIntError,
    },
    #[error("literal index does not fit this platform: {0}")]
    LiteralIndex(#[from] TryFromIntError),
    #[error("failed to write certprobe output: {0}")]
    WriteOutput(io::Error),
    #[error("failed to write proof file {path:?}: {source}")]
    WriteProof {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
}

fn parse_incumbent(input: &str, num_vars: u32) -> Result<Vec<bool>, CertprobeError> {
    let mut incumbent = vec![false; usize::try_from(num_vars)?];
    for token in input.split_whitespace() {
        if token == "v" || token.is_empty() {
            continue;
        }
        let (negated, name) = match token.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, token),
        };
        let index = name
            .trim_start_matches('x')
            .parse::<usize>()
            .map_err(|source| CertprobeError::InvalidLiteral {
                token: token.to_string(),
                source,
            })?;
        if index >= 1 && index <= incumbent.len() {
            incumbent[index - 1] = !negated;
        }
    }
    Ok(incumbent)
}

fn main() -> Result<ExitCode, CertprobeError> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        let stderr = io::stderr();
        writeln!(
            stderr.lock(),
            "usage: certprobe FILE.opb OPTIMUM \"v x1 -x2 ...\""
        )
        .map_err(CertprobeError::WriteOutput)?;
        return Ok(ExitCode::from(2));
    }
    let path = PathBuf::from(&args[1]);
    let optimum = args[2]
        .parse::<i128>()
        .map_err(|source| CertprobeError::InvalidOptimum {
            value: args[2].clone(),
            source,
        })?;
    let text = fs::read_to_string(&path).map_err(|source| CertprobeError::ReadOpb {
        path: path.clone(),
        source,
    })?;
    let instance = ay_pb::parse_opb(&text).map_err(|source| CertprobeError::ParseOpb {
        path: path.clone(),
        source,
    })?;

    // Build the incumbent from AY's `v` line: `v x1 -x2 x3 ...`.
    let incumbent = parse_incumbent(&args[3], instance.num_vars)?;

    let routes: Vec<(&str, Option<String>)> = vec![
        (
            "trivial_zero_floor",
            ay_pb::proof::certify_opt_lin_trivial_zero_floor(&instance, &incumbent, optimum),
        ),
        (
            "knapsack_cardinality",
            ay_pb::proof::certify_opt_lin_knapsack_cardinality(&instance, &incumbent, optimum),
        ),
        (
            "direct_aggregation_floor",
            ay_pb::proof::certify_opt_lin_direct_aggregation_floor(&instance, &incumbent, optimum),
        ),
        (
            "lp_dual_floor",
            ay_pb::proof::certify_opt_lin_lp_dual_floor(&instance, &incumbent, optimum),
        ),
    ];

    let fired: Vec<&str> = routes
        .iter()
        .filter(|(_, p)| p.is_some())
        .map(|(n, _)| *n)
        .collect();
    let first = routes.iter().find(|(_, p)| p.is_some());
    let (name, bytes) = match first {
        Some((n, Some(p))) => (*n, p.len()),
        _ => ("NONE", 0),
    };
    let diag = if std::env::var("CERTPROBE_DIAG").is_ok() {
        ay_pb::proof::lp_dual_floor_diagnosis(&instance, optimum)
    } else {
        String::new()
    };
    let stdout = io::stdout();
    writeln!(
        stdout.lock(),
        "{}\t{}\t{}\t{}\t{}\t{}",
        path.display(),
        optimum,
        name,
        bytes,
        fired.join(","),
        diag
    )
    .map_err(CertprobeError::WriteOutput)?;

    // Dump the winning proof when asked, so it can be handed to VeriPB, plus one
    // file PER ROUTE that fired. A route census that can only hand the checker
    // whichever proof happened to come first cannot verify the route it is
    // actually measuring — the emitters are ordered, not ranked.
    if let Ok(out) = std::env::var("CERTPROBE_DUMP") {
        if let Some((_, Some(p))) = first {
            let output_path = PathBuf::from(&out);
            fs::write(&output_path, p).map_err(|source| CertprobeError::WriteProof {
                path: output_path,
                source,
            })?;
        }
        for (route, proof) in &routes {
            let Some(proof) = proof else { continue };
            let output_path = PathBuf::from(format!("{out}.{route}"));
            fs::write(&output_path, proof).map_err(|source| CertprobeError::WriteProof {
                path: output_path,
                source,
            })?;
        }
    }
    Ok(ExitCode::SUCCESS)
}
