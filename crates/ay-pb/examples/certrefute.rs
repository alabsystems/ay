// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MEASUREMENT harness (not a shipped surface): give the OPT-LIN REFUTATION
//! certificate routes a budget of their own and see whether the derivation
//! exists.
//!
//!     cargo run --release -p ay-pb --example certrefute -- \
//!         FILE.opb OPTIMUM "v x1 -x2 ..." OUT.pbp [BUDGET_MS] [ROUTE]
//!
//! `ROUTE` is `all` (default), or one of `compact`, `auxfree`, `pbnative` to
//! run exactly one route against the whole budget. Selecting a single route is
//! not a convenience: with `all`, the routes SHARE one deadline in the
//! production order, so the first route can consume the entire budget and the
//! others measure nothing — the same starvation the production path has, one
//! level down. Naming a route is how each one gets a budget of its own and the
//! chain's shape stops being a confound.
//!
//! # Why this exists, and why `certprobe` is not enough
//!
//! `certprobe` deliberately probes only the four FLOOR emitters
//! (`trivial_zero`, `knapsack_cardinality`, `direct_aggregation`,
//! `lp_dual_floor`). The CLI's actual optimality-certificate fallback is the
//! other pair — `certify_opt_lin_bounds_compact` and `certify_opt_lin_bounds`,
//! which refute the augmented instance `{instance /\ obj <= optimum-1}` — and
//! nothing in the tree could run those with a stated budget in isolation.
//!
//! That gap matters because it is exactly the question the certificate census
//! cannot otherwise answer. In `solve_optimization_with_proof`
//! (crates/ay/src/cmd_pb.rs) the native proof-logging CDCL is handed the
//! CALLER'S WHOLE `timeout_dur`, with no reservation:
//!
//! ```text
//! || { if term_flag.load(..) { return true; }
//!      if let Some(dur) = timeout_dur { if start.elapsed() >= dur { return true; } }
//!      false }
//! ```
//!
//! and only AFTER that stage fails does the certificate fallback run — with the
//! SAME `start` and the SAME `timeout_dur`:
//!
//! ```text
//! let should_stop = || term_flag.load(..)
//!     || timeout_dur.is_some_and(|d| start.elapsed() >= d);
//! ```
//!
//! So whenever the native stage uses its budget up, `should_stop()` is already
//! true when the certificate assembly begins and every
//! `*_interruptible` helper returns `None` on its first check. Raising
//! `--timeout` cannot fix that: the fallback's budget is `B - B = 0` for every
//! `B`. Running the same routes here against a FRESH deadline separates the two
//! hypotheses a census otherwise has to guess between:
//!
//!   * proof VERIFIES here => the derivation EXISTS and the production miss was
//!     a SCHEDULING loss (DELIVERY), not a missing argument;
//!   * still nothing here => the route genuinely cannot close this instance
//!     (SEARCH-PROOF GAP or EXPRESSION), and more budget is not the answer.
//!
//! SOUNDNESS: this prints and writes proof TEXT only. It is never a claim —
//! the pinned VeriPB checker is what decides whether the emitted file
//! establishes the bound. The helpers themselves re-verify the supplied
//! incumbent is feasible and achieves `optimum`, and return `None` rather than
//! a wrong proof.

use std::fs;
use std::io::{self, Write};
use std::num::{ParseIntError, TryFromIntError};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use thiserror::Error;

#[derive(Debug, Error)]
enum CertrefuteError {
    #[error("invalid optimum {value:?}: {source}")]
    InvalidOptimum {
        value: String,
        #[source]
        source: ParseIntError,
    },
    #[error("invalid budget {value:?}: {source}")]
    InvalidBudget {
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
    #[error("failed to write certrefute output: {0}")]
    WriteOutput(io::Error),
    #[error("failed to write proof file {path:?}: {source}")]
    WriteProof {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
}

fn parse_incumbent(input: &str, num_vars: u32) -> Result<Vec<bool>, CertrefuteError> {
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
            .map_err(|source| CertrefuteError::InvalidLiteral {
                token: token.to_string(),
                source,
            })?;
        if index >= 1 && index <= incumbent.len() {
            incumbent[index - 1] = !negated;
        }
    }
    Ok(incumbent)
}

fn main() -> Result<ExitCode, CertrefuteError> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 5 {
        let stderr = io::stderr();
        writeln!(
            stderr.lock(),
            "usage: certrefute FILE.opb OPTIMUM \"v x1 -x2 ...\" OUT.pbp \
             [BUDGET_MS] [all|compact|auxfree|pbnative]"
        )
        .map_err(CertrefuteError::WriteOutput)?;
        return Ok(ExitCode::from(2));
    }
    let path = PathBuf::from(&args[1]);
    let optimum = args[2]
        .parse::<i128>()
        .map_err(|source| CertrefuteError::InvalidOptimum {
            value: args[2].clone(),
            source,
        })?;
    let out_path = PathBuf::from(&args[4]);
    let budget_ms = if args.len() > 5 {
        args[5]
            .parse::<u64>()
            .map_err(|source| CertrefuteError::InvalidBudget {
                value: args[5].clone(),
                source,
            })?
    } else {
        60_000
    };

    let text = fs::read_to_string(&path).map_err(|source| CertrefuteError::ReadOpb {
        path: path.clone(),
        source,
    })?;
    let instance = ay_pb::parse_opb(&text).map_err(|source| CertrefuteError::ParseOpb {
        path: path.clone(),
        source,
    })?;
    let incumbent = parse_incumbent(&args[3], instance.num_vars)?;

    // A FRESH deadline. This is the whole point of the harness: the production
    // path reaches this code with its budget already spent.
    let start = Instant::now();
    let budget = Duration::from_millis(budget_ms);
    let should_stop = move || start.elapsed() >= budget;

    // Same order as the production chain: compact (Sinz) lower bound first for
    // breadth, then the aux-free lift, then the PB-native refutation, which
    // introduces no auxiliary variables at all and so is the route coefficient
    // magnitude cannot force out.
    let selector = args.get(6).map_or("all", String::as_str);
    let mut route = "none";
    let mut proof: Option<String> = None;
    let mut timings: Vec<(&str, u128)> = Vec::new();

    if matches!(selector, "all" | "compact") {
        let t = Instant::now();
        let p = ay_pb::proof::certify_opt_lin_bounds_compact_interruptible(
            &instance,
            &incumbent,
            optimum,
            &should_stop,
        );
        timings.push(("bounds_compact", t.elapsed().as_millis()));
        if p.is_some() {
            route = "bounds_compact";
            proof = p;
        }
    }

    if proof.is_none() && matches!(selector, "all" | "auxfree") {
        let t = Instant::now();
        let p = ay_pb::proof::certify_opt_lin_bounds_interruptible(
            &instance,
            &incumbent,
            optimum,
            &should_stop,
        );
        timings.push(("bounds_auxfree", t.elapsed().as_millis()));
        if p.is_some() {
            route = "bounds_auxfree";
            proof = p;
        }
    }

    if proof.is_none() && matches!(selector, "all" | "pbnative") {
        let t = Instant::now();
        let p = ay_pb::proof::certify_opt_lin_bounds_pb_interruptible(
            &instance,
            &incumbent,
            optimum,
            &should_stop,
        );
        timings.push(("bounds_pb_native", t.elapsed().as_millis()));
        if p.is_some() {
            route = "bounds_pb_native";
            proof = p;
        }
    }

    let bytes = proof.as_ref().map_or(0, String::len);
    if let Some(text) = &proof {
        fs::write(&out_path, text).map_err(|source| CertrefuteError::WriteProof {
            path: out_path.clone(),
            source,
        })?;
    }

    let timing = timings
        .iter()
        .map(|(name, ms)| format!("{name}={ms}ms"))
        .collect::<Vec<_>>()
        .join(",");
    let stdout = io::stdout();
    writeln!(
        stdout.lock(),
        "{}\t{}\t{}\t{}\t{}\t{}\t{}",
        path.display(),
        optimum,
        budget_ms,
        selector,
        route,
        bytes,
        timing
    )
    .map_err(CertrefuteError::WriteOutput)?;
    Ok(ExitCode::SUCCESS)
}
