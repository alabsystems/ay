// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal CHC probe harness: parse an SMT-LIB CHC file and solve it with the
//! adaptive portfolio under a millisecond budget. Prints `sat` / `unsat` /
//! `unknown` (standard CHC polarity: Safe = sat). Used for before/after
//! benchmark probes without the full `ay --features cli` build.
//!
//! Usage: `chc_probe <file.smt2> [budget_ms]`

use std::time::Duration;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = match args.next() {
        Some(p) => p,
        None => {
            eprintln!("usage: chc_probe <file.smt2> [budget_ms]");
            std::process::exit(2);
        }
    };
    let budget_ms: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(120_000);

    let content = match std::fs::read_to_string(&path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("read error: {e}");
            std::process::exit(2);
        }
    };
    let problem = match ay_chc::ChcParser::parse(&content) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("parse error: {e}");
            println!("unknown");
            return;
        }
    };
    let config = ay_chc::AdaptiveConfig::with_budget(Duration::from_millis(budget_ms), false);
    let solver = ay_chc::AdaptivePortfolio::new(problem, config);
    match solver.solve() {
        ay_chc::VerifiedChcResult::Safe(_) => println!("sat"),
        ay_chc::VerifiedChcResult::Unsafe(_) => println!("unsat"),
        _ => println!("unknown"),
    }
}
