// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal direct-PDR probe harness: parse an SMT-LIB CHC file and solve it
//! with `PdrSolver` directly (no adaptive portfolio, no transforms). Prints
//! `sat` / `unsat` / `unknown` (standard CHC polarity: Safe = sat).
//!
//! Usage: `pdr_probe <file.smt2> [--verbose]`

fn main() {
    let mut args = std::env::args().skip(1);
    let path = match args.next() {
        Some(p) => p,
        None => {
            eprintln!("usage: pdr_probe <file.smt2> [--verbose]");
            std::process::exit(2);
        }
    };
    let rest: Vec<String> = args.collect();
    let verbose = rest.iter().any(|a| a == "--verbose" || a == "-v");
    let mode = rest
        .iter()
        .find(|a| a.starts_with("--config="))
        .map(|a| a.trim_start_matches("--config=").to_string())
        .unwrap_or_else(|| "default".to_string());
    let timeout_ms: Option<u64> = rest
        .iter()
        .find(|a| a.starts_with("--timeout-ms="))
        .and_then(|a| a.trim_start_matches("--timeout-ms=").parse().ok());

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
    let mut config = match mode.as_str() {
        "production" => ay_chc::PdrConfig::production(verbose),
        "splits" => ay_chc::PdrConfig::portfolio_variant_with_splits().with_verbose(verbose),
        "spacer" => ay_chc::PdrConfig::portfolio_spacer_variant().with_verbose(verbose),
        _ => ay_chc::PdrConfig::default().with_verbose(verbose),
    };
    if let Some(ms) = timeout_ms {
        config.solve_timeout = Some(std::time::Duration::from_millis(ms));
    }
    let mut solver = ay_chc::engines::new_pdr_solver(problem, config);
    let start = std::time::Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();
    match result {
        ay_chc::PdrResult::Safe(model) => {
            println!("sat");
            eprintln!("[pdr_probe] Safe in {elapsed:?}; model:");
            for (pred, interp) in model.iter() {
                eprintln!("  pred {} := {}", pred.index(), interp.formula);
            }
        }
        ay_chc::PdrResult::Unsafe(cex) => {
            println!("unsat");
            eprintln!(
                "[pdr_probe] Unsafe in {elapsed:?}; {} steps",
                cex.steps.len()
            );
        }
        ay_chc::PdrResult::Unknown => {
            println!("unknown");
            eprintln!("[pdr_probe] Unknown in {elapsed:?}");
        }
        other => {
            println!("unknown");
            eprintln!("[pdr_probe] {other:?} in {elapsed:?}");
        }
    }
}
