// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External-validation repro harness mirroring model-checker-consumer's native CHC path:
//! `AdaptivePortfolio::new(problem)` + `solve()`, then, on a Safe result,
//! `engines::validate_external_invariant_model(ORIGINAL_problem, model, default)`
//! — the ORIGINAL (un-stripped) problem, exactly as model-checker-consumer re-parses and
//! re-validates it (native.rs `external_validation_problem`).
//!
//! Prints two machine-parsable lines:
//!   SOLVE=<sat|unsat|unknown> solve_ms=<n> model_len=<n>
//!   VALIDATE=<Ok(true)|Ok(false)|Err> val_ms=<n>          (only when Safe)
//!
//! Usage: `repro_cn <file.smt2> [budget_ms]`

use std::time::{Duration, Instant};

fn main() {
    let mut args = std::env::args().skip(1);
    let path = match args.next() {
        Some(p) => p,
        None => {
            eprintln!("usage: repro_cn <file.smt2> [budget_ms]");
            std::process::exit(2);
        }
    };
    let budget_ms: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60_000);

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
            println!("SOLVE=unknown solve_ms=0 model_len=0");
            return;
        }
    };

    // ORIGINAL, un-stripped problem for external re-validation (model-checker-consumer clones
    // the problem BEFORE it is moved+stripped into AdaptivePortfolio::new).
    let external_validation_problem = problem.clone();

    let config = ay_chc::AdaptiveConfig::with_budget(Duration::from_millis(budget_ms), false);
    let solver = ay_chc::AdaptivePortfolio::new(problem, config);

    let t0 = Instant::now();
    let result = solver.solve();
    let solve_ms = t0.elapsed().as_millis();

    match result {
        ay_chc::VerifiedChcResult::Safe(inv) => {
            let model = inv.model().clone();
            println!("SOLVE=sat solve_ms={solve_ms} model_len={}", model.len());
            let vconfig = ay_chc::PdrConfig::default();
            let t1 = Instant::now();
            let v = ay_chc::engines::validate_external_invariant_model(
                &external_validation_problem,
                &model,
                &vconfig,
            );
            let val_ms = t1.elapsed().as_millis();
            let vstr = match v {
                Ok(true) => "Ok(true)".to_string(),
                Ok(false) => "Ok(false)".to_string(),
                Err(e) => format!("Err({e:?})"),
            };
            println!("VALIDATE={vstr} val_ms={val_ms}");
        }
        ay_chc::VerifiedChcResult::Unsafe(_) => {
            println!("SOLVE=unsat solve_ms={solve_ms} model_len=0");
        }
        _ => {
            println!("SOLVE=unknown solve_ms={solve_ms} model_len=0");
        }
    }
}
