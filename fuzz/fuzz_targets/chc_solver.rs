// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC Solver Fuzz Target
//!
//! This fuzz target verifies the CHC parser and solver don't panic on
//! arbitrary SMT-LIB CHC input. It also tests that Safe results have
//! valid proofs (model verification).
//!
//! Verification coverage:
//! - Parser: no panics on arbitrary input
//! - Solver: no panics on valid parsed problems
//! - Safe proofs: verify_model() confirms invariant is inductive (#209)
//! - Preprocessing: run with preprocessing ON to exercise the full pipeline
//! - Cross-check: if both preprocessing-ON and -OFF runs produce definitive
//!   results, they must agree (no soundness flip from transformations)

#![no_main]
#![forbid(unsafe_code)]

use ay_chc::{
    engines, testing, BmcConfig, ChcParser, EngineConfig, PdrConfig, PortfolioConfig,
    PortfolioResult,
};
use libfuzzer_sys::fuzz_target;
use std::time::Duration;

fuzz_target!(|data: &[u8]| {
    // Try to interpret bytes as UTF-8 string
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return, // Non-UTF8 data ignored
    };

    // Parse CHC problem - should not panic
    let problem = match ChcParser::parse(input) {
        Ok(p) => p,
        Err(_) => return, // Parse errors are expected for random input
    };

    // Quick-timeout config for fuzzing (don't want to hang)
    // Use default configs and modify only public fields
    let mut pdr_config = PdrConfig::default();
    pdr_config.max_frames = 5;
    pdr_config.max_iterations = 50;
    pdr_config.max_obligations = 100;
    pdr_config.verbose = false;

    // --- Run 1: WITHOUT preprocessing (original behavior) ---
    let config_no_pp = PortfolioConfig::with_engines(vec![
        EngineConfig::Bmc(BmcConfig::with_engine_config(5, false, None)),
        EngineConfig::Pdr(pdr_config.clone()),
    ])
    .parallel(false) // Sequential for determinism in fuzzing
    .timeout(Some(Duration::from_millis(100)))
    .verbose(false)
    .preprocessing(false);

    let solver = engines::new_portfolio_solver(problem.clone(), config_no_pp);
    let result_no_pp = solver.solve();

    // --- Verify Safe proofs against the original problem ---
    // This is the critical soundness check: if the solver claims Safe, the
    // invariant model must satisfy all original CHC clauses.
    if let PortfolioResult::Safe(ref model) = result_no_pp {
        let mut verifier = testing::new_pdr_solver(problem.clone(), PdrConfig::default());
        assert!(
            verifier.verify_model(model),
            "FUZZ: Safe result has invalid proof (model verification failed, no preprocessing)"
        );
    }

    // --- Run 2: WITH preprocessing to exercise the transformation pipeline ---
    let config_pp = PortfolioConfig::with_engines(vec![
        EngineConfig::Bmc(BmcConfig::with_engine_config(5, false, None)),
        EngineConfig::Pdr(pdr_config),
    ])
    .parallel(false)
    .timeout(Some(Duration::from_millis(100)))
    .verbose(false)
    .preprocessing(true);

    let solver = engines::new_portfolio_solver(problem.clone(), config_pp);
    let result_pp = solver.solve();

    // --- Verify Safe proofs from preprocessed run ---
    if let PortfolioResult::Safe(ref model) = result_pp {
        let mut verifier = testing::new_pdr_solver(problem.clone(), PdrConfig::default());
        assert!(
            verifier.verify_model(model),
            "FUZZ: Safe result has invalid proof (model verification failed, with preprocessing)"
        );
    }

    // --- Cross-check: preprocessing must not flip definitive results ---
    let is_definitive =
        |r: &PortfolioResult| matches!(r, PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_));

    if is_definitive(&result_no_pp) && is_definitive(&result_pp) {
        let same_verdict = matches!(
            (&result_no_pp, &result_pp),
            (PortfolioResult::Safe(_), PortfolioResult::Safe(_))
                | (PortfolioResult::Unsafe(_), PortfolioResult::Unsafe(_))
        );
        assert!(
            same_verdict,
            "FUZZ: Preprocessing changed the result! \
             no_preprocessing={result_no_pp:?}, with_preprocessing={result_pp:?}"
        );
    }
});
