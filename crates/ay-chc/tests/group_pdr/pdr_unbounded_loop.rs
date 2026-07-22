// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_chc::{testing, ChcParser, PdrConfig, PdrResult};
use ntest::timeout;

/// Canonical unbounded loop benchmark requiring x >= 0 invariant discovery (#656, #1858).
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_unbounded_loop_safe_conjecture_verify_model() {
    let input = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/chc/unbounded_loop.smt2"
    ));

    let problem = ChcParser::parse(input).unwrap();
    let mut config = PdrConfig::default();
    config.verbose = false;

    let mut solver = testing::new_pdr_solver(problem, config);
    let result = solver.solve();

    match &result {
        PdrResult::Safe(model) => {
            assert!(
                solver.verify_model(model),
                "PDR returned Safe but verify_model rejected the model"
            );
        }
        other => panic!("expected Safe, got {other:?}"),
    }
}
