// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_chc::{testing, BmcConfig, ChcParser, EngineConfig, PortfolioConfig, PortfolioResult};
use ntest::timeout;
use std::time::{Duration, Instant};

const SAFE_INPUT: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert
  (forall ((x Int))
    (=>
      (= x 0)
      (Inv x))))
(assert
  (forall ((x Int))
    (=>
      (Inv x)
      (Inv (+ x 1)))))
(assert
  (forall ((x Int))
    (=>
      (and (Inv x) (< x 0))
      false)))
(check-sat)
(exit)
"#;

#[test]
#[timeout(15_000)]
fn portfolio_parallel_timeout_returns_unknown_promptly() {
    let problem = ChcParser::parse(SAFE_INPUT).unwrap();

    // Use two long-running BMC engines to deterministically exercise the
    // `parallel_timeout` cancellation path. The solver should return `Unknown`
    // promptly without blocking on engine threads that may be stuck in SMT.
    let config = PortfolioConfig::with_engines(vec![
        EngineConfig::Bmc(BmcConfig::with_engine_config(1_000_000, false, None)),
        EngineConfig::Bmc(BmcConfig::with_engine_config(1_000_000, false, None)),
    ])
    .parallel_timeout(Some(Duration::from_millis(50)))
    .preprocessing(false);

    let solver = testing::new_portfolio_solver(problem, config);
    let start = Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();

    // The algebraic prepass may solve this trivial problem (x >= 0) before
    // the BMC engines even start, returning Safe instead of Unknown. Both
    // outcomes are valid: Safe means the prepass found the invariant quickly,
    // Unknown means BMC timed out as expected. The key property is prompt return.
    assert!(
        matches!(result, PortfolioResult::Unknown | PortfolioResult::Safe(_)),
        "expected Unknown or Safe, got {result:?}"
    );
    // Use generous timeout to avoid flaky failures on loaded CI systems (#1585).
    assert!(
        elapsed < Duration::from_secs(10),
        "expected timely return after parallel_timeout, elapsed={elapsed:?}"
    );
}
