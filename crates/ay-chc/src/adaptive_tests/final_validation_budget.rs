// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `adaptive_tests` to preserve the existing test FQNs.

/// Companion SAFE analogue: same shape, unreachable error. Whatever the lane
/// does (probe, landing, exhaustive follow-on), it must never come back
/// Unsafe. Safe and Unknown are both acceptable.
#[test]
#[timeout(300_000)]
#[serial_test::serial(bmc_only_hub_analogue)]
fn bmc_only_lane_never_reports_safe_hub_analogue_unsafe() {
    let smt = bmc_only_hub_analogue_smt(false);
    let problem = ChcParser::parse(&smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let config = bmc_only_lane_config(&problem, Duration::from_mins(1));
    let result = crate::engines::solve_bmc_only(problem, config);
    assert!(
        !matches!(result, VerifiedChcResult::Unsafe(_)),
        "SAFE hub analogue was reported UNSAFE through the BMC-only lane: {result}"
    );
}

/// #4751 cause-4: the final-validation budget must never be SMALLER than the
/// historical fixed budget, and must be exactly that budget when the run has no
/// deadline. A fixed 1.5s gate discarded an already-verified merged case-split
/// model on dillig12_m while ~33s of the solve budget was still unused.
#[test]
fn final_validation_budget_never_below_nominal() {
    let problem = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-fun p (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x 0) (p x))))\n\
         (assert (forall ((x Int)) (=> (and (p x) (< x 0)) false)))\n",
    )
    .expect("parse");
    let portfolio = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_mins(1)),
    );
    let nominal = Duration::from_millis(1500);

    // No deadline (unbounded run): unchanged from the historical constant.
    assert_eq!(portfolio.final_validation_budget(None, nominal), nominal);

    // Generous remaining wall: scales up, so a complete proof is not discarded
    // for want of validation time.
    let generous =
        portfolio.final_validation_budget(Some(Instant::now() + Duration::from_secs(40)), nominal);
    assert!(
        generous > nominal,
        "expected the budget to scale with a 40s remaining wall, got {generous:?}"
    );
    assert!(
        generous <= Duration::from_secs(20),
        "budget must stay under the cap, got {generous:?}"
    );

    // Nearly-exhausted wall: must still never drop BELOW the nominal, which is
    // where `scaled_probe_budget` would have collapsed the floor to zero.
    let tight = portfolio
        .final_validation_budget(Some(Instant::now() + Duration::from_millis(10)), nominal);
    assert!(
        tight >= nominal,
        "budget must never fall below the historical fixed budget, got {tight:?}"
    );
}
