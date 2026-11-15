// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! model-checker-consumer's exported query for `safe_symbolic_from_elem` (model-checker-consumer
//! the development design notes,
//! sha256 `9d9628d4…582f1`): `E = &[1u32, 2, 3][1]`, `i < 2`, and the read
//! `*(E as *const u32).add(i)` must be 2 or 3. The constant-pointer rule seeds
//! `mem[0x3_0000_0000..=0x3_0000_0008]` with 1, 2, 3, so the query is SAFE.
//!
//! The CHC is acyclic. Clause inlining folds all of it into one unsatisfiable
//! query, and the acyclic BMC and the BV-native probe prove it Safe too, but
//! every one of those proofs was then discarded: back-translating the empty
//! inlined model needs an interpretation of `bb5` (the block after the read),
//! whose defining body reads the seeded memory through the pointer, and no
//! projection could eliminate the array-sorted local `mem`. With no other
//! engine converging, ay ran past model-checker-consumer's 30 s budget on the row (875 s in
//! model-checker-consumer's driver, 120 s standalone).
//!
//! The rows are solved the way model-checker-consumer solves them in process: one
//! `ChcProblem::query_obligations` slice per `error_pN`, the nullary fail
//! query expanded, `AdaptivePortfolio::new_for_solve_with_cancellation` with
//! `strict_proofs`, and every proved row's model re-validated against that
//! row's own problem.

use ay_chc::{
    engines, AdaptiveConfig, AdaptivePortfolio, CancellationToken, ChcParser, ChcProblem,
    PdrConfig, VerifiedChcResult,
};
use ntest::timeout;
use std::time::{Duration, Instant};

const QUERY: &str =
    include_str!("../fixtures/model_checker_consumer_seeded_const_pointer_read_safe.smt2");

/// model-checker-consumer's per-harness budget for this query.
const ROW_BUDGET: Duration = Duration::from_secs(30);

fn rows() -> Vec<(String, ChcProblem)> {
    let problem = ChcParser::parse(QUERY).expect("the exported query parses");
    let obligations = problem
        .query_obligations()
        .expect("the exported query slices");
    assert_eq!(obligations.len(), 15, "one obligation per error_pN");
    obligations
        .into_iter()
        .map(|obligation| {
            let (id, mut problem) = obligation.into_parts();
            problem.expand_nullary_fail_queries(false);
            (id.label().to_string(), problem)
        })
        .collect()
}

fn solve_row(problem: ChcProblem) -> (VerifiedChcResult, Duration) {
    let mut config = AdaptiveConfig::with_budget(ROW_BUDGET, false);
    config.strict_proofs = true;
    let parent = CancellationToken::new();
    let started = Instant::now();
    let report = AdaptivePortfolio::new_for_solve_with_cancellation(problem, config, &parent)
        .solve_proof_run_with_budget_report();
    let result = report.proof_run().result().clone();
    (result, started.elapsed())
}

/// Every row is proved, each with a model that validates against the row, and
/// the row with the seeded read (`error_p14`) inside its budget.
#[test]
#[timeout(600_000)]
fn every_row_is_proved_with_a_model_that_validates() {
    for (label, problem) in rows() {
        let (result, elapsed) = solve_row(problem.clone());
        let VerifiedChcResult::Safe(invariant) = result else {
            panic!("{label}: the query is safe, got {result:?} after {elapsed:?}");
        };
        let validated = engines::validate_external_invariant_model(
            &problem,
            invariant.model(),
            &PdrConfig::default(),
        )
        .expect("validation runs");
        assert!(validated, "{label}: the Safe model must validate");
        assert!(
            elapsed < ROW_BUDGET,
            "{label}: proved after {elapsed:?}, past the {ROW_BUDGET:?} budget"
        );
    }
}

/// The whole query, as `ay query.smt2` solves it.
#[test]
#[timeout(300_000)]
fn the_whole_query_is_proved() {
    let problem = ChcParser::parse(QUERY).expect("the exported query parses");
    let mut config = AdaptiveConfig::with_budget(ROW_BUDGET, false);
    config.strict_proofs = true;
    let started = Instant::now();
    let result = AdaptivePortfolio::new(problem, config).solve();
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "the query is safe, got {result:?} after {:?}",
        started.elapsed()
    );
}
