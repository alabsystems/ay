// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::array_ghost_candidate::CandidateAttempt;
use super::*;
use crate::transform::{ArrayGhostPairTransformer, GhostPairSpec, Transformer};

/// MODEL_CHECKER_CONSUMER regression: the array-cell safety anchor and BV reachability facts
/// are mutually inductive, including across the three-predicate allocation
/// cycle. The raw-ghost Houdini pass must close and seal both through the
/// production route rather than leaving them as PDR-only Unknowns.
#[test]
#[timeout(300000)]
fn route_seals_harder_and_multi_predicate_model_checker_consumer_canaries() {
    let _env_guard = lock_env();
    let canaries = [
        (
            "harder",
            include_str!(
                "../../../../benchmarks/smt/chc_dt_array_model_checker_consumer_harder.smt2"
            ),
        ),
        (
            "multi-predicate",
            include_str!("../../../../benchmarks/smt/chc_loop_alloc_multi_pred.smt2"),
        ),
    ];

    for (name, smtlib) in canaries {
        let problem = ChcParser::parse(smtlib)
            .unwrap_or_else(|error| panic!("parse MODEL_CHECKER_CONSUMER {name} canary: {error}"));
        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        let result =
            adaptive.try_array_ghost_pair_route(Some(Instant::now() + Duration::from_mins(3)));
        let Some((PortfolioResult::Safe(model), evidence)) = result else {
            panic!("MODEL_CHECKER_CONSUMER {name} canary must seal Safe, got {result:?}");
        };
        assert_eq!(
            evidence,
            ValidationEvidence::QuantifiedArrayInvariantCertificate
        );
        assert!(model.has_quantified_array_certificate());
        assert!(matches!(
            adaptive.finalize_verified_result(PortfolioResult::Safe(model), evidence),
            VerifiedChcResult::Safe(_)
        ));
    }
}

#[test]
#[timeout(120000)]
fn production_candidate_attempt_seals_two_distinct_array_accesses_with_n2() {
    let _env_guard = lock_env();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", vec![array_sort.clone()]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            predicate,
            vec![ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0))],
        ),
    ));
    let array = ChcExpr::var(ChcVar::new("a", array_sort));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicate, vec![array.clone()])],
        Some(ChcExpr::or(
            ChcExpr::ne(
                ChcExpr::select(array.clone(), ChcExpr::Int(0)),
                ChcExpr::Int(0),
            ),
            ChcExpr::ne(ChcExpr::select(array, ChcExpr::Int(1)), ChcExpr::Int(0)),
        )),
    )));

    let spec = GhostPairSpec::analyze(&problem, 2);
    let raw = Box::new(ArrayGhostPairTransformer::new(2))
        .transform(problem.clone())
        .problem;
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let route_start = Instant::now();
    let route_budget = Duration::from_secs(90);
    let attempt = adaptive.try_query_anchored_ghost_candidate(
        &raw,
        &spec,
        2,
        route_budget,
        route_start + route_budget,
        route_start,
        route_budget,
    );
    let CandidateAttempt::Sealed((PortfolioResult::Safe(model), evidence)) = attempt else {
        panic!("the production n=2 candidate attempt must seal Safe");
    };
    assert_eq!(
        evidence,
        ValidationEvidence::QuantifiedArrayInvariantCertificate
    );
    assert!(matches!(
        adaptive.finalize_verified_result(PortfolioResult::Safe(model), evidence),
        VerifiedChcResult::Safe(_)
    ));
}
