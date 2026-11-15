// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A satisfiable collapsed query lands through its model's derivation, and a
//! derivation the original clauses refute never lands.
//!
//! The fixture has the realloc-grow twin's shape, scaled down: two facts for
//! `P` merge into one disjunctive edge, BV-native preprocessing inlines the
//! chain into one query-only clause, and only the SECOND disjunct reaches the
//! query. The disjunct defines `y` from `x`, so the discharge's model names
//! `x` alone and `y` comes back from the definition trail.

use super::query_only_landings;
use crate::engine_result::ValidationEvidence;
use crate::portfolio::{PortfolioResult, PreprocessSummary};
use crate::{
    AdaptiveConfig, AdaptivePortfolio, CancellationToken, ChcExpr, ChcParser, ChcProblem,
    ClauseBody, ClauseHead, HornClause,
};
use ntest::timeout;
use std::time::Duration;

/// `P(x) <= x < 16 | 32 < x < 64.  Q(x + 5) <= P(x).  false <= Q(y) /\ y > 48 /\ bound.`
/// Only the second fact reaches the query (`x = 44`, `y = 49` and up).
fn second_fact_problem(bound: &str) -> ChcProblem {
    let source = format!(
        "(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(declare-fun Q ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (bvult x #x10) (P x))))
(assert (forall ((x (_ BitVec 8))) (=> (and (bvugt x #x20) (bvult x #x40)) (P x))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (P x) (= y (bvadd x #x05))) (Q y))))
(assert (forall ((y (_ BitVec 8))) (=> (and (Q y) (bvugt y #x30) {bound}) false)))
(check-sat)
"
    );
    ChcParser::parse(&source).expect("the second-fact fixture parses")
}

fn portfolio(problem: &ChcProblem) -> AdaptivePortfolio {
    AdaptivePortfolio::new(
        problem.clone(),
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(30)),
    )
}

fn probe(
    adaptive: &AdaptivePortfolio,
    summary: PreprocessSummary,
) -> Option<(PortfolioResult, ValidationEvidence)> {
    let features = adaptive.features();
    adaptive.run_preprocessed_acyclic_bmc_probe(
        summary,
        &features,
        Duration::from_secs(20),
        "test-query-only-landing",
        true,
    )
}

/// The counterexample comes from the discharge's own model, back-translated
/// and validated on the original clauses, with the trace it derives.
///
/// Counterfactual: without the landing, the bounded replay confirms this
/// small problem as well, but the landing count stays put. Without the
/// multi-edge candidate fix, the merged fact maps back to the first
/// (`x < 16`) fact, the translation is refused, and the replay runs instead.
#[test]
#[timeout(120_000)]
fn a_satisfiable_collapsed_query_lands_through_its_model() {
    let problem = second_fact_problem("true");
    let summary = PreprocessSummary::build_bv_native_with_limits(
        problem.clone(),
        false,
        None,
        &CancellationToken::new(),
    )
    .expect("BV-native preprocessing completes");
    assert!(
        AdaptivePortfolio::is_fully_collapsed_query_problem(&summary.transformed_problem),
        "setup: preprocessing collapses the chain into query-only clauses"
    );
    let adaptive = portfolio(&problem);
    let landed_before = query_only_landings();

    let result = probe(&adaptive, summary);
    let Some((PortfolioResult::Unsafe(cex), ValidationEvidence::FullVerification)) = result else {
        panic!("x = 44 reaches the query through the second fact; got {result:?}");
    };
    assert_eq!(
        query_only_landings(),
        landed_before + 1,
        "the counterexample must come from the query-only landing, not the replay"
    );
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("the landing carries its derivation");
    crate::ground_derivation::validate_ground_derivation(&problem, derivation)
        .expect("the derivation validates on the original clauses");
    assert!(
        !cex.steps.is_empty(),
        "the published counterexample states the trace its derivation derives"
    );
}

/// Negative twin: a summary whose collapsed query is satisfiable but whose
/// transform chain is fabricated (an identity back-translation of a problem
/// it does not come from). The original problem is safe (`y < 43` leaves
/// nothing above 48), so the landing must refuse and nothing is confirmed.
#[test]
#[timeout(120_000)]
fn a_fabricated_collapse_never_lands() {
    let problem = second_fact_problem("(bvult y #x2b)");
    let mut collapsed = ChcProblem::new();
    collapsed.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::False,
    ));
    let summary = PreprocessSummary {
        original_problem: problem.clone(),
        transformed_problem: collapsed,
        back_translator: Box::new(crate::transform::IdentityBackTranslator),
        bv_abstracted: false,
        transform_memory: crate::transform::TransformMemoryReport::identity(),
    };
    let adaptive = portfolio(&problem);
    let landed_before = query_only_landings();

    let result = probe(&adaptive, summary);
    assert!(
        !matches!(result, Some((PortfolioResult::Unsafe(_), _))),
        "the original problem is safe; got {result:?}"
    );
    assert_eq!(
        query_only_landings(),
        landed_before,
        "a derivation the original clauses refute must not land"
    );
}
