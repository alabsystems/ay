// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::time::Duration;

use ay_chc::{ChcExpr, ChcProblem, ClauseBody, HornClause};

use crate::invoke::{solve_query_obligations_with_proof_report, EncodeConfig};
use crate::query_proof_report::{
    obligation_set_sha256, QueryObligationBatchProofReport, QueryObligationBatchVerdict,
};

fn all_pruned_problem(constraint: ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(constraint)));
    problem
}

#[test]
fn all_pruned_queries_are_source_bound_vacuity_proofs() {
    let problem = all_pruned_problem(ChcExpr::Bool(false));
    let report = solve_query_obligations_with_proof_report(&problem, &EncodeConfig::new())
        .expect("a remembered false query is valid and needs no solver row");

    assert!(report.rows().is_empty());
    assert_eq!(
        report.verdict(),
        QueryObligationBatchVerdict::AllQueriesPruned
    );
    assert!(report.accepted_as_proof());
    assert!(report.trust_full_verifier_admissible());
    assert_eq!(report.source_query_count(), 1);
    assert_eq!(report.source_pruned_false_query_count(), 1);
    assert!(!report.source_pruned_false_query_ids()[0]
        .content_bytes()
        .is_empty());

    let json = report.to_json_value();
    assert_eq!(json["result"], "safe");
    assert_eq!(json["disposition"], "all-queries-pruned");
    assert_eq!(json["proof_status"], "verified-vacuity");
    assert_eq!(json["replay"]["status"], "source-vacuity-checked");
    assert_eq!(json["obligation_set"]["count"], 1);
    assert_eq!(json["obligation_set"]["surviving_count"], 0);
    assert_eq!(json["obligation_set"]["pruned_false_count"], 1);
    assert_eq!(
        json["obligation_set"]["pruned_false_queries"][0]["ordinal"],
        0
    );
    assert!(json["trust_full_verifier_non_admission_reason"].is_null());
}

#[test]
fn distinct_pruned_queries_cannot_share_a_batch_identity() {
    let literal = all_pruned_problem(ChcExpr::Bool(false));
    let folded = all_pruned_problem(ChcExpr::eq(ChcExpr::int(0), ChcExpr::int(1)));
    let literal_report = solve_query_obligations_with_proof_report(&literal, &EncodeConfig::new())
        .expect("literal false query should produce vacuity evidence");
    let folded_report = solve_query_obligations_with_proof_report(&folded, &EncodeConfig::new())
        .expect("folded false query should produce vacuity evidence");

    assert_eq!(
        literal_report.verdict(),
        QueryObligationBatchVerdict::AllQueriesPruned
    );
    assert_eq!(
        folded_report.verdict(),
        QueryObligationBatchVerdict::AllQueriesPruned
    );
    assert_eq!(
        literal_report.source_normalized_input_sha256(),
        folded_report.source_normalized_input_sha256(),
        "post-pruning normalized sources intentionally match"
    );
    assert_ne!(
        literal_report.source_pruned_false_query_ids()[0].content_sha256(),
        folded_report.source_pruned_false_query_ids()[0].content_sha256(),
    );
    assert_ne!(
        literal_report.obligation_set_sha256(),
        folded_report.obligation_set_sha256(),
        "the source-bound set must retain exact pruned-query content"
    );
    assert!(literal_report.trust_full_verifier_admissible());
    assert!(folded_report.trust_full_verifier_admissible());
}

#[test]
fn malformed_pruned_order_is_rejected_by_the_sealed_batch() {
    let mut problem = all_pruned_problem(ChcExpr::Bool(false));
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::int(0),
        ChcExpr::int(1),
    ))));
    let ids = problem.pruned_false_query_ids();
    let mut reversed = ids.clone();
    reversed.reverse();
    for malformed in [reversed, vec![ids[0].clone(), ids[0].clone()]] {
        let result = QueryObligationBatchProofReport::new(
            problem.normalized_input(),
            &malformed,
            false,
            &[],
            Vec::new(),
            Duration::ZERO,
        );
        assert!(result.is_err());
    }
}

fn mixed_order_identity(pruned_first: bool) -> (String, String, usize, usize) {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("p", Vec::new());
    let pruned = HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false)));
    let active = HornClause::query(ClauseBody::predicates_only(vec![(predicate, Vec::new())]));
    if pruned_first {
        problem.add_clause(pruned);
        problem.add_clause(active);
    } else {
        problem.add_clause(active);
        problem.add_clause(pruned);
    }
    let normalized = problem.normalized_input();
    let source_sha256 = problem.normalized_input_sha256();
    let source_bytes = u64::try_from(normalized.len()).expect("fixture length fits u64");
    let pruned_ids = problem.pruned_false_query_ids();
    let active_ids: Vec<_> = problem
        .query_obligations()
        .expect("mixed fixture should validate")
        .into_iter()
        .map(|obligation| obligation.into_parts().0)
        .collect();
    let identity = obligation_set_sha256(
        ay_chc::NORMALIZED_CHC_INPUT_SCHEMA,
        &source_sha256,
        source_bytes,
        &pruned_ids,
        false,
        &active_ids,
    );
    (
        source_sha256,
        identity,
        pruned_ids[0].ordinal(),
        active_ids[0].source_query_ordinal(),
    )
}

#[test]
fn pruned_and_active_source_order_is_identity_bound() {
    let pruned_first = mixed_order_identity(true);
    let active_first = mixed_order_identity(false);
    assert_eq!(pruned_first.0, active_first.0);
    assert_eq!((pruned_first.2, pruned_first.3), (0, 1));
    assert_eq!((active_first.2, active_first.3), (1, 0));
    assert_ne!(pruned_first.1, active_first.1);
}
