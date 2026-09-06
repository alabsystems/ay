// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::time::Duration;

use ay_chc::ChcParser;

use crate::invoke::{solve_with_proof_report, EncodeConfig, ProofMode};
use crate::query_proof_report::{
    QueryObligationBatchProofReport, QueryObligationBatchVerdict, QueryObligationProofReportRow,
};

const TWO_UNSAFE_QUERIES: &str = r#"
(set-logic HORN)
(declare-rel reached_p0 ())
(declare-rel reached_p1 ())
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(declare-rel error ())
(rule reached_p0)
(rule reached_p1)
(rule (=> reached_p0 error_p0))
(rule (=> reached_p1 error_p1))
(rule (=> error_p0 error))
(rule (=> error_p1 error))
(query error)
"#;

#[test]
fn later_checked_refutation_can_admit_unsafe_batch() {
    let problem = ChcParser::parse(TWO_UNSAFE_QUERIES).expect("fixture should parse");
    let normalized = problem.normalized_input();
    let obligations = problem
        .query_obligations()
        .expect("fixture should split into two obligations");
    let ids: Vec<_> = obligations
        .iter()
        .map(|obligation| obligation.id().clone())
        .collect();
    let config = EncodeConfig::new()
        .with_proof_mode(ProofMode::Strict)
        .with_timeout(Duration::from_secs(10));
    let rows = obligations
        .into_iter()
        .enumerate()
        .map(|(index, obligation)| {
            let (id, problem) = obligation.into_parts();
            let report = solve_with_proof_report(problem, &config)
                .expect("unsafe obligation should produce a proof report");
            assert!(report.proof_run().result().is_unsafe());
            let report = if index == 1 {
                report.with_checked_replay(Duration::from_secs(10))
            } else {
                report
            };
            QueryObligationProofReportRow::new(id, Ok(report))
        })
        .collect();
    let report =
        QueryObligationBatchProofReport::new(normalized, &[], false, &ids, rows, Duration::ZERO)
            .expect("complete source-ordered rows should form a batch");

    assert_eq!(
        report.verdict(),
        QueryObligationBatchVerdict::Unsafe {
            first_refuting_row: 0
        }
    );
    assert!(report.accepted_as_proof());
    assert!(report.trust_full_verifier_admissible());
    assert!(report.rows()[0].checked_replay().is_none());
    assert!(report.rows()[1].checked_replay().is_some());
    let json = report.to_json_value();
    assert_eq!(json["rows"][0]["trust_full_verifier_admissible"], false);
    assert_eq!(json["rows"][1]["trust_full_verifier_admissible"], true);
    assert_eq!(json["trust_full_verifier_admissible"], true);
}

#[test]
fn checked_bundle_survives_report_and_repeated_attachment_is_a_noop() {
    let obligation = ChcParser::parse(TWO_UNSAFE_QUERIES)
        .expect("fixture should parse")
        .query_obligations()
        .expect("fixture should split")
        .into_iter()
        .next()
        .expect("one obligation should survive");
    let config = EncodeConfig::new()
        .with_proof_mode(ProofMode::Strict)
        .with_timeout(Duration::from_secs(10));
    let report = solve_with_proof_report(obligation.into_parts().1, &config)
        .expect("unsafe obligation should produce a proof report")
        .with_checked_replay(Duration::ZERO);
    assert!(report.proof_run().result().is_unsafe());
    assert!(report.checked_replay().is_none());

    let report = report.with_checked_replay(Duration::from_secs(10));
    let elapsed = report.budget_report().total_elapsed;
    let checked_sha256 = report
        .checked_replay()
        .expect("successful replay must retain its sealed artifact bundle")
        .summary()
        .identity_sha256();
    let report = report.with_checked_replay(Duration::ZERO);
    assert_eq!(report.budget_report().total_elapsed, elapsed);
    assert_eq!(
        report
            .checked_replay()
            .expect("repeated attachment must preserve the first bundle")
            .summary()
            .identity_sha256(),
        checked_sha256
    );
    let (run, _, _, _, _) = report.into_parts();
    assert!(run.metadata().trust_full_verifier_admissible());
}
