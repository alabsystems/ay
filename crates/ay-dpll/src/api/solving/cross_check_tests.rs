// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn run(label: &str, result: SolveResult, sat_model_validated: bool) -> CrossCheckRun {
    let unknown_reason = result.is_unknown().then(|| "unknown".to_string());
    CrossCheckRun {
        label: label.to_string(),
        result,
        verification: VerificationSummary {
            sat_model_validated,
            ..VerificationSummary::default()
        },
        unknown_reason,
    }
}

#[test]
fn cross_check_disagreement_ignores_unknown_and_rejected_sat() {
    let baseline = run("baseline", SolveResult::Unknown, false);
    let variants = vec![
        run("rejected_sat", SolveResult::Sat, false),
        run("unsat", SolveResult::unsat(), false),
    ];
    assert_eq!(find_disagreement(&baseline, &variants), None);

    let variants = vec![
        run("trusted_sat", SolveResult::Sat, true),
        run("trusted_unsat", SolveResult::unsat(), false),
    ];
    assert_eq!(
        find_disagreement(&baseline, &variants),
        Some(CrossCheckDisagreement {
            lhs_label: "trusted_sat".to_string(),
            rhs_label: "trusted_unsat".to_string(),
            lhs: SolveResult::Sat,
            rhs: SolveResult::unsat(),
        })
    );
}
