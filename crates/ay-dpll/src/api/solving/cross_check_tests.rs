// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn run(
    label: &str,
    result: SolveResult,
    sat_model_validated: bool,
    unsat_proof_strictly_verified: bool,
) -> CrossCheckRun {
    let unknown_reason = result.is_unknown().then(|| "unknown".to_string());
    CrossCheckRun {
        label: label.to_string(),
        result,
        verification: VerificationSummary {
            sat_model_validated,
            unsat_proof_strictly_verified,
            ..VerificationSummary::default()
        },
        unknown_reason,
    }
}

#[test]
fn cross_check_disagreement_ignores_unknown_and_rejected_sat() {
    let baseline = run("baseline", SolveResult::Unknown, false, false);
    let variants = vec![
        run("rejected_sat", SolveResult::Sat, false, false),
        run("uncertified_unsat", SolveResult::unsat(), false, false),
    ];
    assert_eq!(find_disagreement(&baseline, &variants), None);

    let variants = vec![
        run("trusted_sat", SolveResult::Sat, true, false),
        run("trusted_unsat", SolveResult::unsat(), false, true),
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

#[test]
fn cross_check_plain_unsat_crosses_strict_authored_boundary() {
    let report = Solver::cross_check_smtlib2(
        "(set-logic QF_LIA) (declare-const x Int) (assert (< x x)) (check-sat)",
        &[],
    )
    .expect("cross-check script");

    assert!(report.baseline.result.is_unsat());
    assert!(report.baseline.verification.unsat_proof_strictly_verified);
    assert!(accepted_definite_result(&report.baseline).is_some());
}

#[test]
fn cross_check_assumption_unsat_crosses_strict_authored_boundary() {
    let report = Solver::cross_check_smtlib2(
        "(set-logic QF_LIA) (declare-const p Bool) (assert (not p)) \
         (check-sat-assuming (p))",
        &[],
    )
    .expect("cross-check assumption script");

    assert!(report.baseline.result.is_unsat());
    assert!(report.baseline.verification.unsat_proof_strictly_verified);
    assert!(accepted_definite_result(&report.baseline).is_some());
}

#[test]
fn cross_check_exact_exists_unsat_preserves_semantic_admission_class() {
    let report = Solver::cross_check_smtlib2(
        "(set-logic LIA) (declare-const y Int) \
         (assert (exists ((x Int)) (and (> x y) (< x (+ y 1))))) (check-sat)",
        &[],
    )
    .expect("cross-check exact-exists script");

    assert!(report.baseline.result.is_unsat());
    assert!(!report.baseline.verification.unsat_proof_strictly_verified);
    assert!(!report.baseline.verification.unsat_independently_verified);
    assert!(
        report
            .baseline
            .verification
            .unsat_exact_semantically_verified
    );
    assert!(accepted_definite_result(&report.baseline).is_some());
}

#[test]
fn cross_check_rejects_stateful_commands_after_solve() {
    for suffix in [
        "(reset) (assert true)",
        "(push 1) (assert true)",
        "(assert true)",
    ] {
        let input = format!("(assert false) (check-sat) {suffix}");
        let error = Solver::cross_check_smtlib2(&input, &[])
            .expect_err("post-solve state mutation must be rejected, not reordered");
        assert!(
            matches!(
                &error,
                SolverError::InvalidArgument { operation, message }
                    if *operation == CROSS_CHECK_OPERATION
                        && message.contains("commands after check-sat")
            ),
            "unexpected error for suffix {suffix}: {error:?}"
        );
    }
}
