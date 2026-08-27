// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbLit, PbTerm};

type TestChecker = fn(&PbInstance, &PbObjective, i128, u64) -> OptimalityCheck;

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit(var)],
    }
}

fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn instance() -> PbInstance {
    // min x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 2   (optimum = 2)
    PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge(vec![term(1, 1), term(1, 2), term(1, 3)], 2)],
        objective: Some(PbObjective {
            terms: vec![term(1, 1), term(1, 2), term(1, 3)],
        }),
    }
}

fn overflowing_objective_instance() -> PbInstance {
    PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![ge(vec![term(1, 1)], 1), ge(vec![term(1, 2)], 1)],
        objective: Some(PbObjective {
            terms: vec![term(i128::MAX, 1), term(1, 2)],
        }),
    }
}

fn transiently_overflowing_objective_instance() -> PbInstance {
    PbInstance {
        num_vars: 3,
        num_constraints: 3,
        constraints: vec![
            ge(vec![term(1, 1)], 1),
            ge(vec![term(1, 2)], 1),
            ge(vec![term(1, 3)], 1),
        ],
        objective: Some(PbObjective {
            terms: vec![term(i128::MAX, 1), term(1, 2), term(-1, 3)],
        }),
    }
}

fn minimum_objective_instance() -> PbInstance {
    PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![ge(vec![term(1, 1)], 1), ge(vec![term(1, 2)], 1)],
        objective: Some(PbObjective {
            terms: vec![term(-i128::MAX, 1), term(-1, 2)],
        }),
    }
}

fn confirmed(
    _instance: &PbInstance,
    _objective: &PbObjective,
    _claimed: i128,
    _timeout_secs: u64,
) -> OptimalityCheck {
    OptimalityCheck::Confirmed
}

fn refuted(
    _instance: &PbInstance,
    _objective: &PbObjective,
    _claimed: i128,
    _timeout_secs: u64,
) -> OptimalityCheck {
    OptimalityCheck::Refuted("better model found".to_string())
}

fn skipped(
    _instance: &PbInstance,
    _objective: &PbObjective,
    _claimed: i128,
    _timeout_secs: u64,
) -> OptimalityCheck {
    OptimalityCheck::Skipped("checker unavailable".to_string())
}

fn inconclusive(
    _instance: &PbInstance,
    _objective: &PbObjective,
    _claimed: i128,
    _timeout_secs: u64,
) -> OptimalityCheck {
    OptimalityCheck::Inconclusive("checker returned unknown".to_string())
}

fn not_applicable(
    _instance: &PbInstance,
    _objective: &PbObjective,
    _claimed: i128,
    _timeout_secs: u64,
) -> OptimalityCheck {
    OptimalityCheck::NotApplicable
}

fn verify_with(
    instance: &PbInstance,
    text: &str,
    mode: Z3Mode,
    checker: TestChecker,
) -> VerifyReport {
    let output = parse_solver_output(text, instance.num_vars);
    report::verify_with_checker(instance, &output, mode, 10, checker)
}

#[test]
fn parses_multi_vline_and_objective() {
    let output = "c hi\no 5\no 2\ns OPTIMUM FOUND\nv x1 -x2\nv x3\n";
    let parsed = parse_solver_output(output, 3);
    assert_eq!(parsed.status.as_deref(), Some("OPTIMUM FOUND"));
    assert_eq!(parsed.objective, Some(2));
    assert!(parsed.has_model);
    assert_eq!(parsed.assignment, vec![true, false, true]);
}

#[test]
fn out_of_range_model_token_neither_grows_assignment_nor_grants_authority() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![ge(vec![term(1, 1)], 1)],
        objective: None,
    };
    let output = parse_solver_output("s SATISFIABLE\nv x4294967295\n", instance.num_vars);
    assert_eq!(output.assignment, vec![false]);

    let report = verify(&instance, &output, Z3Mode::Off, 10);
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Rejected(VerificationFailure::InfeasibleModel)
    );
}

#[test]
fn feasible_sat_model_is_fully_verified_without_z3() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "s SATISFIABLE\nv x1 x2 -x3\n",
        Z3Mode::Off,
        confirmed,
    );
    assert_eq!(report.verdict(), VerificationVerdict::VerifiedSatisfiable);
    assert!(report.is_verified());
    assert!(report.checked_model());
    assert_eq!(report.status(), Some("SATISFIABLE"));
    assert_eq!(report.total_constraints(), 1);
    assert_eq!(report.violated_constraints(), 0);
    assert_eq!(report.claimed_objective(), None);
    assert_eq!(report.computed_objective(), Some(2));
    assert_eq!(report.objective_matches(), None);
    assert_eq!(report.optimality(), &OptimalityCheck::NotApplicable);
}

#[test]
fn model_bearing_status_without_model_is_rejected() {
    let instance = instance();
    let report = verify_with(&instance, "s SATISFIABLE\n", Z3Mode::Off, confirmed);
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Rejected(VerificationFailure::MissingModel)
    );
    assert!(!report.checked_model());
    assert!(!report.is_verified());
}

#[test]
fn infeasible_model_is_rejected() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "o 1\ns SATISFIABLE\nv x1 -x2 -x3\n",
        Z3Mode::Off,
        confirmed,
    );
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Rejected(VerificationFailure::InfeasibleModel)
    );
    assert_eq!(report.violated_constraints(), 1);
}

#[test]
fn objective_mismatch_is_rejected() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "o 1\ns OPTIMUM FOUND\nv x1 x2 -x3\n",
        Z3Mode::Off,
        confirmed,
    );
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Rejected(VerificationFailure::ObjectiveMismatch)
    );
    assert_eq!(report.objective_matches(), Some(false));
}

#[test]
fn overflowing_model_objective_is_rejected_instead_of_saturating_to_claim() {
    let instance = overflowing_objective_instance();
    let output = parse_solver_output(
        "o 170141183460469231731687303715884105727\ns OPTIMUM FOUND\nv x1 x2\n",
        instance.num_vars,
    );
    let report = verify(&instance, &output, Z3Mode::Off, 10);
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Rejected(VerificationFailure::ObjectiveOverflow)
    );
    assert_eq!(report.computed_objective(), None);
    assert_eq!(report.objective_matches(), None);
    assert!(report
        .messages()
        .iter()
        .any(|message| message.contains("OBJECTIVE OVERFLOW")));
}

#[test]
fn overflowing_incidental_objective_does_not_disprove_sat_claim() {
    let instance = overflowing_objective_instance();
    let output = parse_solver_output("s SATISFIABLE\nv x1 x2\n", instance.num_vars);
    let report = verify(&instance, &output, Z3Mode::Off, 10);
    assert_eq!(report.verdict(), VerificationVerdict::VerifiedSatisfiable);
    assert_eq!(report.computed_objective(), None);
    assert_eq!(report.objective_matches(), None);
}

#[test]
fn public_verify_accepts_exact_final_sum_after_transient_overflow() {
    let instance = transiently_overflowing_objective_instance();
    let output = parse_solver_output(
        "o 170141183460469231731687303715884105727\ns SATISFIABLE\nv x1 x2 x3\n",
        instance.num_vars,
    );
    let report = verify(&instance, &output, Z3Mode::Off, 10);
    assert_eq!(report.verdict(), VerificationVerdict::VerifiedSatisfiable);
    assert_eq!(report.computed_objective(), Some(i128::MAX));
    assert_eq!(report.objective_matches(), Some(true));
}

#[test]
fn public_verify_rejects_minimum_strict_improvement_bound() {
    let instance = minimum_objective_instance();
    let output = parse_solver_output(
        "o -170141183460469231731687303715884105728\ns OPTIMUM FOUND\nv x1 x2\n",
        instance.num_vars,
    );
    let report = verify(&instance, &output, Z3Mode::Off, 10);
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Unverified(UnverifiedReason::OptimalityBoundOutOfRange)
    );
    assert_eq!(report.computed_objective(), Some(i128::MIN));
    assert_eq!(report.objective_matches(), Some(true));
    assert!(matches!(
        report.optimality(),
        OptimalityCheck::Inconclusive(_)
    ));
}

#[test]
fn non_model_claims_are_never_verification_passes() {
    let instance = instance();
    for (output, reason) in [
        ("", UnverifiedReason::MissingStatus),
        ("s UNKNOWN\n", UnverifiedReason::UnknownStatus),
        (
            "s UNSATISFIABLE\n",
            UnverifiedReason::UnsatisfiableWithoutProof,
        ),
        ("s UNSUPPORTED\n", UnverifiedReason::UnsupportedStatus),
    ] {
        let report = verify_with(&instance, output, Z3Mode::Off, confirmed);
        assert_eq!(
            report.verdict(),
            VerificationVerdict::Unverified(reason),
            "output: {output:?}"
        );
        assert!(!report.is_verified(), "output: {output:?}");
        assert!(!report.messages().is_empty(), "output: {output:?}");
    }
}

#[test]
fn optimum_without_claimed_objective_is_unverified() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "s OPTIMUM FOUND\nv x1 x2 -x3\n",
        Z3Mode::Auto,
        confirmed,
    );
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Unverified(UnverifiedReason::MissingClaimedObjective)
    );
    assert_eq!(
        report.optimality(),
        &OptimalityCheck::Skipped("no claimed objective".to_string())
    );
}

#[test]
fn optimum_for_instance_without_objective_is_unverified() {
    let mut decision_instance = instance();
    decision_instance.objective = None;
    let report = verify_with(
        &decision_instance,
        "o 0\ns OPTIMUM FOUND\nv x1 x2 -x3\n",
        Z3Mode::Auto,
        confirmed,
    );
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Unverified(UnverifiedReason::MissingInstanceObjective)
    );
}

#[test]
fn disabled_optimality_check_is_unverified() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n",
        Z3Mode::Off,
        confirmed,
    );
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Unverified(UnverifiedReason::OptimalityCheckSkipped)
    );
    assert!(report.verdict().is_unverified());
}

#[test]
fn skipped_or_inconclusive_optimality_is_unverified_in_every_enabled_mode() {
    let instance = instance();
    let output = "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n";
    for mode in [Z3Mode::Auto, Z3Mode::Require] {
        let skipped_report = verify_with(&instance, output, mode, skipped);
        assert_eq!(
            skipped_report.verdict(),
            VerificationVerdict::Unverified(UnverifiedReason::OptimalityCheckSkipped)
        );
        let inconclusive_report = verify_with(&instance, output, mode, inconclusive);
        assert_eq!(
            inconclusive_report.verdict(),
            VerificationVerdict::Unverified(UnverifiedReason::OptimalityCheckInconclusive)
        );
    }
}

#[test]
fn confirmed_optimum_is_fully_verified() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n",
        Z3Mode::Auto,
        confirmed,
    );
    assert_eq!(report.verdict(), VerificationVerdict::VerifiedOptimal);
    assert_eq!(report.optimality(), &OptimalityCheck::Confirmed);
    assert!(report.is_verified());
}

#[test]
fn refuted_optimum_is_rejected() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n",
        Z3Mode::Auto,
        refuted,
    );
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Rejected(VerificationFailure::OptimalityRefuted)
    );
    assert!(report.verdict().is_rejected());
}

#[test]
fn inapplicable_optimality_response_fails_closed() {
    let instance = instance();
    let report = verify_with(
        &instance,
        "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n",
        Z3Mode::Auto,
        not_applicable,
    );
    assert_eq!(
        report.verdict(),
        VerificationVerdict::Unverified(UnverifiedReason::OptimalityCheckInconclusive)
    );
}

#[test]
fn smt2_encodes_constraint_and_bound() {
    let instance = instance();
    let smt = emit_smt2_better_than(&instance, instance.objective.as_ref().unwrap(), 2).unwrap();
    assert!(smt.contains("(declare-const x1 Int)"));
    assert!(smt.contains("(assert (<= x1 1))"));
    assert!(smt.contains("(set-logic QF_LIA)"));
    assert!(smt.contains("(>= (+ "));
    assert!(smt.contains("(<= (+ "));
    assert!(smt.contains("(check-sat)"));
}

#[test]
fn smt2_rejects_minimum_claim_without_subtracting() {
    let instance = minimum_objective_instance();
    assert!(
        emit_smt2_better_than(&instance, instance.objective.as_ref().unwrap(), i128::MIN).is_none()
    );
}

#[test]
fn int_smt_handles_negatives() {
    assert_eq!(int_smt(5), "5");
    assert_eq!(int_smt(-5), "(- 5)");
    assert_eq!(int_smt(0), "0");
}
