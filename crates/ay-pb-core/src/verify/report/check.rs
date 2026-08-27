// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{UnverifiedReason, VerificationFailure, VerificationVerdict, VerifyReport};
use crate::solver::{eval_constraint, eval_objective_exact, ObjectiveEvalError};
use crate::types::{PbInstance, PbObjective};
use crate::verify::{OptimalityCheck, SolverOutput, Z3Mode};

type OptimalityChecker = fn(&PbInstance, &PbObjective, i128, u64) -> OptimalityCheck;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SolverClaim<'a> {
    Satisfiable,
    Optimal,
    Unsatisfiable,
    Unknown,
    Missing,
    Unsupported(&'a str),
}

impl<'a> SolverClaim<'a> {
    fn from_status(status: Option<&'a str>) -> Self {
        match status {
            Some(value) if value.eq_ignore_ascii_case("SATISFIABLE") => Self::Satisfiable,
            Some(value) if value.eq_ignore_ascii_case("OPTIMUM FOUND") => Self::Optimal,
            Some(value) if value.eq_ignore_ascii_case("UNSATISFIABLE") => Self::Unsatisfiable,
            Some(value) if value.eq_ignore_ascii_case("UNKNOWN") => Self::Unknown,
            Some(value) => Self::Unsupported(value),
            None => Self::Missing,
        }
    }
}

struct ModelAssessment {
    checked_model: bool,
    violated_constraints: usize,
    computed_objective: Option<i128>,
    objective_matches: Option<bool>,
    failure: Option<VerificationFailure>,
    messages: Vec<String>,
}

pub(in crate::verify) fn verify_with_checker(
    instance: &PbInstance,
    output: &SolverOutput,
    z3: Z3Mode,
    timeout_secs: u64,
    checker: OptimalityChecker,
) -> VerifyReport {
    match SolverClaim::from_status(output.status.as_deref()) {
        SolverClaim::Satisfiable => verify_model_claim(
            instance,
            output,
            SolverClaim::Satisfiable,
            z3,
            timeout_secs,
            checker,
        ),
        SolverClaim::Optimal => verify_model_claim(
            instance,
            output,
            SolverClaim::Optimal,
            z3,
            timeout_secs,
            checker,
        ),
        SolverClaim::Unsatisfiable => unverified_report(
            instance,
            output,
            UnverifiedReason::UnsatisfiableWithoutProof,
            "status UNSATISFIABLE has no independently checked proof".to_string(),
        ),
        SolverClaim::Unknown => unverified_report(
            instance,
            output,
            UnverifiedReason::UnknownStatus,
            "status UNKNOWN does not claim a checkable result".to_string(),
        ),
        SolverClaim::Missing => unverified_report(
            instance,
            output,
            UnverifiedReason::MissingStatus,
            "no solver status was reported; nothing was verified".to_string(),
        ),
        SolverClaim::Unsupported(value) => unverified_report(
            instance,
            output,
            UnverifiedReason::UnsupportedStatus,
            format!("unsupported solver status `{value}`; nothing was verified"),
        ),
    }
}

fn verify_model_claim(
    instance: &PbInstance,
    output: &SolverOutput,
    claim: SolverClaim<'_>,
    z3: Z3Mode,
    timeout_secs: u64,
    checker: OptimalityChecker,
) -> VerifyReport {
    let mut assessment = assess_model(instance, output);
    let (optimality, verdict) = match assessment.failure {
        Some(failure) => (
            OptimalityCheck::NotApplicable,
            VerificationVerdict::Rejected(failure),
        ),
        None if claim == SolverClaim::Satisfiable => (
            OptimalityCheck::NotApplicable,
            VerificationVerdict::VerifiedSatisfiable,
        ),
        None => assess_optimality(
            instance,
            output,
            z3,
            timeout_secs,
            checker,
            &mut assessment.messages,
        ),
    };
    report_from_assessment(instance, output, assessment, optimality, verdict)
}

fn assess_model(instance: &PbInstance, output: &SolverOutput) -> ModelAssessment {
    let total_constraints = instance.constraints.len();
    if !output.has_model {
        return ModelAssessment {
            checked_model: false,
            violated_constraints: 0,
            computed_objective: None,
            objective_matches: None,
            failure: Some(VerificationFailure::MissingModel),
            messages: vec!["status claims a model but no `v` line was present".to_string()],
        };
    }

    let violated_constraints = instance
        .constraints
        .iter()
        .filter(|constraint| !eval_constraint(constraint, &output.assignment))
        .count();
    let mut failure = (violated_constraints > 0).then_some(VerificationFailure::InfeasibleModel);
    let mut messages = if violated_constraints == 0 {
        vec![format!(
            "model feasible: {total_constraints}/{total_constraints} constraints satisfied"
        )]
    } else {
        vec![format!(
            "MODEL INFEASIBLE: {violated_constraints}/{total_constraints} constraints violated"
        )]
    };

    let (computed_objective, objective_matches) =
        assess_objective(instance, output, &mut failure, &mut messages);
    ModelAssessment {
        checked_model: true,
        violated_constraints,
        computed_objective,
        objective_matches,
        failure,
        messages,
    }
}

fn assess_objective(
    instance: &PbInstance,
    output: &SolverOutput,
    failure: &mut Option<VerificationFailure>,
    messages: &mut Vec<String>,
) -> (Option<i128>, Option<bool>) {
    let Some(objective) = instance.objective.as_ref() else {
        return (None, None);
    };
    let computed = match eval_objective_exact(objective, &output.assignment) {
        Ok(value) => value,
        Err(ObjectiveEvalError::Overflow) => {
            if output.objective.is_some() {
                messages.push(
                    "OBJECTIVE OVERFLOW: claimed objective cannot equal the model's exact value, which is outside the i128 verification range"
                        .to_string(),
                );
                if failure.is_none() {
                    *failure = Some(VerificationFailure::ObjectiveOverflow);
                }
            } else {
                messages.push(
                    "objective not reported; model objective is outside the i128 reporting range"
                        .to_string(),
                );
            }
            return (None, None);
        }
    };
    let Some(claimed) = output.objective else {
        messages.push(format!(
            "objective not reported on an `o` line; model attains {computed}"
        ));
        return (Some(computed), None);
    };
    let matches = computed == claimed;
    if matches {
        messages.push(format!(
            "objective consistent: claimed = computed = {claimed}"
        ));
    } else {
        messages.push(format!(
            "OBJECTIVE MISMATCH: claimed o {claimed}, model attains {computed}"
        ));
        if failure.is_none() {
            *failure = Some(VerificationFailure::ObjectiveMismatch);
        }
    }
    (Some(computed), Some(matches))
}

fn assess_optimality(
    instance: &PbInstance,
    output: &SolverOutput,
    z3: Z3Mode,
    timeout_secs: u64,
    checker: OptimalityChecker,
    messages: &mut Vec<String>,
) -> (OptimalityCheck, VerificationVerdict) {
    let Some(claimed) = output.objective else {
        return unverified_optimality(
            "no claimed objective",
            UnverifiedReason::MissingClaimedObjective,
            messages,
        );
    };
    let Some(objective) = instance.objective.as_ref() else {
        return unverified_optimality(
            "instance has no objective",
            UnverifiedReason::MissingInstanceObjective,
            messages,
        );
    };
    if claimed.checked_sub(1).is_none() {
        let detail = "claimed objective is i128::MIN; its strict improvement bound is outside the i128 verification range";
        messages.push(format!("optimality unconfirmed (z3): {detail}"));
        return (
            OptimalityCheck::Inconclusive(detail.to_string()),
            VerificationVerdict::Unverified(UnverifiedReason::OptimalityBoundOutOfRange),
        );
    }
    if z3 == Z3Mode::Off {
        return unverified_optimality(
            "z3 check disabled (--no-z3)",
            UnverifiedReason::OptimalityCheckSkipped,
            messages,
        );
    }

    let optimality = checker(instance, objective, claimed, timeout_secs);
    let verdict = match &optimality {
        OptimalityCheck::Confirmed => {
            messages.push(format!(
                "independent optimality (z3): no feasible solution beats {claimed} → OPTIMUM CONFIRMED"
            ));
            VerificationVerdict::VerifiedOptimal
        }
        OptimalityCheck::Refuted(detail) => {
            messages.push(format!("UNSOUND OPTIMUM (z3): {detail}"));
            VerificationVerdict::Rejected(VerificationFailure::OptimalityRefuted)
        }
        OptimalityCheck::Inconclusive(detail) => {
            messages.push(format!("optimality unconfirmed (z3): {detail}"));
            VerificationVerdict::Unverified(UnverifiedReason::OptimalityCheckInconclusive)
        }
        OptimalityCheck::Skipped(detail) => {
            messages.push(format!("optimality not checked: {detail}"));
            VerificationVerdict::Unverified(UnverifiedReason::OptimalityCheckSkipped)
        }
        OptimalityCheck::NotApplicable => {
            messages.push("optimality checker returned no applicable result".to_string());
            VerificationVerdict::Unverified(UnverifiedReason::OptimalityCheckInconclusive)
        }
    };
    (optimality, verdict)
}

fn unverified_optimality(
    detail: &str,
    reason: UnverifiedReason,
    messages: &mut Vec<String>,
) -> (OptimalityCheck, VerificationVerdict) {
    messages.push(format!("optimality not checked: {detail}"));
    (
        OptimalityCheck::Skipped(detail.to_string()),
        VerificationVerdict::Unverified(reason),
    )
}

fn unverified_report(
    instance: &PbInstance,
    output: &SolverOutput,
    reason: UnverifiedReason,
    message: String,
) -> VerifyReport {
    VerifyReport {
        status: output.status.clone(),
        checked_model: false,
        total_constraints: instance.constraints.len(),
        violated_constraints: 0,
        claimed_objective: output.objective,
        computed_objective: None,
        objective_matches: None,
        optimality: OptimalityCheck::NotApplicable,
        verdict: VerificationVerdict::Unverified(reason),
        messages: vec![message],
    }
}

fn report_from_assessment(
    instance: &PbInstance,
    output: &SolverOutput,
    assessment: ModelAssessment,
    optimality: OptimalityCheck,
    verdict: VerificationVerdict,
) -> VerifyReport {
    VerifyReport {
        status: output.status.clone(),
        checked_model: assessment.checked_model,
        total_constraints: instance.constraints.len(),
        violated_constraints: assessment.violated_constraints,
        claimed_objective: output.objective,
        computed_objective: assessment.computed_objective,
        objective_matches: assessment.objective_matches,
        optimality,
        verdict,
        messages: assessment.messages,
    }
}
