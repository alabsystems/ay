// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct ClaimReportSeal {
    _private: (),
}

impl ClaimReportSeal {
    fn new() -> Self {
        Self { _private: () }
    }
}

pub(super) fn check_claims(
    certificate: &Certificate,
    model: &Model,
    claimed_value: Option<&BigRational>,
    affine: Option<&Result<AffineAggregationVerification, AffineAggregationCertificateError>>,
    state: &mut CheckState,
) -> Vec<ClaimReport> {
    let mut reports = Vec::new();
    for claim in &certificate.claims {
        let (verified, detail) = check_claim(certificate, model, claimed_value, affine, claim);
        let report = ClaimReport::new(
            ClaimReportSeal::new(),
            claim.name.clone(),
            claim.kind,
            verified,
            detail,
        );
        if !report.is_verified() {
            state.demote(if claim.kind == EvidenceKind::Succinct {
                CheckStatus::Refuted
            } else {
                CheckStatus::Unverified
            });
        }
        reports.push(report);
    }
    reports
}

fn check_claim(
    certificate: &Certificate,
    model: &Model,
    claimed_value: Option<&BigRational>,
    affine: Option<&Result<AffineAggregationVerification, AffineAggregationCertificateError>>,
    claim: &ParsedClaim,
) -> (bool, String) {
    match (claim.name.as_str(), claim.kind) {
        ("primal", EvidenceKind::Succinct) => check_primal(
            certificate,
            model,
            claimed_value,
            certificate.verdict == "optimal" || certificate.verdict == "feasible",
        ),
        ("dual", EvidenceKind::Succinct) => check_dual(
            certificate,
            model,
            claimed_value,
            claim.source.as_deref(),
            affine,
        ),
        ("infeasible", EvidenceKind::Succinct) => {
            check_infeasible(certificate, model, claim.source.as_deref(), affine)
        }
        (_, EvidenceKind::Succinct) => (
            false,
            format!("no independent check exists for claim `{}`", claim.name),
        ),
        (_, EvidenceKind::Replay) => replay_detail(certificate, claim),
        (_, EvidenceKind::None) => none_detail(claim),
    }
}

fn replay_detail(certificate: &Certificate, claim: &ParsedClaim) -> (bool, String) {
    let source = claim.source.clone().unwrap_or_default();
    let replay = certificate
        .replay
        .iter()
        .find(|replay| replay.claim == source);
    let tcb = replay.map_or("<unnamed>", |replay| replay.tcb.as_str());
    let nondeterminism = replay.map_or_else(String::new, |replay| replay.nondeterminism.join(","));
    let suffix = if nondeterminism.is_empty() {
        String::new()
    } else {
        format!("; nondeterminism: {nondeterminism}")
    };
    (
        false,
        format!(
            "NOT VERIFIED — this claim has no exported object. Re-verification means \
             RE-RUNNING the solver ({source}); the trusted computing base is {tcb}{suffix}. \
             This checker did not check it and does not vouch for it."
        ),
    )
}

fn none_detail(claim: &ParsedClaim) -> (bool, String) {
    let why = match claim.source.as_deref() {
        Some("trivial-optcert") => {
            " (legacy emitter metadata downgraded an empty-multiplier zero-objective bound; \
             current emitters export that exact bound as SUCCINCT optcert)"
        }
        Some("truncated") => " (the backing block exceeded the emitter's size cap)",
        _ => "",
    };
    (
        false,
        format!("NOT VERIFIED — no evidence of any kind was exported{why}"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replay_and_none_reports_cannot_become_verified() {
        for kind in [EvidenceKind::Replay, EvidenceKind::None] {
            let report = ClaimReport::new(
                ClaimReportSeal::new(),
                "claim".to_owned(),
                kind,
                true,
                "unchecked".to_owned(),
            );
            assert!(!report.is_verified());
            assert_eq!(report.standing(), ClaimStanding::Unbacked);
        }
    }
}
