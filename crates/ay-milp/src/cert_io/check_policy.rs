// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn enforce_claim_policy(certificate: &Certificate, state: &mut CheckState) {
    let (required, forbidden): (&[&str], &[&str]) = match certificate.verdict.as_str() {
        "optimal" => (&["primal", "dual"], &["infeasible"]),
        "feasible" => (&["primal"], &["infeasible"]),
        "infeasible" => (&["infeasible"], &["primal", "dual"]),
        "unbounded" | "unknown" => (&[], &["primal", "dual", "infeasible"]),
        "bound" => (&["dual"], &["primal", "infeasible"]),
        other => {
            state.notes.push(format!(
                "UNRECOGNISED VERDICT `{other}` — this checker cannot determine what \
                 claims that verdict requires, so it refuses rather than passing it"
            ));
            state.demote(CheckStatus::Refuted);
            (&[], &[])
        }
    };
    for wanted in required {
        if !certificate.claims.iter().any(|claim| claim.name == *wanted) {
            state.notes.push(format!(
                "CLAIM-SET VIOLATION: verdict `{}` requires a `{wanted}` claim and the \
                 certificate carries none — a required claim is missing, which is a \
                 forged or truncated certificate, not an unproven one",
                certificate.verdict
            ));
            state.demote(CheckStatus::Refuted);
        }
    }
    for forbidden in forbidden {
        if certificate
            .claims
            .iter()
            .any(|claim| claim.name == *forbidden)
        {
            state.notes.push(format!(
                "CLAIM-SET VIOLATION: verdict `{}` cannot carry a `{forbidden}` claim — the \
                 certificate contradicts itself",
                certificate.verdict
            ));
            state.demote(CheckStatus::Refuted);
        }
    }
}

pub(super) fn append_metadata_notes(
    certificate: &Certificate,
    reports: &[ClaimReport],
    state: &mut CheckState,
) {
    if reports.is_empty() {
        state.notes.push(format!(
            "certificate carries NO claims (verdict `{}`) — nothing to verify",
            certificate.verdict
        ));
        state.demote(CheckStatus::Unverified);
    }
    for unchecked in &certificate.unchecked {
        state.notes.push(format!(
            "NOT VERIFIED (emitter marked unchecked): {unchecked}"
        ));
        state.demote(CheckStatus::Unverified);
    }
    for truncated in &certificate.truncated {
        state.notes.push(format!(
            "evidence dropped by the emitter's size cap: {truncated}"
        ));
    }
    if let Some(reason) = &certificate.reason {
        state.notes.push(format!("solver reason: {reason}"));
    }
}
