// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn enforce_claim_policy(certificate: &Certificate, state: &mut CheckState) {
    // NO CLAIM MAY SHADOW ANOTHER'S NAME. This is checked before anything about
    // what the claims say, because it is not about what they prove: a name that
    // strictly extends a known name makes the shorter name's grep signature
    // match the longer name's line on all three surfaces that publish a
    // standing (see `CLAIM_NAMES`), so admitting one lets a hand-written
    // certificate answer a question about `dual` with a record about something
    // else. Our own emitter cannot produce one; this closes the same door for
    // certificates we did not write.
    for claim in &certificate.claims {
        if claim_name_shadows_another(&claim.name) {
            state.notes.push(format!(
                "CLAIM-NAME VIOLATION: `{}` extends a claim name this format already uses — \
                 every line that reports a claim's standing delimits the name only by what \
                 follows it, so this record would answer a query about the shorter name; it is \
                 refused rather than reported",
                claim.name
            ));
            state.demote(CheckStatus::Refuted);
        }
    }
    // `objbound` is ALLOWED on `optimal` and FORBIDDEN everywhere else. It is a
    // residual against a claimed optimum, so a verdict that names no optimum has
    // nothing for it to be a residual against, and a certificate carrying one
    // anyway is malformed rather than merely unproved.
    let (required, forbidden): (&[&str], &[&str]) = match certificate.verdict.as_str() {
        "optimal" => (&["primal", "dual"], &["infeasible"]),
        "feasible" => (&["primal"], &["infeasible", "objbound"]),
        "infeasible" => (&["infeasible"], &["primal", "dual", "objbound"]),
        "unbounded" | "unknown" => (&[], &["primal", "dual", "infeasible", "objbound"]),
        "bound" => (&["dual"], &["primal", "infeasible", "objbound"]),
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
