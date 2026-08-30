// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// EVERY claim name this format uses. **The list is PREFIX-FREE, and that is a
/// reporting-soundness property, not a style rule.**
///
/// A claim's standing is published on three LINE-ORIENTED surfaces: the
/// artifact's `evidence <name> <kind> <source>` record, `verify`'s
/// `claim <name> …` report line, and the comma-joined
/// `CLAIMS verified=… refuted=… unbacked=…` census that
/// [`CheckReport::census`] documents as a "grep-able line". On all three a
/// name is delimited only by what FOLLOWS it, so if one name extends another
/// then the shorter name's signature matches the longer name's line and a
/// consumer that asks for a claim by name is answered about a different claim.
///
/// The failure this list exists to stop was MEASURED, not imagined. A root LP
/// bound first shipped under the claim name `dualbound`, and the census of a
/// certificate whose optimum is NOT proved --
/// `CLAIMS verified=primal,dualbound refuted=- unbacked=dual` -- matched
/// `CLAIMS verified=primal,dual`, which
/// the development design notes records as the
/// signature of a PROVED optimum. A primal-only certificate could present as
/// dual-verified to the exact reader this line is written for. The claim is
/// `objbound` because a bound on the objective is what it is and because that
/// token extends nothing here.
pub(super) const CLAIM_NAMES: &[&str] = &[
    "primal",
    "dual",
    "objbound",
    "infeasible",
    // A bare label on an `unbounded` verdict, with no object to re-derive. It
    // still lands on the three surfaces above, so it still owes the
    // prefix-freeness the rest owe.
    "unbounded",
];

/// Whether `name` strictly extends some name in [`CLAIM_NAMES`] -- i.e.
/// whether admitting it would break the prefix-freeness the three reporting
/// surfaces rely on. [`enforce_claim_policy`] REFUSES a certificate carrying
/// such a name.
pub(super) fn claim_name_shadows_another(name: &str) -> bool {
    CLAIM_NAMES
        .iter()
        .any(|&known| name != known && name.starts_with(known))
}

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
        // A SEPARATE ARM FROM `dual`, deliberately, and a NON-EXTENDING NAME,
        // just as deliberately. Routing a root bound through `check_dual` would
        // make one function answer two different questions ("is this THE
        // optimum" and "is this A bound"), and the first thing such a function
        // loses is the ability to keep their answers apart; naming it
        // `dualbound` kept the answers apart inside the checker and merged them
        // again on every line the checker prints (see [`CLAIM_NAMES`]).
        ("objbound", EvidenceKind::Succinct) => check_dual_bound(certificate, model, claimed_value),
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

    /// THE INVARIANT THE CENSUS LINE RESTS ON.
    ///
    /// Mutating `objbound` back to the `dualbound` this lane first shipped
    /// turns this test RED, which is the whole point: the property is not "we
    /// picked a tidy name", it is "no name in this vocabulary can answer for
    /// another".
    #[test]
    fn no_claim_name_extends_another() {
        for &outer in CLAIM_NAMES {
            for &inner in CLAIM_NAMES {
                assert!(
                    outer == inner || !outer.starts_with(inner),
                    "`{outer}` extends `{inner}`: every surface that reports a claim's standing \
                     delimits the name only by what follows it, so a query for `{inner}` would \
                     match a `{outer}` line and read one claim's standing as another's"
                );
            }
        }
    }

    /// The shadow guard must fire on the exact name that caused the defect and
    /// must NOT fire on the vocabulary itself.
    #[test]
    fn the_shadow_guard_names_the_defect_it_was_written_for() {
        assert!(claim_name_shadows_another("dualbound"));
        assert!(claim_name_shadows_another("primalish"));
        for &name in CLAIM_NAMES {
            assert!(
                !claim_name_shadows_another(name),
                "`{name}` is in the vocabulary and must not be refused by the guard"
            );
        }
        // Unrelated names are none of this guard's business: they are refused,
        // if at all, for having no check — not for their spelling.
        assert!(!claim_name_shadows_another("objective"));
    }

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
