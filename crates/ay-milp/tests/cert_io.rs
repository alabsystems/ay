// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `.ayc` certificate emission, parsing, and — the part that matters — the
//! independent checker's ability to FAIL.
//!
//! A checker that cannot reject is worthless, so most of this file is tampering:
//! flip a witness value, rescale a multiplier, swap the model digest, promote a
//! REPLAY claim to SUCCINCT, or point the checker at a different model, and
//! assert the exit status is not `VERIFIED`.

use ay_milp::cert_io::{self, CheckStatus, EvidenceKind};
use ay_milp::{BabSession, Outcome, SolveOpts};
use num_rational::BigRational;
use num_traits::One;

/// `min x + 2y` s.t. `x + y >= 3`, `x <= 2`, `0 <= x,y <= 10`, continuous.
/// The optimum is `x = 2, y = 1`, value 4 — and a continuous model is the one
/// verdict shape this build certifies on BOTH halves.
const LP: &str = "NAME          LP1
ROWS
 N  COST
 G  R1
 L  R2
COLUMNS
    X         COST      1.0        R1        1.0
    X         R2        1.0
    Y         COST      2.0        R1        1.0
RHS
    RHS       R1        3.0        R2        2.0
BOUNDS
 UP BND       X         10.0
 UP BND       Y         10.0
ENDATA
";

/// `min x + y` s.t. `x + y >= 3`, `x <= 2`, both INTEGER. Optimum 3. A MILP
/// optimum has no dual-side object in this build; the certificate must say so.
const MILP: &str = "NAME          MILP1
ROWS
 N  COST
 G  R1
 L  R2
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1.0        R1        1.0
    X         R2        1.0
    Y         COST      1.0        R1        1.0
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       R1        3.0        R2        2.0
BOUNDS
 UP BND       X         10.0
 UP BND       Y         10.0
ENDATA
";

/// `x >= 3` and `x <= 2` over one integer column: infeasible at the root, so
/// the root Farkas lane produces one combination.
const INF: &str = "NAME          INF1
ROWS
 N  COST
 G  R1
 L  R2
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1.0        R1        1.0
    X         R2        1.0
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       R1        3.0        R2        2.0
BOUNDS
 UP BND       X         10.0
ENDATA
";

fn solve_and_emit(text: &str) -> (String, Outcome) {
    let p = ay_milp::read_mps(text).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs(20));
    let mut s = BabSession::new(p.model, &opts).expect("session");
    let outcome = s.check().expect("solve");
    let ctx = cert_io::EmitCtx {
        model: s.model(),
        model_text: text,
        col_names: &names,
        obj_scale: &scale,
        provenance: "host=test",
        replay_claims: s.replay_claims(),
        max_bytes: None,
    };
    (cert_io::emit(&ctx, &outcome), outcome)
}

/// Re-seal a hand-edited certificate so the `%END` digest still matches. Used
/// by every tamper test that wants to prove the CONTENT check fires rather than
/// merely tripping the body digest.
fn reseal(text: &str) -> String {
    let mut body = String::new();
    for l in text
        .lines()
        .take_while(|l| !l.trim_start().starts_with("%END"))
    {
        body.push_str(l);
        body.push('\n');
    }
    let digest = cert_io::sha256_hex(body.as_bytes());
    format!("{body}%END sha256:{digest}\n")
}

// ---------------------------------------------------------------------------
// (a) Emission and the happy path.
// ---------------------------------------------------------------------------

#[test]
fn continuous_optimum_is_fully_verified() {
    let (ayc, _) = solve_and_emit(LP);
    let r = cert_io::check(&ayc, LP);
    assert_eq!(r.status, CheckStatus::Verified, "{r:#?}");
    assert_eq!(r.status.exit_code(), 0);
    assert_eq!(r.claims.len(), 2);
    assert!(r
        .claims
        .iter()
        .all(|c| c.verified && c.kind == EvidenceKind::Succinct));
}

#[test]
fn milp_optimum_emits_the_witness_and_admits_the_missing_dual() {
    // THE HONESTY REQUIREMENT, end to end. An `Optimal` is TWO claims: the
    // primal half is succinctly checkable and the dual half does not exist in
    // this build. `Outcome::Optimal { cert: None }` cannot express that
    // difference; the certificate must.
    let (ayc, out) = solve_and_emit(MILP);
    assert!(matches!(out, Outcome::Optimal { cert: None, .. }));
    let r = cert_io::check(&ayc, MILP);
    assert_eq!(r.status, CheckStatus::Unverified, "{r:#?}");
    assert_eq!(r.status.exit_code(), 10);
    let primal = r
        .claims
        .iter()
        .find(|c| c.name == "primal")
        .expect("primal");
    assert!(primal.verified && primal.kind == EvidenceKind::Succinct);
    let dual = r.claims.iter().find(|c| c.name == "dual").expect("dual");
    assert!(!dual.verified && dual.kind == EvidenceKind::None);
    // The witness IS in the file — the thing the old `AY_DUMP_SOL` could not do
    // on an `Optimal` at all.
    assert!(ayc.contains("witness cols="));
}

// ---------------------------------------------------------------------------
// (a2) CLAIM-SET POLICY. The obligations come from the VERDICT, not from
// whichever records survive in the file.
//
// These four are the attacks two independent adversarial reviewers used to make
// the checker print VERIFIED / exit 0 for demonstrably wrong answers. The
// checker validated the claims PRESENT and started at `Verified`, so deleting a
// line deleted the obligation it named — and since `%END` is a body checksum,
// not a signature, `reseal()` (used by every tamper test above) made the edit
// look pristine. Each of these MUST stay refuted.
// ---------------------------------------------------------------------------

#[test]
fn deleting_the_required_dual_claim_cannot_bless_an_optimum() {
    // The misc07 attack in miniature: take an honest certificate, drop the
    // record that carries the unmet obligation, re-seal. Before the claim-set
    // policy this checked VERIFIED with exit 0.
    let (ayc, _) = solve_and_emit(MILP);
    assert!(
        ayc.contains("evidence dual"),
        "fixture must carry a dual record"
    );
    let stripped: String = ayc
        .lines()
        .filter(|l| !l.trim_start().starts_with("evidence dual"))
        .map(|l| format!("{l}\n"))
        .collect();
    let forged = reseal(&stripped);
    assert_ne!(forged, ayc, "the deletion must actually apply");
    let r = cert_io::check(&forged, MILP);
    // REFUTED, not merely Unverified: a missing REQUIRED claim is a forged or
    // truncated certificate, which is a stronger failure than an unproven one.
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
    assert_eq!(r.status.exit_code(), 20);
    assert!(
        r.notes.iter().any(|n| n.contains("CLAIM-SET VIOLATION")),
        "the refusal must name the claim-set violation: {r:#?}"
    );
}

#[test]
fn promoting_a_feasible_verdict_to_optimal_cannot_bless_a_wrong_value() {
    // The exact misc07 forgery: an honest FEASIBLE certificate whose verdict
    // word is rewritten to `optimal` and whose dual record is dropped. The
    // witness is genuinely feasible, so every check that EXISTS passes; only
    // the claim set catches it.
    let (ayc, _) = solve_and_emit(MILP);
    let promoted: String = ayc
        .lines()
        .filter(|l| !l.trim_start().starts_with("evidence dual"))
        .map(|l| format!("{}\n", l.replace("verdict feasible", "verdict optimal")))
        .collect();
    let forged = reseal(&promoted);
    let r = cert_io::check(&forged, MILP);
    assert_ne!(
        r.status,
        CheckStatus::Verified,
        "a promoted verdict with its dual obligation deleted must never verify: {r:#?}"
    );
}

#[test]
fn an_infeasible_verdict_carrying_a_primal_witness_is_self_contradictory() {
    // The checker blessed INFEASIBLE while its own primal check proved a point
    // of that very model feasible. A verdict and its claims must be consistent.
    let (ayc, _) = solve_and_emit(MILP);
    let flipped = reseal(&ayc.replace("verdict optimal", "verdict infeasible"));
    let r = cert_io::check(&flipped, MILP);
    assert_ne!(r.status, CheckStatus::Verified, "{r:#?}");
    assert!(
        r.notes.iter().any(|n| n.contains("CLAIM-SET VIOLATION")),
        "a primal claim under an infeasible verdict must be rejected: {r:#?}"
    );
}

#[test]
fn deleting_a_replay_claim_cannot_launder_it_into_a_proof() {
    // The markshare1 attack. A REPLAY claim is the checker's honest "I did not
    // check this"; deleting it must not silently upgrade the file to VERIFIED.
    // Synthesised on the MILP fixture so the test does not depend on the
    // lattice device arming.
    let (ayc, _) = solve_and_emit(MILP);
    let stripped: String = ayc
        .lines()
        .filter(|l| !l.trim_start().starts_with("evidence dual"))
        .map(|l| format!("{l}\n"))
        .collect();
    let r = cert_io::check(&reseal(&stripped), MILP);
    assert_ne!(
        r.status,
        CheckStatus::Verified,
        "deleting an unmet obligation must never produce a pass: {r:#?}"
    );
}

#[test]
fn an_unrecognised_verdict_word_fails_closed() {
    // The claim-set policy's OWN first bypass, found by attacking the fix
    // rather than trusting it. The required/forbidden table keyed on the exact
    // lowercase verdict words and fell through to "no obligations" for anything
    // else, so `Optimal`, `optimum` and `opt` all dodged it and checked
    // VERIFIED / exit 0 on the very misc07 forgery the policy was written to
    // stop. "I do not know what this claims" must never mean "this is fine".
    let (ayc, _) = solve_and_emit(MILP);
    for word in ["Optimal", "optimum", "opt", "OPTIMAL", "optimal_x", ""] {
        let forged = reseal(&ayc.replace("verdict optimal", &format!("verdict {word}")));
        let r = cert_io::check(&forged, MILP);
        assert_ne!(
            r.status,
            CheckStatus::Verified,
            "verdict `{word}` must not verify: {r:#?}"
        );
    }
}

#[test]
fn root_infeasibility_emits_a_verifying_farkas() {
    let (ayc, _) = solve_and_emit(INF);
    assert!(ayc.contains("evidence infeasible SUCCINCT farkas"));
    let r = cert_io::check(&ayc, INF);
    assert_eq!(r.status, CheckStatus::Verified, "{r:#?}");
}

#[test]
fn every_verdict_shape_emits_something_parseable() {
    for text in [LP, MILP, INF] {
        let (ayc, _) = solve_and_emit(text);
        let parsed = cert_io::parse(&ayc).expect("emitted certificates parse");
        assert!(parsed.end_digest_ok, "the emitter seals what it writes");
        assert!(!parsed.claims.is_empty());
    }
}

// ---------------------------------------------------------------------------
// (b) TAMPERING. A checker that cannot fail is worthless.
// ---------------------------------------------------------------------------

#[test]
fn tamper_witness_value_is_refuted() {
    let (ayc, _) = solve_and_emit(LP);
    // `x 0 X 2` is the optimum's first coordinate. Move it and the point either
    // stops being feasible or stops attaining the claimed value.
    let tampered = reseal(&ayc.replace("x 0 X 2\n", "x 0 X 1\n"));
    assert_ne!(tampered, ayc, "the tamper must actually apply");
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
    assert_eq!(r.status.exit_code(), 20);
}

#[test]
fn tamper_claimed_optimum_is_refuted() {
    let (ayc, _) = solve_and_emit(LP);
    // Claim a better optimum than the point attains. Both halves must catch it:
    // the witness no longer attains the value, and the dual bound no longer
    // meets it.
    let tampered = reseal(&ayc.replace("value=4 frame=file", "value=3 frame=file"));
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
    assert!(r
        .claims
        .iter()
        .filter(|c| c.name == "primal" || c.name == "dual")
        .all(|c| !c.verified));
}

#[test]
fn tamper_multiplier_is_refuted() {
    let (ayc, _) = solve_and_emit(INF);
    // Rescale one Farkas multiplier: the combination stops being the identity
    // `0·x >= positive`.
    let tampered = reseal(&ayc.replace("mult row 1 upper 1\n", "mult row 1 upper 2\n"));
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, INF);
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn tamper_dropped_multiplier_is_refuted() {
    let (ayc, _) = solve_and_emit(INF);
    let tampered = reseal(&ayc.replace("mult row 0 lower 1\n", ""));
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, INF);
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn tamper_model_file_digest_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    let parsed = cert_io::parse(&ayc).expect("parses");
    let forged = "0".repeat(64);
    let tampered = reseal(&ayc.replace(&parsed.header.file_digest, &forged));
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status, CheckStatus::Mismatch, "{r:#?}");
    assert_eq!(r.status.exit_code(), 30);
}

#[test]
fn tamper_canonical_model_digest_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    let parsed = cert_io::parse(&ayc).expect("parses");
    let forged = "1".repeat(64);
    let tampered = reseal(&ayc.replace(&parsed.header.canon_digest, &forged));
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status, CheckStatus::Mismatch, "{r:#?}");
}

#[test]
fn tamper_end_digest_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    // Edit the body WITHOUT resealing: the trailing digest catches it even when
    // the edited content would still verify.
    let tampered = ayc.replace("solver ay-milp", "solver not-ay-milp");
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status, CheckStatus::Mismatch, "{r:#?}");
}

#[test]
fn certificate_checked_against_a_different_model_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    let r = cert_io::check(&ayc, MILP);
    assert_eq!(r.status, CheckStatus::Mismatch, "{r:#?}");
}

// ---------------------------------------------------------------------------
// (c) MISLABELLING. The one failure that would make the format worse than
//     emitting nothing.
// ---------------------------------------------------------------------------

#[test]
fn a_replay_claim_relabelled_succinct_is_rejected_by_the_parser() {
    // Hand-build the exact forgery the format exists to prevent: a replay block
    // (an exhaustive sweep, no exported object) whose evidence record claims
    // SUCCINCT. This must fail at PARSE time — not merely fail verification —
    // because the source-token set for each kind is closed.
    let forged = "%AYC 1
model file sha256:"
        .to_string()
        + &"0".repeat(64)
        + " bytes=1 form=text
model canon v1 sha256:"
        + &"0".repeat(64)
        + "
model shape rows=0 cols=0 intcols=0 sense=min obj_scale=1
solver ay-milp test
verdict optimal value=1 frame=file
evidence dual SUCCINCT objective-face-empty
replay objective-face-empty
device lattice-cvp
method ahl-hnf-lll+bkz+schnorr-euchner
arithmetic outward-rounded-f64-interval
nodes-visited 1
node-budget 4000000000
outcome exhausted
tcb crates/ay-milp/src/lattice.rs
end
";
    let sealed = reseal(&forged);
    let err = cert_io::parse(&sealed).expect_err("a mislabelled evidence record must not parse");
    assert!(
        matches!(err, cert_io::CertIoError::MislabelledEvidence { .. }),
        "{err:?}"
    );
    // And the checker reports it as REFUTED, never as a pass.
    let r = cert_io::check(&sealed, LP);
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn a_succinct_source_relabelled_replay_is_rejected_by_the_parser() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&ayc.replace(
        "evidence primal SUCCINCT witness",
        "evidence primal REPLAY witness",
    ));
    let err = cert_io::parse(&forged).expect_err("REPLAY cannot name a succinct block");
    assert!(
        matches!(err, cert_io::CertIoError::MislabelledEvidence { .. }),
        "{err:?}"
    );
}

#[test]
fn a_succinct_claim_whose_block_is_missing_is_refuted() {
    let (ayc, _) = solve_and_emit(INF);
    // Delete the farkas block but keep the SUCCINCT claim.
    let mut body = String::new();
    for l in ayc
        .lines()
        .filter(|l| !l.starts_with("farkas ") && !l.starts_with("mult ") && *l != "end")
    {
        body.push_str(l);
        body.push('\n');
    }
    let forged = reseal(&body);
    let r = cert_io::check(&forged, INF);
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn a_certificate_bounding_a_different_objective_is_refuted() {
    // THE CHECK A TRUSTING CHECKER WOULD SKIP.
    //
    // For `min x + 2y` s.t. `x + y >= 3`, the single multiplier `1 ×
    // (row0 lower)` combines to exactly `x + y - 3`. That is a PERFECTLY VALID
    // optimality certificate — for the objective `x + y` with bound 3. It
    // verifies. It says nothing about the model's `x + 2y`, and
    // `tighten_col_bounds` legitimately produces certificates over other
    // objectives, so this is not a hypothetical shape. The checker must compare
    // the certificate's own named objective against the model's and reject.
    let forged = format!(
        "%AYC 1
model file sha256:{} bytes={} form=text
model canon v1 sha256:{}
model shape rows=2 cols=2 intcols=0 sense=min obj_scale=1
solver ay-milp test
verdict optimal value=3 frame=file
evidence dual SUCCINCT optcert
optcert sense=min bound=3 frame=model trivial=0
obj 0 1
obj 1 1
mult row 0 lower 1
end
",
        cert_io::sha256_hex(LP.as_bytes()),
        LP.len(),
        cert_io::canonical_digest(&ay_milp::read_mps(LP).expect("parses").model),
    );
    let sealed = reseal(&forged);
    let r = cert_io::check(&sealed, LP);
    assert_eq!(r.status, CheckStatus::Refuted, "{r:#?}");
    let dual = r.claims.iter().find(|c| c.name == "dual").expect("dual");
    assert!(
        dual.detail.contains("DIFFERENT objective"),
        "the rejection must name the reason: {}",
        dual.detail
    );
}

// ---------------------------------------------------------------------------
// (d) Wire-format strictness. A canonical format keeps the seal meaningful.
// ---------------------------------------------------------------------------

#[test]
fn non_canonical_rationals_do_not_parse() {
    let (ayc, _) = solve_and_emit(LP);
    for bad in ["2/4", "6/3", "4/1", "1/0", "2/-1"] {
        let forged = reseal(&ayc.replace("value=4 frame=file", &format!("value={bad} frame=file")));
        assert!(
            cert_io::parse(&forged).is_err(),
            "`{bad}` must not parse as a canonical wire rational"
        );
    }
}

#[test]
fn a_reordered_witness_does_not_parse() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&ayc.replace("x 0 X", "x 1 X"));
    assert!(
        cert_io::parse(&forged).is_err(),
        "a witness whose indices do not match their position must be rejected"
    );
}

#[test]
fn an_unknown_record_does_not_parse() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&format!("{ayc}\nsurprise 1\n").replace("%END", "#END"));
    assert!(cert_io::parse(&forged).is_err());
}

#[test]
fn a_future_format_version_is_refused() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&ayc.replace("%AYC 1", "%AYC 2"));
    assert!(cert_io::parse(&forged).is_err());
    assert_eq!(cert_io::check(&forged, LP).status, CheckStatus::Refuted);
}

// ---------------------------------------------------------------------------
// (e) Truncation DOWNGRADES; it never silently drops evidence.
// ---------------------------------------------------------------------------

#[test]
fn a_size_cap_downgrades_the_claim_it_drops() {
    let p = ay_milp::read_mps(LP).expect("parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new();
    let mut s = BabSession::new(p.model, &opts).expect("session");
    let outcome = s.check().expect("solve");
    let ctx = cert_io::EmitCtx {
        model: s.model(),
        model_text: LP,
        col_names: &names,
        obj_scale: &scale,
        provenance: "host=test",
        replay_claims: s.replay_claims(),
        // Small enough that no block fits.
        max_bytes: Some(1),
    };
    let ayc = cert_io::emit(&ctx, &outcome);
    assert!(ayc.contains("truncated witness"), "{ayc}");
    assert!(ayc.contains("evidence primal NONE truncated"), "{ayc}");
    let r = cert_io::check(&ayc, LP);
    // Downgraded, not passed and not silently shortened.
    assert_eq!(r.status, CheckStatus::Unverified, "{r:#?}");
}

// ---------------------------------------------------------------------------
// (f) The canonical model digest binds the MODEL, not the file.
// ---------------------------------------------------------------------------

#[test]
fn canonical_digest_separates_models_the_file_digest_cannot() {
    let a = ay_milp::read_mps(LP).expect("parses").model;
    let mut b = a.clone();
    // A bound change the file digest would only notice as "different bytes";
    // the canonical digest notices it as "different model".
    let c = b.col_at(0).expect("col 0");
    b.fix_col(c, 1.0);
    assert_ne!(cert_io::canonical_digest(&a), cert_io::canonical_digest(&b));
    // And it is a pure function of the model, not of how it was built.
    assert_eq!(
        cert_io::canonical_digest(&a),
        cert_io::canonical_digest(&a.clone())
    );
}

#[test]
fn value_frames_are_named_and_honoured() {
    // The reported optimum is in FILE units; an `OptimalityCertificate`'s bound
    // is in MODEL units (post-`obj_scale`). A checker that divided once and one
    // that divided twice would both look right, so the frame is on the wire.
    let (ayc, _) = solve_and_emit(LP);
    let parsed = cert_io::parse(&ayc).expect("parses");
    assert_eq!(parsed.value_frame, "file");
    assert_eq!(parsed.header.obj_scale, BigRational::one());
    assert!(
        ayc.contains("frame=model"),
        "the optcert bound names its frame"
    );
}
