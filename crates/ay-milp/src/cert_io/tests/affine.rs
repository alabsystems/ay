// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn affine_optimality_wire_round_trips_and_checks_end_to_end() {
    let (problem, certificate, outcome) = affine_optimal_fixture(true);
    let wire = emit_affine_fixture(&problem, &certificate, &outcome);
    assert!(wire.contains("evidence dual SUCCINCT affine-aggregation"));
    assert!(wire.contains("inner optimality"));
    let parsed = parse(&wire).expect("affine wire parses");
    assert!(parsed.affine_aggregation.is_some());
    let report = check(&wire, AFFINE_OPTIMAL_MPS);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");
    assert_eq!(
        report.claims_in(ClaimStanding::Verified),
        vec!["primal", "dual"]
    );
}

pub(super) fn sat_relu_rup_emitter_refuses_noncanonical_internal_dags() {
    let variable = Variable::new(0);
    let malformed = SatReluInfeasibilityCertificate::from_wire_parts(
        1,
        [0; 32],
        [0; 32],
        1,
        2,
        vec![
            RupStep {
                id: 3,
                clause: vec![Literal::positive(variable)],
                rup_hints: vec![1],
            },
            RupStep {
                id: 4,
                clause: Vec::new(),
                // A forward/unknown hint is structurally noncanonical even
                // before semantic RUP replay.
                rup_hints: vec![5],
            },
        ],
        4,
    );
    assert!(sat_relu_rup_block(&malformed, MAX_SAT_RELU_RUP_BYTES).is_none());
}

pub(super) fn unsupported_affine_optimality_stays_partial_but_replays() {
    let (problem, certificate, outcome) = affine_optimal_fixture(false);
    let wire = emit_affine_fixture(&problem, &certificate, &outcome);
    assert!(wire.contains("inner unsupported"));
    assert!(wire.contains("evidence dual NONE"));
    assert!(!wire.contains("evidence dual SUCCINCT affine-aggregation"));
    let report = check(&wire, AFFINE_OPTIMAL_MPS);
    assert_eq!(report.status(), CheckStatus::Partial, "{report:#?}");
    assert_eq!(report.claims_in(ClaimStanding::Verified), vec!["primal"]);
    assert_eq!(report.claims_in(ClaimStanding::Unbacked), vec!["dual"]);
}

pub(super) fn unsupported_affine_infeasibility_is_unverified_and_cannot_be_promoted() {
    let (problem, mut certificate, _) = affine_optimal_fixture(false);
    certificate.claim = AffineAggregationClaim::Infeasible;
    certificate.reduced_primal = None;
    certificate.source_primal = None;
    let outcome = Outcome::Infeasible {
        cert: None,
        tree_cert: None,
    };
    let wire = emit_affine_fixture(&problem, &certificate, &outcome);
    assert!(wire.contains("inner unsupported"));
    assert!(wire.contains("evidence infeasible NONE"));
    let report = check(&wire, AFFINE_OPTIMAL_MPS);
    assert_eq!(report.status(), CheckStatus::Unverified, "{report:#?}");
    assert_eq!(
        report.claims_in(ClaimStanding::Unbacked),
        vec!["infeasible"]
    );

    let promoted = wire.replace(
        "evidence infeasible NONE\n",
        "evidence infeasible SUCCINCT affine-aggregation\n",
    );
    let end = promoted
        .rfind("%END sha256:")
        .expect("wire has an end seal");
    let mut promoted = promoted[..end].to_owned();
    let digest = sha256_hex(promoted.as_bytes());
    let _ = writeln!(promoted, "%END sha256:{digest}");
    let report = check(&promoted, AFFINE_OPTIMAL_MPS);
    assert_eq!(report.status(), CheckStatus::Refuted, "{report:#?}");
    assert_eq!(report.claims_in(ClaimStanding::Refuted), vec!["infeasible"]);
}

pub(super) fn affine_codec_caps_are_atomic_and_legacy_v1_stays_readable() {
    let (problem, certificate, outcome) = affine_optimal_fixture(true);

    let capped = emit_affine_fixture_with(&problem, Some(&certificate), &outcome, Some(1));
    assert!(!capped.contains("affine-aggregation version="));
    assert!(capped.contains("truncated affine-aggregation"));
    assert!(capped.contains("evidence dual NONE truncated"));
    assert_eq!(
        check(&capped, AFFINE_OPTIMAL_MPS).status(),
        CheckStatus::Unverified
    );

    let legacy = emit_affine_fixture_with(&problem, None, &outcome, None);
    assert!(legacy.starts_with("%AYC 1\n"));
    let parsed = parse(&legacy).expect("pre-affine v1 shape remains readable");
    assert!(parsed.affine_aggregation.is_none());
    assert_eq!(
        check(&legacy, AFFINE_OPTIMAL_MPS).status(),
        CheckStatus::Partial
    );
}

pub(super) fn affine_parser_rejects_oversized_rationals_and_tree_depth_before_building() {
    let too_long = "9".repeat(MAX_AFFINE_RATIONAL_TOKEN_BYTES + 1);
    assert!(parse_affine_rat(&too_long).is_none());
    let too_many_bits = (BigInt::one() << (MAX_RATIONAL_BITS as usize)).to_string();
    assert!(too_many_bits.len() <= MAX_AFFINE_RATIONAL_TOKEN_BYTES);
    assert!(parse_affine_rat(&too_many_bits).is_none());

    let mut tree = String::new();
    for _ in 0..=MAX_AFFINE_TREE_DEPTH {
        let _ = writeln!(tree, "split 0 0");
    }
    let lines: Vec<&str> = tree.lines().collect();
    let error = parse_tree_until(&lines, 0, "endinner", ProofParseMode::Affine)
        .expect_err("over-depth affine tree must be rejected before reconstruction");
    assert!(error.to_string().contains("depth exceeds hard cap"));

    let multiple_roots = ["leaf", "endleaf", "leaf", "endleaf", "end"];
    assert!(parse_tree(&multiple_roots, 0).is_err());
}

pub(super) fn affine_wire_checker_rejects_every_tampered_boundary() {
    let (problem, certificate, outcome) = affine_optimal_fixture(false);
    let rejected = |certificate: &AffineAggregationCertificate| {
        let wire = emit_affine_fixture(&problem, certificate, &outcome);
        let report = check(&wire, AFFINE_OPTIMAL_MPS);
        assert_eq!(report.status(), CheckStatus::Refuted, "{report:#?}");
    };

    let mut tampered = certificate.clone();
    tampered.analysis.source_digest.push('0');
    rejected(&tampered);

    let mut tampered = certificate.clone();
    tampered.analysis.reduced_digest.push('0');
    rejected(&tampered);

    let mut tampered = certificate.clone();
    tampered.analysis.objective_delta += BigRational::from_integer(1.into());
    rejected(&tampered);

    let mut tampered = certificate.clone();
    let bounds = Arc::make_mut(&mut tampered.analysis.bounds);
    bounds[0].lower = Some(BigRational::from_integer(3.into()));
    bounds[0].upper = Some(BigRational::from_integer(2.into()));
    rejected(&tampered);

    let mut tampered = certificate.clone();
    let steps = Arc::make_mut(&mut tampered.analysis.steps);
    let AffineRecovery::Equality { constant, .. } = &mut steps[0] else {
        panic!("fixture has one equality step");
    };
    *constant += BigRational::from_integer(1.into());
    rejected(&tampered);

    let mut tampered = certificate.clone();
    tampered.inner_proof = AffineAggregationInnerProof::Farkas(FarkasCertificate {
        multipliers: Vec::new(),
    });
    rejected(&tampered);

    let mut tampered = certificate;
    tampered.source_primal.as_mut().expect("source primal")[0] =
        BigRational::from_integer(3.into());
    rejected(&tampered);
}
