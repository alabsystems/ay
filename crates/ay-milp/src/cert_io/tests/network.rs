// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn network_pattern_count_wire_round_trips_and_rejects_duplicate_variables() {
    let proof = crate::pattern_count_route::PatternCountOptimalityCertificate {
        blocks: vec![vec![1, 2], vec![3, 4], vec![5, 6]],
        pb_value: -17,
    };
    let value = BigRational::new(29.into(), 4.into());
    let certificate =
        crate::network_design_route::optimality_from_pattern_count(value.clone(), proof.clone());
    let wire = network_design_optimality_block(&certificate).expect("bounded wire block");
    let lines: Vec<&str> = wire.lines().collect();
    let (decoded, next) = parse_network_design_pattern_count(&lines, 0).expect("wire parses");
    assert_eq!(decoded, proof);
    assert_eq!(next, lines.len());
    assert!(wire.contains("value=29/4 frame=model kind=pattern-count"));

    let duplicate = [
        "network-design-optimality value=0 frame=model kind=pattern-count \
             pb_value=0 blocks=2 width=2",
        "block 1 2",
        "block 2 3",
        "end",
    ];
    assert!(parse_network_design_pattern_count(&duplicate, 0).is_err());

    let oversized_variable = format!("block {}", "1".repeat(2_000));
    let oversized = [
        "network-design-optimality value=0 frame=model kind=pattern-count \
             pb_value=0 blocks=2 width=1",
        oversized_variable.as_str(),
        "block 2",
        "end",
    ];
    assert!(parse_network_design_pattern_count(&oversized, 0).is_err());
}

pub(super) fn emitted_pattern_count_optimum_parses_and_checks_end_to_end() {
    let model_text = "NAME          REPEATED_NETWORK\n\
                          ROWS\n\
                          \x20N  COST\n\
                          \x20E  DEF\n\
                          \x20E  BAL1\n\
                          \x20L  CAP1\n\
                          \x20E  BAL2\n\
                          \x20L  CAP2\n\
                          COLUMNS\n\
                          \x20   F1        BAL1      1          CAP1      1\n\
                          \x20   F2        BAL2      1          CAP2      1\n\
                          \x20   OBJ       COST      0.5        DEF       1\n\
                          \x20   MARK0000  'MARKER'              'INTORG'\n\
                          \x20   E1        DEF      -5          CAP1     -1\n\
                          \x20   E2        DEF      -5          CAP2     -1\n\
                          \x20   MARK0001  'MARKER'              'INTEND'\n\
                          RHS\n\
                          \x20   RHS       BAL1      1          BAL2      1\n\
                          BOUNDS\n\
                          \x20LO BND       F1        0\n\
                          \x20LO BND       F2        0\n\
                          \x20FR BND       OBJ\n\
                          \x20BV BND       E1\n\
                          \x20BV BND       E2\n\
                          ENDATA\n";
    let problem = crate::read_mps(model_text).expect("repeated network MPS parses");
    assert_eq!(problem.obj_scale, BigRational::from_integer(2.into()));
    let decision = crate::network_design_route::try_solve_certified(&problem.model, None)
        .expect("pattern-count route proves the repeated network optimum");
    let crate::network_design_route::CertifiedNetworkDesignDecision::Optimal {
        value,
        model_values,
        certificate,
    } = decision
    else {
        panic!("expected a certified optimum")
    };
    let pattern_proof = match crate::network_design_route::optimality_parts(&certificate).1 {
        crate::network_design_route::NetworkDesignOptimalityProofRef::PatternCount(proof) => {
            proof.clone()
        }
        crate::network_design_route::NetworkDesignOptimalityProofRef::StrictBetter(_) => {
            panic!("expected a pattern-count certificate")
        }
    };

    let scale = problem.obj_scale.clone();
    let ctx = EmitCtx {
        model: &problem.model,
        model_text,
        col_names: &problem.col_names,
        obj_scale: &scale,
        provenance: "pattern-count-e2e-test",
        replay_claims: &[],
        affine_aggregation_certificate: None,
        parity_infeasibility_certificate: None,
        sat_relu_infeasibility_certificate: None,
        network_design_infeasibility_certificate: None,
        network_design_optimality_certificate: Some(&certificate),
        block_angular_optimality_certificate: None,
        single_machine_scheduling_optimality_certificate: None,
        single_row_dp_infeasibility_certificate: None,
        multi_row_bdd_infeasibility_certificate: None,
        open_domain_single_row_dp_infeasibility_certificate: None,
        open_domain_multi_row_bdd_infeasibility_certificate: None,
        open_domain_hybrid_pb_lp_infeasibility_certificate: None,
        open_domain_hybrid_integer_lift_infeasibility_certificate: None,
        hybrid_pb_lp_infeasibility_certificate: None,
        hybrid_integer_lift_infeasibility_certificate: None,
        max_bytes: None,
    };
    let outcome = Outcome::Optimal {
        value: value.clone(),
        model_values: model_values.clone(),
        cert: None,
    };
    let wire = emit(&ctx, &outcome);
    assert!(wire.contains("kind=pattern-count"));
    assert!(wire.contains("verdict optimal value=5 frame=file"));
    assert!(wire.contains("network-design-optimality value=10 frame=model"));
    let parsed = parse(&wire).expect("public parser accepts the emitted certificate");
    assert!(parsed.network_design_optimality.is_some());
    let report = check(&wire, model_text);
    assert_eq!(report.status, CheckStatus::Verified, "{}", report.census());
    assert_eq!(
        report.claims_in(ClaimStanding::Verified),
        vec!["primal", "dual"]
    );
    assert_pattern_tampering_is_refuted(ctx, &outcome, value, pattern_proof, model_text);
}

fn assert_pattern_tampering_is_refuted(
    ctx: EmitCtx<'_>,
    outcome: &Outcome,
    value: BigRational,
    mut tampered_proof: crate::pattern_count_route::PatternCountOptimalityCertificate,
    model_text: &str,
) {
    tampered_proof.pb_value = tampered_proof
        .pb_value
        .checked_add(1)
        .expect("small fixture value");
    let tampered =
        crate::network_design_route::optimality_from_pattern_count(value.clone(), tampered_proof);
    let tampered_ctx = EmitCtx {
        network_design_optimality_certificate: Some(&tampered),
        ..ctx
    };
    let tampered_wire = emit(&tampered_ctx, &outcome);
    let tampered_report = check(&tampered_wire, model_text);
    assert_eq!(tampered_report.status, CheckStatus::Refuted);
    assert_eq!(
        tampered_report.claims_in(ClaimStanding::Refuted),
        vec!["dual"]
    );
}

/// THE SIZE-PREFERENCE LANE MEASURES THE BYTES THIS WRITER WRITES.
///
/// `tree_cert::compact_leaf` ranks two exact-verified proposals for the
/// same leaf by [`crate::tree_cert::wire_weight`] and ships the smaller,
/// because `--emit-cert-max-bytes` drops an overflowing block and
/// downgrades the claim. That decision is only as good as the estimate, so
/// the estimate is held to THIS function's actual output — the one the
/// consumer pays for — rather than to a formula nobody re-derives.
pub(super) fn the_leaf_weight_estimate_is_the_bytes_the_writer_emits() {
    let mults = vec![
        // A bare integer, a fraction, a negative numerator, a wide dyadic
        // of the kind the exactified float lane produces, and both fact
        // kinds at one- and multi-digit indices.
        Multiplier {
            fact: FactRef::RowBound {
                row: Row(0),
                side: BoundSide::Lower,
            },
            coeff: BigRational::one(),
        },
        Multiplier {
            fact: FactRef::RowBound {
                row: Row(1234),
                side: BoundSide::Upper,
            },
            coeff: BigRational::new(BigInt::from(75733), BigInt::from(1510)),
        },
        Multiplier {
            fact: FactRef::ColBound {
                col: Col(7),
                side: BoundSide::Lower,
            },
            coeff: BigRational::new(BigInt::from(-3), BigInt::from(4)),
        },
        Multiplier {
            fact: FactRef::ColBound {
                col: Col(65_535),
                side: BoundSide::Upper,
            },
            coeff: BigRational::new(
                BigInt::from(2_514_297_896_833_393_i64),
                BigInt::from(70_368_744_177_664_i64),
            ),
        },
    ];
    let cert = FarkasCertificate { multipliers: mults };
    let mut written = String::new();
    write_multipliers(&mut written, &cert.multipliers);
    assert_eq!(
        crate::tree_cert::wire_weight(&cert),
        written.len(),
        "the lane's size estimate must be the emitted byte count exactly, \
             or it ranks proposals in units the cap does not use; wrote {written:?}"
    );
}
