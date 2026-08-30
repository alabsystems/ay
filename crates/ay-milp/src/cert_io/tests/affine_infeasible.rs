// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

enum InnerProof {
    Farkas,
    Tree,
}

fn infeasible_affine_fixture(
    inner: InnerProof,
) -> (crate::MpsProblem, AffineAggregationCertificate) {
    let problem = crate::read_mps(AFFINE_INFEASIBLE_MPS).expect("infeasible affine fixture parses");
    let (reduced, post) = crate::presolve::implied_free::aggregate_implied_free_equalities(
        &problem.model,
        None,
        None,
    )
    .expect("the unrelated fixed integer projects");
    assert_eq!((reduced.num_cols(), reduced.num_rows()), (2, 2));
    let farkas = FarkasCertificate {
        multipliers: vec![
            Multiplier {
                fact: FactRef::RowBound {
                    row: Row(0),
                    side: BoundSide::Upper,
                },
                coeff: BigRational::one(),
            },
            Multiplier {
                fact: FactRef::RowBound {
                    row: Row(1),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            },
        ],
    };
    farkas
        .verify(&reduced)
        .expect("the two reduced equalities contradict");
    let outcome = match inner {
        InnerProof::Farkas => Outcome::Infeasible {
            cert: Some(farkas),
            tree_cert: None,
        },
        InnerProof::Tree => Outcome::Infeasible {
            cert: None,
            tree_cert: Some(MilpInfeasibilityCertificate {
                root: TreeNode::Leaf { farkas },
            }),
        },
    };
    let certificate = post
        .certificate_for_outcome(&outcome, &reduced, &problem.model, None, None)
        .expect("reduced infeasibility artifact is built");
    (problem, certificate)
}

fn emit_infeasible_affine(
    problem: &crate::MpsProblem,
    certificate: &AffineAggregationCertificate,
) -> String {
    emit(
        &EmitCtx {
            model: &problem.model,
            model_text: AFFINE_INFEASIBLE_MPS,
            col_names: &problem.col_names,
            obj_scale: &problem.obj_scale,
            provenance: "affine-infeasible-codec-test",
            replay_claims: &[],
            affine_aggregation_certificate: Some(certificate),
            parity_infeasibility_certificate: None,
            sat_relu_infeasibility_certificate: None,
            network_design_infeasibility_certificate: None,
            network_design_optimality_certificate: None,
            block_angular_optimality_certificate: None,
            milp_optimality_tree_certificate: None,
            root_dual_bound_certificate: None,
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
        },
        &Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        },
    )
}

pub(super) fn affine_farkas_wire_checks_in_the_rebuilt_reduced_frame() {
    let (problem, certificate) = infeasible_affine_fixture(InnerProof::Farkas);
    assert_eq!(
        certificate.verify(&problem.model),
        Ok(AffineAggregationVerification {
            primal_verified: false,
            infeasibility_verified: true,
            optimality_verified: false,
        })
    );
    let wire = emit_infeasible_affine(&problem, &certificate);
    assert!(wire.contains("evidence infeasible SUCCINCT affine-aggregation"));
    assert!(wire.contains("inner farkas"));
    let report = check(&wire, AFFINE_INFEASIBLE_MPS);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");
    assert_eq!(
        report.claims_in(ClaimStanding::Verified),
        vec!["infeasible"]
    );
}

pub(super) fn affine_tree_wire_checks_in_the_rebuilt_reduced_frame() {
    let (problem, certificate) = infeasible_affine_fixture(InnerProof::Tree);
    let wire = emit_infeasible_affine(&problem, &certificate);
    assert!(wire.contains("inner tree"));
    assert_eq!(
        check(&wire, AFFINE_INFEASIBLE_MPS).status(),
        CheckStatus::Verified
    );
}
