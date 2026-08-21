// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn check_infeasible(
    certificate: &Certificate,
    model: &Model,
    source: Option<&str>,
    affine: Option<&Result<AffineAggregationVerification, AffineAggregationCertificateError>>,
) -> (bool, String) {
    match source {
        Some("affine-aggregation") => check_affine_infeasibility(certificate, affine),
        Some("sat-relu-rup") => check_sat_relu(certificate, model),
        Some("parity-gf2") => check_parity(certificate, model),
        Some("network-design-infeasibility") => check_network_infeasibility(certificate, model),
        Some("farkas") => check_farkas(certificate, model),
        Some("tree") => check_tree(certificate, model),
        Some("single-row-dp") => check_single_row(certificate, model),
        Some("multi-row-bdd") => check_multi_row(certificate, model),
        Some("open-domain-dp") => check_open_single_row(certificate, model),
        Some("open-domain-bdd") => check_open_multi_row(certificate, model),
        Some("hybrid-pb-lp") => check_hybrid(certificate, model),
        Some("open-domain-hybrid-pb-lp") => check_open_hybrid(certificate, model),
        Some("open-domain-hybrid-integer-lift") => check_open_lift(certificate, model),
        Some("hybrid-integer-lift") => check_integer_lift(certificate, model),
        _ => (
            false,
            "claim names an unsupported infeasibility block".into(),
        ),
    }
}

fn check_affine_infeasibility(
    certificate: &Certificate,
    affine: Option<&Result<AffineAggregationVerification, AffineAggregationCertificateError>>,
) -> (bool, String) {
    let Some(artifact) = &certificate.affine_aggregation else {
        return (
            false,
            "claim names an affine-aggregation block that is absent".into(),
        );
    };
    let Some(Ok(verification)) = affine else {
        return (
            false,
            "the affine-aggregation block did not replay successfully".into(),
        );
    };
    if artifact.claim() != &AffineAggregationClaim::Infeasible
        || !verification.infeasibility_verified
    {
        return (
            false,
            "the affine artifact carries no verified reduced-frame infeasibility proof".into(),
        );
    }
    (
        true,
        "threshold-free exact propagation licensed the recorded analysis box; every affine \
         substitution, digest and objective delta replayed; and the reduced Farkas/tree proof \
         verified against the independently rebuilt reduced model"
            .into(),
    )
}

fn check_sat_relu(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.sat_relu_infeasibility else {
        return (
            false,
            "claim names a sat-relu-rup block that is absent".into(),
        );
    };
    match crate::verify_sat_relu_infeasibility_certificate(model, proof, None) {
        Ok(()) => (
            true,
            "the exact SAT/ReLU CNF was rebuilt from the re-parsed source model, matched \
             clause-for-clause, and its bounded RUP refutation independently replayed"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the SAT/ReLU resolution artifact DOES NOT verify: {error}"),
        ),
    }
}

fn check_parity(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.parity_infeasibility else {
        return (
            false,
            "claim names a parity-gf2 block that is absent".into(),
        );
    };
    match crate::verify_parity_infeasibility_certificate(model, proof) {
        Ok(()) => (
            true,
            "the named exact equality rows sum to even coefficients for every integral column \
             and an odd right-hand side"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the GF(2) source-row contradiction DOES NOT verify: {error}"),
        ),
    }
}

fn check_network_infeasibility(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.network_design_infeasibility else {
        return (
            false,
            "claim names a network-design-infeasibility block that is absent".into(),
        );
    };
    match crate::network_design_route::verify_infeasibility_certificate(model, proof) {
        Ok(()) => (
            true,
            "the exact Hoffman projection was rebuilt from the re-parsed model, and its PB \
             refutation independently replayed against that rebuilt master"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the network-design infeasibility artifact DOES NOT verify: {error}"),
        ),
    }
}

fn check_farkas(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.farkas else {
        return (false, "claim names a Farkas block that is absent".into());
    };
    match proof.verify(model) {
        Ok(()) => (
            true,
            format!(
                "{} positive multipliers over model facts combine to `0 >= positive`: no point \
                 satisfies the model",
                proof.multipliers.len()
            ),
        ),
        Err(error) => (
            false,
            format!("the Farkas combination DOES NOT verify: {error}"),
        ),
    }
}

fn check_tree(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.tree else {
        return (false, "claim names a tree block that is absent".into());
    };
    let leaves = count_leaves(&proof.root);
    match proof.verify(model) {
        Ok(()) => (
            true,
            format!(
                "the case-split tree covers the model's integer domain and all {leaves} leaves \
                 are exactly empty"
            ),
        ),
        Err(error) => (
            false,
            format!("the tree certificate DOES NOT verify: {error}"),
        ),
    }
}

fn check_single_row(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.single_row_dp else {
        return (
            false,
            "claim names a single-row-dp block that is absent".into(),
        );
    };
    match crate::pb_route::verify_single_row_infeasibility_certificate(model, proof) {
        Ok(()) => (
            true,
            "the exact MILP-to-PB projection was rebuilt from the re-parsed model, and an \
             independent scalar replay verified every reachability checkpoint and found no \
             admissible sum"
                .into(),
        ),
        Err(error) => (false, error),
    }
}

fn check_multi_row(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.multi_row_bdd else {
        return (
            false,
            "claim names a multi-row-bdd block that is absent".into(),
        );
    };
    match crate::pb_route::verify_multi_row_infeasibility_certificate(model, proof) {
        Ok(()) => (
            true,
            "the exact MILP-to-PB projection was rebuilt from the re-parsed model, and the \
             independent verifier reconstructed every exact residual row state, checked every \
             decision-DAG merge, and proved every leaf rejecting"
                .into(),
        ),
        Err(error) => (false, error),
    }
}

fn check_open_single_row(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.open_domain_dp else {
        return (
            false,
            "claim names an open-domain-dp block that is absent".into(),
        );
    };
    if crate::open_domain_route::verify_single_row_infeasibility_certificate(model, proof) {
        (
            true,
            "the monotone open-domain projection was deterministically rebuilt from the \
             re-parsed source model, and an independent scalar replay verified every residual \
             reachability checkpoint"
                .into(),
        )
    } else {
        (
            false,
            "the rebuilt open-domain residual DOES NOT accept the single-row proof".into(),
        )
    }
}

fn check_open_multi_row(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.open_domain_bdd else {
        return (
            false,
            "claim names an open-domain-bdd block that is absent".into(),
        );
    };
    if crate::open_domain_route::verify_multi_row_infeasibility_certificate(model, proof) {
        (
            true,
            "the monotone open-domain projection was deterministically rebuilt from the \
             re-parsed source model, and the independent verifier reconstructed every residual \
             state, checked every DAG merge, and proved every leaf rejecting"
                .into(),
        )
    } else {
        (
            false,
            "the rebuilt open-domain residual DOES NOT accept the multi-row proof".into(),
        )
    }
}

fn check_hybrid(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.hybrid_pb_lp else {
        return (
            false,
            "claim names a hybrid-pb-lp block that is absent".into(),
        );
    };
    match verify_hybrid_pb_lp_infeasibility_certificate(model, proof) {
        Ok(()) => (
            true,
            "the binary master and every exact Benders cut were rebuilt from the re-parsed \
             model, every Farkas/no-good license verified, and the final PB refutation \
             independently replayed"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the hybrid PB/LP certificate DOES NOT verify: {error}"),
        ),
    }
}

fn check_open_hybrid(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.open_domain_hybrid_pb_lp else {
        return (
            false,
            "claim names an open-domain-hybrid-pb-lp block that is absent".into(),
        );
    };
    if crate::open_domain_route::verify_hybrid_pb_lp_infeasibility_certificate(model, proof) {
        (
            true,
            "the monotone open-domain projection was rebuilt from the re-parsed source model, \
             then every exact hybrid cut license and the final PB refutation independently \
             replayed"
                .into(),
        )
    } else {
        (
            false,
            "the rebuilt open-domain residual DOES NOT accept the hybrid PB/LP proof".into(),
        )
    }
}

fn check_open_lift(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.open_domain_hybrid_integer_lift else {
        return (
            false,
            "claim names an open-domain-hybrid-integer-lift block that is absent".into(),
        );
    };
    if crate::open_domain_route::verify_hybrid_integer_lift_infeasibility_certificate(model, proof)
    {
        (
            true,
            "the monotone open-domain projection and bounded-integer radix transform were \
             rebuilt from the re-parsed source model, then the nested hybrid proof \
             independently replayed"
                .into(),
        )
    } else {
        (
            false,
            "the rebuilt open-domain residual DOES NOT accept the integer-lifted hybrid proof"
                .into(),
        )
    }
}

fn check_integer_lift(certificate: &Certificate, model: &Model) -> (bool, String) {
    let Some(proof) = &certificate.hybrid_integer_lift else {
        return (
            false,
            "claim names a hybrid-integer-lift block that is absent".into(),
        );
    };
    match verify_hybrid_integer_lift_infeasibility_certificate(model, proof) {
        Ok(()) => (
            true,
            "the bounded general-integer radix transform was rebuilt and revalidated from the \
             re-parsed source model, then its nested hybrid cut ledger and final PB refutation \
             independently replayed"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the hybrid integer-lift certificate DOES NOT verify: {error}"),
        ),
    }
}

pub(super) fn count_leaves(node: &TreeNode) -> usize {
    let mut stack = vec![node];
    let mut leaves = 0;
    while let Some(node) = stack.pop() {
        match node {
            TreeNode::Leaf { .. } => leaves += 1,
            TreeNode::Split { lo, hi, .. } => {
                stack.push(lo);
                stack.push(hi);
            }
        }
    }
    leaves
}
