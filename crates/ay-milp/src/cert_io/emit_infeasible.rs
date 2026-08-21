// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn emit_infeasible(emission: &mut Emission<'_, '_>, outcome: &Outcome) -> String {
    let Outcome::Infeasible { cert, tree_cert } = outcome else {
        return String::new();
    };
    let claim = if let Some(claim) = primary_claim(emission, cert.as_ref(), tree_cert.as_ref()) {
        claim
    } else if let Some(claim) = projected_claim(emission) {
        claim
    } else if let Some(claim) = encoded_claim(emission) {
        claim
    } else {
        infeasible_claim_from_replay(emission.ctx)
    };
    emission.claims.push(claim);
    "verdict infeasible".to_owned()
}

fn primary_claim(
    emission: &mut Emission<'_, '_>,
    cert: Option<&FarkasCertificate>,
    tree: Option<&MilpInfeasibilityCertificate>,
) -> Option<EmittedClaim> {
    if let Some(certificate) = cert {
        return Some(emission.block_claim(
            "infeasible",
            farkas_block(certificate),
            "farkas",
            "farkas",
        ));
    }
    if let Some(certificate) = tree {
        return Some(emission.block_claim("infeasible", tree_block(certificate), "tree", "tree"));
    }
    if let Some(certificate) = emission.ctx.sat_relu_infeasibility_certificate {
        let limit = emission
            .ctx
            .max_bytes
            .map_or(MAX_SAT_RELU_RUP_BYTES, |cap| {
                cap.saturating_sub(emission.blocks.len())
                    .min(MAX_SAT_RELU_RUP_BYTES)
            });
        return Some(emission.codec_claim(
            "infeasible",
            sat_relu_rup_block(certificate, limit),
            "sat-relu-rup",
            "sat-relu-rup",
        ));
    }
    if let Some(certificate) = emission
        .ctx
        .affine_aggregation_certificate
        .filter(supports_affine_infeasibility)
    {
        return Some(emission.affine_claim("infeasible", certificate));
    }
    emission
        .ctx
        .parity_infeasibility_certificate
        .map(|certificate| {
            emission.block_claim(
                "infeasible",
                parity_infeasibility_block(certificate),
                "parity-gf2",
                "parity-gf2",
            )
        })
}

fn projected_claim(emission: &mut Emission<'_, '_>) -> Option<EmittedClaim> {
    if let Some(certificate) = emission.ctx.network_design_infeasibility_certificate {
        return Some(emission.codec_claim(
            "infeasible",
            network_design_infeasibility_block(certificate),
            "network-design-infeasibility",
            "network-design-infeasibility",
        ));
    }
    if let Some(certificate) = emission.ctx.single_row_dp_infeasibility_certificate {
        return Some(emission.codec_claim(
            "infeasible",
            single_row_dp_block(certificate),
            "single-row-dp",
            "single-row-dp",
        ));
    }
    if let Some(certificate) = emission.ctx.multi_row_bdd_infeasibility_certificate {
        return Some(emission.codec_claim(
            "infeasible",
            multi_row_bdd_block(certificate),
            "multi-row-bdd",
            "multi-row-bdd",
        ));
    }
    if let Some(certificate) = emission
        .ctx
        .open_domain_single_row_dp_infeasibility_certificate
    {
        return Some(emission.codec_claim(
            "infeasible",
            open_domain_dp_block(certificate),
            "open-domain-dp",
            "open-domain-dp",
        ));
    }
    emission
        .ctx
        .open_domain_multi_row_bdd_infeasibility_certificate
        .map(|certificate| {
            emission.codec_claim(
                "infeasible",
                open_domain_bdd_block(certificate),
                "open-domain-bdd",
                "open-domain-bdd",
            )
        })
}

fn encoded_claim(emission: &mut Emission<'_, '_>) -> Option<EmittedClaim> {
    if let Some(certificate) = emission
        .ctx
        .open_domain_hybrid_pb_lp_infeasibility_certificate
    {
        return Some(emission.codec_claim(
            "infeasible",
            open_domain_hybrid_pb_lp_block(certificate),
            "open-domain-hybrid-pb-lp",
            "open-domain-hybrid-pb-lp",
        ));
    }
    if let Some(certificate) = emission
        .ctx
        .open_domain_hybrid_integer_lift_infeasibility_certificate
    {
        return Some(emission.codec_claim(
            "infeasible",
            open_domain_hybrid_integer_lift_block(certificate),
            "open-domain-hybrid-integer-lift",
            "open-domain-hybrid-integer-lift",
        ));
    }
    if let Some(certificate) = emission.ctx.hybrid_pb_lp_infeasibility_certificate {
        return Some(emission.codec_claim(
            "infeasible",
            hybrid_pb_lp_block(certificate),
            "hybrid-pb-lp",
            "hybrid-pb-lp",
        ));
    }
    emission
        .ctx
        .hybrid_integer_lift_infeasibility_certificate
        .map(|certificate| {
            emission.codec_claim(
                "infeasible",
                hybrid_integer_lift_block(certificate),
                "hybrid-integer-lift",
                "hybrid-integer-lift",
            )
        })
}

fn supports_affine_infeasibility(certificate: &&AffineAggregationCertificate) -> bool {
    matches!(
        (&certificate.claim, &certificate.inner_proof),
        (
            AffineAggregationClaim::Infeasible,
            AffineAggregationInnerProof::Farkas(_)
                | AffineAggregationInnerProof::InfeasibilityTree(_)
        )
    )
}
