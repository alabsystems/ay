// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn emit_optimal(emission: &mut Emission<'_, '_>, outcome: &Outcome) -> String {
    let Outcome::Optimal {
        value,
        model_values,
        cert,
    } = outcome
    else {
        return String::new();
    };
    let primal = emission.block_claim(
        "primal",
        witness_block(emission.ctx, model_values),
        "witness",
        "witness",
    );
    emission.claims.push(primal);
    let dual = if let Some(certificate) = cert {
        emission.block_claim(
            "dual",
            optcert_block(certificate, is_trivial_optcert(certificate)),
            "optcert",
            "optcert",
        )
    } else {
        emit_special_optimality(emission)
    };
    emission.claims.push(dual);
    format!(
        "verdict optimal value={} frame=file",
        fmt_rat(&(value / emission.ctx.obj_scale))
    )
}

fn emit_special_optimality(emission: &mut Emission<'_, '_>) -> EmittedClaim {
    if let Some(certificate) = emission.ctx.block_angular_optimality_certificate {
        return emission.block_claim(
            "dual",
            block_angular_optimality_block(certificate),
            "block-angular-optimality",
            "block-angular-optimality",
        );
    }
    if let Some(certificate) = emission
        .ctx
        .affine_aggregation_certificate
        .filter(supports_affine_optimality)
    {
        return emission.affine_claim("dual", certificate);
    }
    if let Some(certificate) = emission
        .ctx
        .single_machine_scheduling_optimality_certificate
    {
        return emission.block_claim(
            "dual",
            single_machine_scheduling_optimality_block(certificate),
            "single-machine-scheduling-optimality",
            "single-machine-scheduling-optimality",
        );
    }
    if let Some(certificate) = emission.ctx.network_design_optimality_certificate {
        let body = network_design_optimality_block(certificate);
        return emission.codec_claim(
            "dual",
            body,
            "network-design-optimality",
            "network-design-optimality",
        );
    }
    // THE GENERAL LANE, LAST AMONG THE SUCCINCT ONES. Every artifact above
    // recognises a STRUCTURE and, where it fires, produces a smaller and
    // cheaper-to-check object than a whole split tree. The tree applies to any
    // branched MILP, so its job is to catch what those miss -- which makes this
    // lane purely ADDITIVE: no verdict that already shipped succinct dual
    // evidence has its evidence changed by the tree existing.
    if let Some(certificate) = emission.ctx.milp_optimality_tree_certificate {
        return emission.block_claim(
            "dual",
            opt_tree_block(&certificate.root),
            "optimality-tree",
            "optimality-tree",
        );
    }
    dual_claim_from_replay(
        emission.ctx,
        &[
            "objective-face-empty",
            "pb-projection-optimal",
            "pb-portfolio-projection-optimal",
            "network-design-projection-optimal",
            "open-domain-cap-optimal",
            "hybrid-pb-lp-optimal",
        ],
    )
}

fn supports_affine_optimality(certificate: &&AffineAggregationCertificate) -> bool {
    matches!(
        (&certificate.claim, &certificate.inner_proof),
        (
            AffineAggregationClaim::Optimal { .. },
            AffineAggregationInnerProof::Optimality(_)
        )
    )
}
