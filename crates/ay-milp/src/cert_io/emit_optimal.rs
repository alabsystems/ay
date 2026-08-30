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
    // SUBORDINATE, AND ONLY WHERE THERE IS NOTHING TO BE SUBORDINATE TO. A root
    // bound proves strictly less than the dual claim it sits beside, so it is
    // offered only where that claim came out unbacked. Where an artifact already
    // proves the optimum, adding a weaker statement about the same model would
    // be noise at best and, at worst, an invitation to read the pair as one
    // hedged claim.
    let dual_is_backed = dual.kind == EvidenceKind::Succinct;
    emission.claims.push(dual);
    if !dual_is_backed {
        if let Some(claim) = emit_root_dual_bound(emission, value) {
            emission.claims.push(claim);
        }
    }
    format!(
        "verdict optimal value={} frame=file",
        fmt_rat(&(value / emission.ctx.obj_scale))
    )
}

/// The `objbound` claim: a checkable bound that is NOT the optimum, with the
/// residual it leaves unproved written into the block.
///
/// The name does not contain `dual` ON PURPOSE. It is checked by a separate
/// arm, reported under a separate standing and refused by a separate policy,
/// and none of that survives contact with a reader if the token it is printed
/// under has `dual` as a prefix -- see `CLAIM_NAMES` for the measured failure
/// that costs.
///
/// Returns `None` — emitting nothing at all — when the derived bound is not
/// consistent with the verdict being certified. That is the fail-closed
/// direction: a bound BETTER than the claimed optimum would mean the verdict is
/// wrong, and dressing that contradiction up as evidence is the one thing this
/// lane must never do.
fn emit_root_dual_bound(
    emission: &mut Emission<'_, '_>,
    value: &BigRational,
) -> Option<EmittedClaim> {
    let certificate = emission.ctx.root_dual_bound_certificate?;
    // The RESIDUAL is derived here from the certificate and the verdict value,
    // by the same function the checker re-runs. There is no separate emitter
    // arithmetic for it to drift from.
    let gap = crate::root_dual::root_dual_gap(certificate, emission.ctx.model, value).ok()?;
    Some(emission.block_claim(
        "objbound",
        root_dual_block(certificate, &gap),
        "root-dual-bound",
        "root-dual-bound",
    ))
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
