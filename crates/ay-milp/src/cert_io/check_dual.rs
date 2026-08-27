// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Re-check the universal bound, its exact objective vector, and the claimed
/// optimum in the certificate's declared frame.
pub(super) fn check_dual(
    certificate: &Certificate,
    model: &Model,
    claimed_value: Option<&BigRational>,
    source: Option<&str>,
    affine: Option<&Result<AffineAggregationVerification, AffineAggregationCertificateError>>,
) -> (bool, String) {
    match source {
        Some("block-angular-optimality") => check_block_angular(certificate, model, claimed_value),
        Some("affine-aggregation") => check_affine_dual(certificate, claimed_value, affine),
        Some("single-machine-scheduling-optimality") => {
            check_scheduling(certificate, model, claimed_value)
        }
        Some("network-design-optimality") => {
            check_network_optimality(certificate, model, claimed_value)
        }
        Some("optcert") => check_optcert(certificate, model, claimed_value),
        Some("optimality-tree") => check_optimality_tree(certificate, model, claimed_value),
        _ => (false, "claim names an unsupported dual block".into()),
    }
}

/// Re-derive the DUAL half of an optimality claim from the `opttree` block.
///
/// Every fact this consults comes from the re-parsed model or from the verdict
/// line; the block itself contributes only a split skeleton and multiplier
/// lists. In particular the leaf boxes are RECONSTRUCTED by
/// [`verify_optimality_tree_bound`] (model column bounds intersected with the
/// path's splits) rather than read, and the target is `claimed` — the same
/// value `check_primal` pins the witness to — so the two halves cannot be
/// priced against different numbers.
fn check_optimality_tree(
    certificate: &Certificate,
    model: &Model,
    claimed: Option<&BigRational>,
) -> (bool, String) {
    let Some(root) = &certificate.opt_tree else {
        return (false, "claim names an opttree block that is absent".into());
    };
    let Some(claimed) = claimed else {
        return (
            false,
            "an optimality-tree claim has no verdict value to be priced against".into(),
        );
    };
    match verify_optimality_tree_bound(model, claimed, root) {
        Ok(()) => (
            true,
            "every leaf of the split tree was re-priced in exact rational arithmetic at a box \
             reconstructed from the re-parsed model's own column bounds intersected with the \
             branch path, and each is either Farkas-empty or carries positive multipliers whose \
             oriented combination is the model's objective bounded by the claimed value; the \
             splits are integer cuts on integral columns, so the leaves tile the feasible set"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the whole-tree optimality artifact DOES NOT verify: {error}"),
        ),
    }
}

fn check_block_angular(
    certificate: &Certificate,
    model: &Model,
    claimed: Option<&BigRational>,
) -> (bool, String) {
    let Some(proof) = &certificate.block_angular_optimality else {
        return (
            false,
            "claim names a block-angular-optimality block that is absent".into(),
        );
    };
    let Some(claimed) = claimed else {
        return (
            false,
            "block-angular optimality claim has no verdict value".into(),
        );
    };
    match crate::block_angular_route::verify_optimality_certificate(model, claimed, proof) {
        Ok(()) => (
            true,
            "the integral conservation-chain decomposition was rebuilt from the source model, \
             every bounded capacity tuple and chain exit was re-priced exactly, and the \
             resulting Lagrangian lower bound meets the claimed optimum"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the block-angular optimality artifact DOES NOT verify: {error}"),
        ),
    }
}

fn check_affine_dual(
    certificate: &Certificate,
    claimed: Option<&BigRational>,
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
    if !verification.optimality_verified {
        return (
            false,
            "the affine artifact carries no verified reduced-frame optimality proof".into(),
        );
    }
    let AffineAggregationClaim::Optimal { value } = artifact.claim() else {
        return (
            false,
            "the affine artifact does not claim optimality".into(),
        );
    };
    let Some(claimed) = claimed else {
        return (false, "affine optimality has no verdict value".into());
    };
    if value != claimed {
        return (
            false,
            "the affine artifact and outer verdict claim different optimum values".into(),
        );
    }
    (
        true,
        "threshold-free exact propagation licensed the recorded analysis box; every affine \
         substitution, digest and objective delta replayed; the reduced-frame dual proof \
         verified against the rebuilt reduced model; and the widened source point attained \
         the same exact optimum"
            .into(),
    )
}

fn check_scheduling(
    certificate: &Certificate,
    model: &Model,
    claimed: Option<&BigRational>,
) -> (bool, String) {
    let Some(proof) = &certificate.single_machine_scheduling_optimality else {
        return (
            false,
            "claim names a single-machine-scheduling-optimality block that is absent".into(),
        );
    };
    let Some(claimed) = claimed else {
        return (
            false,
            "single-machine scheduling claim has no verdict value".into(),
        );
    };
    match crate::scheduling_route::verify_optimality_certificate(model, claimed, proof) {
        Ok(()) => (
            true,
            "the source scheduling formulation and sequence were rebuilt and checked in exact \
             arithmetic, and an independent bounded subset/Pareto DP replay proved the claimed \
             optimum"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the single-machine scheduling optimality artifact DOES NOT verify: {error}"),
        ),
    }
}

fn check_network_optimality(
    certificate: &Certificate,
    model: &Model,
    claimed: Option<&BigRational>,
) -> (bool, String) {
    let Some(proof) = &certificate.network_design_optimality else {
        return (
            false,
            "claim names a network-design-optimality block that is absent".into(),
        );
    };
    let Some(claimed) = claimed else {
        return (
            false,
            "network-design optimality claim has no verdict value".into(),
        );
    };
    match crate::network_design_route::verify_optimality_certificate(model, claimed, proof) {
        Ok(()) => (
            true,
            "the exact Hoffman projection was rebuilt from the re-parsed model, and an \
             independent exact PB artifact replay proved the claimed master optimum"
                .into(),
        ),
        Err(error) => (
            false,
            format!("the network-design optimality artifact DOES NOT verify: {error}"),
        ),
    }
}

fn check_optcert(
    certificate: &Certificate,
    model: &Model,
    claimed: Option<&BigRational>,
) -> (bool, String) {
    let Some(proof) = &certificate.optcert else {
        return (false, "claim names an optcert block that is absent".into());
    };
    if let Err(error) = proof.verify(model) {
        return (
            false,
            format!("the dual multipliers DO NOT verify: {error}"),
        );
    }
    if proof.sense != model.sense() {
        return (false, "the certificate bounds the opposite sense".into());
    }
    if let Err(detail) = check_objective_vector(proof, model) {
        return (false, detail);
    }
    let Some(claimed) = claimed else {
        return (
            true,
            format!(
                "the multipliers prove a valid bound of {} on the model's objective (no verdict \
                 value to meet)",
                fmt_rat(&proof.bound)
            ),
        );
    };
    let bound = &proof.bound + model.obj_offset_exact();
    if &bound != claimed {
        return (
            false,
            format!(
                "the dual bound is {} (offset included) but the verdict claims the optimum is \
                 {claimed}: this certificate does NOT prove that optimum",
                fmt_rat(&bound)
            ),
        );
    }
    (
        true,
        "the positive multipliers combine, exactly, to the model's own objective minus the \
         claimed optimum: no feasible point can beat it"
            .into(),
    )
}

fn check_objective_vector(proof: &OptimalityCertificate, model: &Model) -> Result<(), String> {
    let mut certificate_objective = vec![BigRational::zero(); model.num_cols()];
    for (column, coefficient) in &proof.objective {
        let Some(slot) = certificate_objective.get_mut(*column as usize) else {
            return Err("the certificate's objective names a missing column".into());
        };
        *slot += coefficient;
    }
    for (column, certificate_value) in certificate_objective.iter().enumerate() {
        let handle = Col(column as u32);
        let coefficient = model.obj_coeff(handle);
        let model_value = if coefficient == 0.0 {
            BigRational::zero()
        } else {
            model.obj_coeff_exact_at(column as u32, coefficient)
        };
        if certificate_value != &model_value {
            return Err(format!(
                "the certificate bounds a DIFFERENT objective (column {column}: certificate {} \
                 vs model {})",
                fmt_rat(certificate_value),
                fmt_rat(&model_value)
            ));
        }
    }
    Ok(())
}
