// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Re-check an `objbound` claim: the `rootdual` block proves a VALID BOUND on
/// the model's optimum, and the residual it says it leaves unproved is the
/// residual it actually leaves unproved.
///
/// # What a pass means, and the sentence it must not be read as
///
/// `true` here means "no feasible point of the model is better than `bound`".
/// It does NOT mean the verdict's value is the optimum, and nothing in this
/// file can make it mean that: the `dual` claim is checked separately, by
/// [`check_dual`], against a different block. A certificate whose `dual` claim
/// is `NONE` and whose `objbound` claim verifies is a certificate that proves
/// the optimum lies in an interval and does not prove where in that interval
/// it is — which is exactly what `PARTIAL` (exit 11) says.
///
/// Keeping those two answers apart INSIDE the checker is only half the job.
/// The claim is named `objbound` rather than `dualbound` because every line
/// that publishes a standing delimits a claim name only by what follows it, so
/// a name with `dual` as a prefix hands the shorter name's answer to anyone
/// who greps for it. `CLAIM_NAMES` carries the measurement.
///
/// # Every fact comes from the model or the verdict line
///
/// * The BOUND is re-derived by [`OptimalityCertificate::verify`], which
///   re-prices the multipliers against the re-parsed model's own rows and
///   column bounds.
/// * The OBJECTIVE is compared against the one this checker builds from the
///   model, so a block bounding a DIFFERENT linear function is refused rather
///   than blessed. This is stricter than the `optcert` lane's
///   `check_objective_vector`, which reads a column's `f64` proxy to decide
///   whether the column is in the objective at all; here the rule is the model's
///   own (`f64` advice nonzero OR an exact side-store entry), so a coefficient
///   whose proxy underflowed to zero still counts.
/// * The GAP is re-derived from the block's `bound` and the VERDICT line's
///   value. The block's own `gap` field is compared against that and never
///   used in its place, so an emitter cannot understate its residual.
pub(super) fn check_dual_bound(
    certificate: &Certificate,
    model: &Model,
    claimed: Option<&BigRational>,
) -> (bool, String) {
    let Some(record) = &certificate.root_dual_bound else {
        return (false, "claim names a rootdual block that is absent".into());
    };
    let Some(claimed) = claimed else {
        return (
            false,
            "a root dual bound claim has no verdict value to price its residual against".into(),
        );
    };
    if record.certificate.sense != model.sense() {
        return (false, "the bound is proved for the opposite sense".into());
    }
    if let Err(error) = record.certificate.verify(model) {
        return (
            false,
            format!("the root dual multipliers DO NOT verify: {error}"),
        );
    }
    if let Err(detail) = check_bounds_the_models_objective(&record.certificate, model) {
        return (false, detail);
    }
    let gap = match crate::root_dual::root_dual_gap(&record.certificate, model, claimed) {
        Ok(gap) => gap,
        Err(_) => {
            return (
                false,
                format!(
                    "the block proves a bound of {} which is BETTER than the {claimed} the \
                     verdict line claims: the two records cannot both be true of one model",
                    fmt_rat(&crate::root_dual::root_dual_bound_in_model_frame(
                        &record.certificate,
                        model
                    ))
                ),
            );
        }
    };
    if gap != record.gap {
        return (
            false,
            format!(
                "the block records an unproved residual of {} but the residual re-derived from \
                 its own bound and the verdict line is {}: a certificate may not understate how \
                 much of its optimum is unproved",
                fmt_rat(&record.gap),
                fmt_rat(&gap)
            ),
        );
    }
    let bound = crate::root_dual::root_dual_bound_in_model_frame(&record.certificate, model);
    (
        true,
        format!(
            "the positive multipliers combine, exactly, to the model's own objective priced at \
             the model's own row and column bounds, so no feasible point is better than {} ({}) \
             — a BOUND, not an optimum. The claimed optimum {} ({}) is {} ({}) away from it and \
             THAT RESIDUAL IS NOT PROVED BY THIS CERTIFICATE: this check licenses only that the \
             optimum lies between the two",
            fmt_rat(&bound),
            approx_decimal(&bound),
            fmt_rat(claimed),
            approx_decimal(claimed),
            fmt_rat(&gap),
            approx_decimal(&gap)
        ),
    )
}

/// The block's objective must be the MODEL's objective, coefficient for
/// coefficient.
///
/// A bound on a different linear function is a perfectly valid certificate of
/// something, and blessing it here would let a forger prove a tight bound on a
/// cheap objective and present it as a bound on the expensive one.
fn check_bounds_the_models_objective(
    proof: &OptimalityCertificate,
    model: &Model,
) -> Result<(), String> {
    let mut written = vec![BigRational::zero(); model.num_cols()];
    for (column, coefficient) in &proof.objective {
        let Some(slot) = written.get_mut(*column as usize) else {
            return Err("the block's objective names a missing column".into());
        };
        *slot += coefficient;
    }
    let mut wanted = vec![BigRational::zero(); model.num_cols()];
    for (column, coefficient) in crate::root_dual::model_objective_exact(model) {
        wanted[column as usize] += coefficient;
    }
    for (column, (block, truth)) in written.iter().zip(&wanted).enumerate() {
        if block != truth {
            return Err(format!(
                "the block bounds a DIFFERENT objective (column {column}: block {} vs model {})",
                fmt_rat(block),
                fmt_rat(truth)
            ));
        }
    }
    Ok(())
}
