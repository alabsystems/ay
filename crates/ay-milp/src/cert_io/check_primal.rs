// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Re-check that the point is feasible in the re-parsed model and attains the
/// claimed value.
pub(super) fn check_primal(
    cert: &Certificate,
    model: &Model,
    claimed_model_value: Option<&BigRational>,
    needs_value: bool,
) -> (bool, String) {
    let Some(x) = &cert.witness else {
        return (false, "claim names a witness block that is absent".into());
    };
    if x.len() != model.num_cols() {
        return (
            false,
            format!(
                "witness has {} entries, the re-parsed model has {} columns",
                x.len(),
                model.num_cols()
            ),
        );
    }
    if let Err(v) = model.check_point(x) {
        return (
            false,
            format!("the point is INFEASIBLE for the model: {v:?}"),
        );
    }
    if needs_value {
        let Some(claimed) = claimed_model_value else {
            return (false, "verdict carries no value to attain".into());
        };
        let attained = model.objective_value_at(x);
        if &attained != claimed {
            return (
                false,
                format!(
                    "the point attains {} (model frame), the verdict claims {claimed}",
                    fmt_rat(&attained)
                ),
            );
        }
    }
    (
        true,
        "the point satisfies every row, column bound and integrality constraint of the re-parsed \
         model, in exact rational arithmetic, and attains the claimed value"
            .into(),
    )
}
