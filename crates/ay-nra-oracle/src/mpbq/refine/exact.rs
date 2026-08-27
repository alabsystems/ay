// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-root refinement checks.

use super::*;

pub(super) fn check_exact_root(
    case: &RefineCase<'_>,
    index: usize,
    root: Ast,
    rational: &BigRational,
) -> Result<RootCheck, Outcome> {
    let Some(center) = OBq::from_rational(rational) else {
        return Ok(RootCheck::Unusable);
    };
    let Some(interval) = symmetric_exact_interval(case, index, &center)? else {
        return Ok(RootCheck::Unusable);
    };
    let Some(target) = interval.width().div_two_pow(case.g.target_k) else {
        return Err(Outcome::Declined("target underflow"));
    };
    let Some((answer, trace)) = obq_refine_to_width(&case.g.poly, &interval, &target) else {
        return Err(Outcome::Declined(
            "refine_to_width declined on the exact-root bracket",
        ));
    };
    validate_exact_refinement(case, root, &center, answer, trace)?;
    Ok(RootCheck::Matched(5))
}

fn symmetric_exact_interval(
    case: &RefineCase<'_>,
    index: usize,
    center: &OBq,
) -> Result<Option<OBqInterval>, Outcome> {
    for exponent in 0..=24 {
        let delta = OBq::inv_two_pow(exponent);
        let Some(candidate) = OBqInterval::new(&center.sub(&delta), &center.add(&delta)) else {
            continue;
        };
        match (
            obq_poly_sign_at(&case.g.poly, &candidate.lo()),
            obq_poly_sign_at(&case.g.poly, &candidate.hi()),
        ) {
            (Some(lo), Some(hi)) if lo != 0 && hi != 0 => {}
            _ => continue,
        }
        let (Some(lo), Some(hi)) = (
            case.z3.rational(&candidate.lo().to_rational()),
            case.z3.rational(&candidate.hi().to_rational()),
        ) else {
            return Err(Outcome::Skipped("z3 could not build endpoint numerals"));
        };
        let Some(inside) = z3_roots_inside(case.z3, case.roots, lo, hi) else {
            return Err(Outcome::Skipped("z3 errored while ordering roots"));
        };
        if inside == vec![index] {
            return Ok(Some(candidate));
        }
    }
    Ok(None)
}

fn validate_exact_refinement(
    case: &RefineCase<'_>,
    root: Ast,
    center: &OBq,
    answer: ORefined,
    trace: ay_nra::oracle_api::ORefineTrace,
) -> Result<(), Outcome> {
    let ORefined::Exact(value) = answer else {
        return Err(Divergence::outcome(
            "bq-refine",
            "identity",
            "a symmetric bracket around a dyadic root did not report Exact".into(),
            vec![
                ("poly".into(), render_poly(&case.g.poly)),
                ("root".into(), render_bq(center)),
            ],
        ));
    };
    if value != *center {
        return Err(Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "Exact reported {}, but the root is {}",
                render_bq(&value),
                render_bq(center)
            ),
            vec![("poly".into(), render_poly(&case.g.poly))],
        ));
    }
    if obq_poly_sign_at(&case.g.poly, &value) != Some(0) {
        return Err(Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "claimed exact root {} does not zero the polynomial",
                render_bq(&value)
            ),
            vec![("poly".into(), render_poly(&case.g.poly))],
        ));
    }
    let Some(ast) = case.z3.rational(&value.to_rational()) else {
        return Err(Outcome::Skipped(
            "z3 could not build the exact-root numeral",
        ));
    };
    let Some(equal) = case.z3.eq(ast, root) else {
        return Err(Outcome::Skipped(
            "z3 errored while comparing the exact root",
        ));
    };
    if !equal {
        return Err(Divergence::outcome(
            "bq-refine",
            "z3",
            format!("AY says the root is exactly {}", render_bq(&value)),
            vec![
                ("poly".into(), render_poly(&case.g.poly)),
                (
                    "z3 root".into(),
                    case.z3
                        .ast_string(root)
                        .unwrap_or_else(|| "<invalid-z3-ast>".into()),
                ),
            ],
        ));
    }
    validate_exact_trace(case, &value, &trace)
}

fn validate_exact_trace(
    case: &RefineCase<'_>,
    value: &OBq,
    trace: &ay_nra::oracle_api::ORefineTrace,
) -> Result<(), Outcome> {
    if trace.steps != 1 {
        return Err(Divergence::outcome(
            "bq-refine",
            "identity",
            format!("exact root found after {} steps, expected 1", trace.steps),
            vec![("poly".into(), render_poly(&case.g.poly))],
        ));
    }
    if trace.end_max_k != value.k() {
        return Err(Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "end_max_k {} != exact root k {}",
                trace.end_max_k,
                value.k()
            ),
            vec![("poly".into(), render_poly(&case.g.poly))],
        ));
    }
    Ok(())
}
