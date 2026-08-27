// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module so the differential checks share one namespace.

// ===========================================================================
// Check 4 — `explain-projection`
// ===========================================================================

/// The CAD projection operator: leading coefficients, discriminants and the
/// resultants of the relevant pairs.
///
/// z3 legs: every resultant and discriminant AY produces is SPECIALIZED at a
/// range of integer points and compared against `Z3_polynomial_subresultants`
/// computed on the specialized univariate pair. Specialization commutes with the
/// resultant exactly when the leading coefficient survives, which is checked
/// before the comparison rather than assumed.
/// Identity legs: the degree report is recomputed from the factors and must
/// match; the constant-factor count must match; `relevant_pairs` must return
/// only in-range, ordered, deduplicated pairs.
/// Guard, fired on purpose: an out-of-range pair index must be refused.
fn projection_inputs(g: &GenEx) -> Result<Vec<OBiPoly>, Outcome> {
    if g.bi.len() < 2 {
        return Err(Outcome::Skipped("need two bivariate inputs"));
    }
    let polys =
        g.bi.iter()
            .map(|coefficients| {
                let terms: Vec<Vec<(u32, BigInt)>> = coefficients
                    .iter()
                    .map(|term| {
                        term.iter()
                            .map(|&(exponent, coefficient)| (exponent, BigInt::from(coefficient)))
                            .collect()
                    })
                    .collect();
                OBiPoly::from_x_coeffs(&terms)
            })
            .collect::<Vec<_>>();
    if polys.iter().any(|poly| poly.degree_x().unwrap_or(0) < 1) {
        return Err(Outcome::Skipped("bivariate degree < 1 in x"));
    }
    Ok(polys)
}

fn validate_projection_contract(
    polys: &[OBiPoly],
    projection: &OProjection,
    g: &GenEx,
) -> Result<(), Outcome> {
    if oexplain_project(polys, &[(0, polys.len())]).is_some() {
        return Err(Divergence::outcome(
            "explain-projection",
            "identity",
            "an out-of-range pair index was accepted".to_string(),
            inputs(g),
        ));
    }
    if oexplain_project(polys, &[]).is_none() {
        return Err(Divergence::outcome(
            "explain-projection",
            "identity",
            "an empty pair list was refused -- the guard fires on valid input".to_string(),
            inputs(g),
        ));
    }
    let recomputed = projection
        .factors
        .iter()
        .map(|(_, factor)| y_total_degree(factor))
        .max()
        .unwrap_or(0);
    if recomputed != projection.out_max_total_degree {
        return Err(Divergence::outcome(
            "explain-projection",
            "identity",
            format!(
                "reported out-degree {} but the factors max at {recomputed}",
                projection.out_max_total_degree
            ),
            inputs(g),
        ));
    }
    Ok(())
}

fn check_leading_factors(
    polys: &[OBiPoly],
    projection: &OProjection,
    g: &GenEx,
    sabotage: Sabotage,
) -> Result<u64, Outcome> {
    let mut comparisons = 0;
    for (idx, poly) in polys.iter().enumerate().take(2) {
        let factor = projection
            .factors
            .iter()
            .find(|(kind, _)| matches!(kind, OProjKind::LeadingCoeff(i) if *i == idx));
        let Some((_, factor)) = factor else {
            continue;
        };
        for point in [-2i64, -1, 0, 1, 2, 3].map(BigInt::from) {
            let Some(leading) = poly.leading_x() else {
                continue;
            };
            let expected = leading.eval_at(&point);
            let mut actual = factor.eval_at(&point);
            if sabotage.on() {
                actual += BigInt::one();
            }
            comparisons += 1;
            if actual != expected {
                return Err(Divergence::outcome(
                    "explain-projection",
                    "identity",
                    format!(
                        "LeadingCoeff({idx}) at x = {point}: projection says {actual}, the \
                         polynomial's own leading coefficient is {expected}"
                    ),
                    inputs(g),
                ));
            }
        }
    }
    Ok(comparisons)
}

fn check_resultant_factor(
    z3: &Z3,
    polys: &[OBiPoly],
    projection: &OProjection,
    g: &GenEx,
    sabotage: Sabotage,
) -> Result<u64, Outcome> {
    let (f, q) = (&polys[0], &polys[1]);
    let (df, dq) = (f.degree_x().unwrap_or(0), q.degree_x().unwrap_or(0));
    let Some(resultant) = projection
        .factors
        .iter()
        .find(|(kind, _)| matches!(kind, OProjKind::Resultant(0, 1)))
        .map(|(_, factor)| factor)
    else {
        return Err(Divergence::outcome(
            "explain-projection",
            "identity",
            "the requested resultant is missing from the projection".to_string(),
            inputs(g),
        ));
    };
    let mut comparisons = 0;
    for point in [-2i64, -1, 0, 1, 2, 3].map(BigInt::from) {
        let preserves_degree = |poly: &OBiPoly| {
            poly.leading_x()
                .is_some_and(|leading| !leading.eval_at(&point).is_zero())
        };
        if !preserves_degree(f) || !preserves_degree(q) {
            continue;
        }
        let mut value = resultant.eval_at(&point);
        if sabotage.on() {
            value += BigInt::one();
        }
        let to_rationals = |poly: &ay_nra::oracle_api::OZPoly| {
            poly.coeffs()
                .into_iter()
                .map(BigRational::from)
                .collect::<Vec<_>>()
        };
        let (sf, sq) = (f.specialize(&point), q.specialize(&point));
        let (zf, zq) = if df >= dq {
            (to_rationals(&sf), to_rationals(&sq))
        } else {
            (to_rationals(&sq), to_rationals(&sf))
        };
        let Some(z3_resultant) = crate::subres::z3_resultant(z3, &zf, &zq) else {
            continue;
        };
        let ordered = if df < dq && (df * dq) % 2 == 1 {
            -value
        } else {
            value
        };
        if ordered != z3_resultant {
            return Err(Divergence::outcome(
                "explain-projection",
                "z3",
                format!(
                    "at y = {point}: AY's Res_x specializes to {ordered}, z3 gives {z3_resultant}"
                ),
                inputs(g),
            ));
        }
        comparisons += 1;
    }
    Ok(comparisons)
}

pub(crate) fn check_projection(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    let polys = match projection_inputs(g) {
        Ok(polys) => polys,
        Err(outcome) => return outcome,
    };
    let Some(projection) = oexplain_project(&polys, &[(0, 1)]) else {
        return Outcome::Declined("projection");
    };
    if let Err(outcome) = validate_projection_contract(&polys, &projection, g) {
        return outcome;
    }
    let mut comparisons = 3;
    match check_leading_factors(&polys, &projection, g, sab) {
        Ok(count) => comparisons += count,
        Err(outcome) => return outcome,
    }
    match check_resultant_factor(z3, &polys, &projection, g, sab) {
        Ok(count) => comparisons += count,
        Err(outcome) => return outcome,
    }
    if comparisons == 3 {
        Outcome::Skipped("every specialization dropped the x-degree")
    } else {
        Outcome::Match(comparisons)
    }
}

/// Total degree of a `y`-polynomial, recomputed by the oracle.
fn y_total_degree(y: &OYPoly) -> u32 {
    y.terms().iter().map(|&(e, _)| e).max().unwrap_or(0)
}

/// `relevant_pairs`, driven directly.
pub(crate) fn check_relevant_pairs(z3: &Z3, g: &GenEx) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(pairs) = oexplain_relevant_pairs(&lits) else {
        return Outcome::Declined("relevant pairs");
    };
    let mut seen = pairs.clone();
    seen.sort_unstable();
    let n = seen.len();
    seen.dedup();
    if seen.len() != n {
        return Divergence::outcome(
            "explain-projection",
            "identity",
            format!("relevant_pairs returned a duplicate: {pairs:?}"),
            inputs(g),
        );
    }
    for &(i, j) in &pairs {
        if i >= j || j >= lits.len() {
            return Divergence::outcome(
                "explain-projection",
                "identity",
                format!("relevant_pairs returned an ill-formed pair ({i}, {j})"),
                inputs(g),
            );
        }
    }
    Outcome::Match(u64::try_from(pairs.len()).unwrap_or(0) + 1)
}
