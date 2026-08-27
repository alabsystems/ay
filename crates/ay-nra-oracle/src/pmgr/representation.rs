// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sparse-polynomial representation and interning checks.

use super::*;

// ---------------------------------------------------------------------------
// 1. Representation
// ---------------------------------------------------------------------------

/// Re-derivation of the manager's documented monomial order, written from the
/// specification rather than shared with it: graded first, then lexicographic
/// with the HIGHER variable index more significant.
fn cmp_mono_spec(a: &[(u32, u32)], b: &[(u32, u32)]) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let da: u32 = a.iter().map(|&(_, e)| e).sum();
    let db: u32 = b.iter().map(|&(_, e)| e).sum();
    match da.cmp(&db) {
        Ordering::Equal => {}
        other => return other,
    }
    let (mut i, mut j) = (a.len(), b.len());
    loop {
        match (i, j) {
            (0, 0) => return Ordering::Equal,
            (0, _) => return Ordering::Less,
            (_, 0) => return Ordering::Greater,
            _ => {}
        }
        let (va, ea) = a[i - 1];
        let (vb, eb) = b[j - 1];
        if va != vb {
            return va.cmp(&vb);
        }
        if ea != eb {
            return ea.cmp(&eb);
        }
        i -= 1;
        j -= 1;
    }
}

/// Canonical form, interning and the recursive `x`-coefficient view.
pub(crate) fn check_pm_rep(g: &GenPm, sab: Sabotage) -> Outcome {
    let mut manager = OPolyMgr::new();
    let planted = manager.mk(&g.g_terms);
    let other = manager.mk(&g.a_terms);
    let product = manager.mul(&planted, &other);
    if manager.is_zero(&product) {
        return Outcome::Skipped("generated product is zero");
    }
    let mut terms = manager.terms(&product);
    if sab.on() && terms.len() >= 2 {
        terms.swap(0, 1);
    }
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_canonical_terms(&manager, &product, &terms),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_degree_queries(&manager, &product, &terms),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_recursive_view(&mut manager, &product),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_representation_identities(&mut manager, g, &product),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_canonical_terms(
    manager: &OPolyMgr,
    product: &OMgrPoly,
    terms: &[(Vec<(u32, u32)>, BigInt)],
) -> Outcome {
    let mut comparisons = 0;
    for pair in terms.windows(2) {
        comparisons += 1;
        if cmp_mono_spec(&pair[0].0, &pair[1].0) != std::cmp::Ordering::Greater {
            return Divergence::outcome(
                "pm-representation",
                "identity",
                format!(
                    "term list is not descending: {:?} then {:?}",
                    pair[0].0, pair[1].0
                ),
                vec![("p".to_string(), render(manager, product))],
            );
        }
    }
    for (powers, coefficient) in terms {
        comparisons += 1;
        if coefficient.is_zero() {
            return Divergence::outcome(
                "pm-representation",
                "identity",
                "a zero coefficient survived normalization".to_string(),
                vec![("p".to_string(), render(manager, product))],
            );
        }
        comparisons += 1;
        if powers.iter().any(|&(_, exponent)| exponent == 0)
            || powers.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        {
            return Divergence::outcome(
                "pm-representation",
                "identity",
                format!("monomial is not canonical: {powers:?}"),
                vec![("p".to_string(), render(manager, product))],
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_degree_queries(
    manager: &OPolyMgr,
    product: &OMgrPoly,
    terms: &[(Vec<(u32, u32)>, BigInt)],
) -> Outcome {
    for variable in 0..NVARS {
        let expected = terms
            .iter()
            .map(|(powers, _)| {
                powers
                    .iter()
                    .find(|&&(candidate, _)| candidate == variable)
                    .map_or(0, |&(_, exponent)| exponent)
            })
            .max()
            .unwrap_or(0);
        if manager.degree(product, variable) != expected {
            return Divergence::outcome(
                "pm-representation",
                "identity",
                format!(
                    "degree(p, x{variable}) = {}, terms say {expected}",
                    manager.degree(product, variable)
                ),
                vec![("p".to_string(), render(manager, product))],
            );
        }
    }
    Outcome::Match(u64::from(NVARS))
}

fn check_recursive_view(manager: &mut OPolyMgr, product: &OMgrPoly) -> Outcome {
    let coefficients = manager.x_coeffs(product, X);
    let reconstructed = manager.from_x_coeffs(X, &coefficients);
    if reconstructed != *product {
        return Divergence::outcome(
            "pm-representation",
            "identity",
            "from_x_coeffs(x_coeffs(p)) != p".to_string(),
            vec![
                ("p".to_string(), render(manager, product)),
                ("back".to_string(), render(manager, &reconstructed)),
            ],
        );
    }
    for (degree, coefficient) in coefficients.iter().enumerate() {
        let direct = manager.coeff(product, X, u32::try_from(degree).unwrap_or(u32::MAX));
        if &direct != coefficient {
            return Divergence::outcome(
                "pm-representation",
                "identity",
                format!("coeff(p, x, {degree}) disagrees with x_coeffs[{degree}]"),
                vec![("p".to_string(), render(manager, product))],
            );
        }
    }
    Outcome::Match(1 + coefficients.len() as u64)
}

fn check_representation_identities(
    manager: &mut OPolyMgr,
    g: &GenPm,
    product: &OMgrPoly,
) -> Outcome {
    let difference = manager.sub(product, product);
    if !manager.is_zero(&difference) {
        return Divergence::outcome(
            "pm-representation",
            "identity",
            "p - p is not the zero polynomial".to_string(),
            vec![("p".to_string(), render(manager, product))],
        );
    }
    let one = manager.constant(BigInt::one());
    if manager.mul(product, &one) != *product {
        return Divergence::outcome(
            "pm-representation",
            "identity",
            "p * 1 != p".to_string(),
            vec![("p".to_string(), render(manager, product))],
        );
    }
    let mut forward = product.clone();
    for (variable, value) in &g.point {
        forward = manager.eval_var(&forward, *variable, value);
    }
    let mut reverse = product.clone();
    for (variable, value) in g.point.iter().rev() {
        reverse = manager.eval_var(&reverse, *variable, value);
    }
    if forward != reverse {
        return Divergence::outcome(
            "pm-representation",
            "identity",
            "substitution is order-dependent".to_string(),
            vec![("p".to_string(), render(manager, product))],
        );
    }
    Outcome::Match(3)
}
