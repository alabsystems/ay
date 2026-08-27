// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete finite-field factorization checks.

use super::*;

// ---------------------------------------------------------------------------
// Check 4: complete factorization over Z_p
// ---------------------------------------------------------------------------

/// Complete factorization over `Z_p`, against the perfect identity plus the
/// independent irreducibility witness.
///
///   (a) `lc * prod f_i^{e_i} == input`, EXACTLY;
///   (b) every `f_i` is monic of degree `>= 1`, and the `f_i` are pairwise
///       distinct — a factorizer that returns the same factor twice instead of
///       raising its multiplicity still satisfies (a);
///   (c) every `f_i` is irreducible by **Rabin's test**, which is what catches
///       an under-factorization that (a) cannot see;
///   (d) `sum deg(f_i) * e_i == deg(input)`;
///   (e) the counter pin: `edf_splits == (number of factors produced by
///       equal-degree) - (number of buckets fed to it)`.
pub(crate) fn check_factor(g: &GenUp, sab: Sabotage) -> Outcome {
    let Some(manager) = OZpMgr::new(g.p) else {
        return Outcome::Declined("modulus refused");
    };
    let reduced = manager.reduce(&build_z(g));
    let Some(degree) = reduced.degree() else {
        return Outcome::Skipped("reduction vanished");
    };
    if degree == 0 {
        return Outcome::Skipped("reduction is a constant");
    }
    manager.reset_stats();
    let Some((leading, mut factors)) = manager.factor(&reduced) else {
        return Outcome::Declined("factor refused");
    };
    let splits = manager.stats().edf_splits;
    if sab.on() {
        if factors.len() >= 2 && factors[0].1 == factors[1].1 {
            let merged = manager.mul(&factors[0].0, &factors[1].0);
            let multiplicity = factors[0].1;
            factors.drain(0..2);
            factors.push((merged, multiplicity));
        } else if let Some(first) = factors.first().cloned() {
            factors.push(first);
        } else {
            return Outcome::Skipped("nothing to sabotage");
        }
    }
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_factor_product(&manager, &reduced, leading, &factors),
    ) {
        return outcome;
    }
    let (total_degree, shape_comparisons) = match check_factor_shape(&manager, &reduced, &factors) {
        Ok(value) => value,
        Err(outcome) => return outcome,
    };
    comparisons += shape_comparisons;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_irreducibility(&manager, &reduced, &factors),
    ) {
        return outcome;
    }
    if total_degree != degree {
        return Divergence::outcome(
            "up-zp-factor",
            "identity",
            format!("degrees sum to {total_degree}, input degree is {degree}"),
            vec![("input".to_string(), render_zp(&manager, &reduced))],
        );
    }
    comparisons += 1;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_factor_counter(&manager, &reduced, splits),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_factor_product(
    manager: &OZpMgr,
    reduced: &OUniZp,
    leading: u64,
    factors: &[(OUniZp, usize)],
) -> Outcome {
    let mut product = manager.from_u64(vec![leading]);
    for (factor, multiplicity) in factors {
        for _ in 0..*multiplicity {
            product = manager.mul(&product, factor);
        }
    }
    if product != *reduced {
        return Divergence::outcome(
            "up-zp-factor",
            "identity",
            "lc * prod f_i^e_i != input".to_string(),
            vec![
                ("input".to_string(), render_zp(manager, reduced)),
                ("lc".to_string(), leading.to_string()),
                (
                    "factors".to_string(),
                    render_factorization(manager, factors),
                ),
                ("product".to_string(), render_zp(manager, &product)),
            ],
        );
    }
    Outcome::Match(1)
}

fn render_factorization(manager: &OZpMgr, factors: &[(OUniZp, usize)]) -> String {
    factors
        .iter()
        .map(|(factor, exponent)| format!("({})^{exponent}", render_zp(manager, factor)))
        .collect::<Vec<_>>()
        .join(" * ")
}

fn check_factor_shape(
    manager: &OZpMgr,
    reduced: &OUniZp,
    factors: &[(OUniZp, usize)],
) -> Result<(usize, u64), Outcome> {
    let mut total_degree = 0;
    let mut comparisons = 0;
    for (factor, multiplicity) in factors {
        comparisons += 1;
        if factor.lc() != Some(1) || factor.degree().unwrap_or(0) == 0 || *multiplicity == 0 {
            return Err(Divergence::outcome(
                "up-zp-factor",
                "identity",
                "factor is non-monic, constant, or has zero multiplicity".to_string(),
                vec![
                    ("input".to_string(), render_zp(manager, reduced)),
                    ("factor".to_string(), render_zp(manager, factor)),
                    ("mult".to_string(), multiplicity.to_string()),
                ],
            ));
        }
        total_degree += factor.degree().unwrap_or(0) * *multiplicity;
    }
    for first in 0..factors.len() {
        for second in first + 1..factors.len() {
            comparisons += 1;
            if factors[first].0 == factors[second].0 {
                return Err(Divergence::outcome(
                    "up-zp-factor",
                    "identity",
                    format!("factors {first} and {second} are equal"),
                    vec![
                        ("input".to_string(), render_zp(manager, reduced)),
                        ("factor".to_string(), render_zp(manager, &factors[first].0)),
                    ],
                ));
            }
        }
    }
    Ok((total_degree, comparisons))
}

fn check_irreducibility(
    manager: &OZpMgr,
    reduced: &OUniZp,
    factors: &[(OUniZp, usize)],
) -> Outcome {
    let mut comparisons = 0;
    for (factor, _) in factors {
        let Some(irreducible) = manager.is_irreducible(factor) else {
            return Outcome::Declined("irreducibility test refused");
        };
        comparisons += 1;
        if !irreducible {
            return Divergence::outcome(
                "up-zp-factor",
                "identity",
                "returned factor is reducible by Rabin's test".to_string(),
                vec![
                    ("input".to_string(), render_zp(manager, reduced)),
                    ("factor".to_string(), render_zp(manager, factor)),
                ],
            );
        }
    }
    if factors.len() >= 2 {
        let composite = manager.mul(&factors[0].0, &factors[1].0);
        let Some(irreducible) = manager.is_irreducible(&composite) else {
            return Outcome::Declined("irreducibility test refused a composite");
        };
        comparisons += 1;
        if irreducible {
            return Divergence::outcome(
                "up-zp-factor",
                "identity",
                "irreducibility test called a product irreducible".to_string(),
                vec![
                    ("input".to_string(), render_zp(manager, reduced)),
                    ("f0".to_string(), render_zp(manager, &factors[0].0)),
                    ("f1".to_string(), render_zp(manager, &factors[1].0)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_factor_counter(manager: &OZpMgr, reduced: &OUniZp, actual: u64) -> Outcome {
    let Some((_, monic)) = manager.monic(reduced) else {
        return Outcome::Declined("monic refused");
    };
    let Some(square_free) = manager.square_free_decomposition(&monic) else {
        return Outcome::Declined("square-free decomposition refused");
    };
    let mut buckets = 0;
    let mut produced = 0;
    for (factor, _) in &square_free {
        let Some(degrees) = manager.distinct_degree(factor) else {
            return Outcome::Declined("distinct_degree refused");
        };
        for (bucket, degree) in degrees {
            buckets += 1;
            produced += bucket.degree().unwrap_or(0) / degree.max(1);
        }
    }
    let expected = u64::try_from(produced.saturating_sub(buckets)).unwrap_or(0);
    if actual != expected {
        return Divergence::outcome(
            "up-zp-factor",
            "identity",
            format!(
                "edf_splits says {actual}, but {produced} factors from {buckets} buckets imply {expected}"
            ),
            vec![("input".to_string(), render_zp(manager, reduced))],
        );
    }
    Outcome::Match(1)
}
