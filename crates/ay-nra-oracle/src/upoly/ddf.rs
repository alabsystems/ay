// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Distinct-degree factorization checks over finite fields.

use super::*;

// ---------------------------------------------------------------------------
// Check 3: distinct-degree factorization over Z_p
// ---------------------------------------------------------------------------

/// Distinct-degree factorization, in ISOLATION.
///
/// It gets its own check rather than being covered through `factor` because a
/// bucket that is assigned the WRONG degree label still multiplies back
/// correctly — the product identity is blind to `d`. What is not blind to `d`
/// is the field-theoretic characterization, which this check applies directly:
///
///   (a) `prod g_d == a` exactly;
///   (b) `deg(g_d)` is divisible by `d`;
///   (c) **the independent witness**: every root of `g_d` lies in `F_(p^d)`,
///       i.e. `x^(p^d) == x (mod g_d)`, and in NO smaller field, i.e.
///       `gcd(x^(p^e) - x, g_d) == 1` for every proper divisor `e` of `d`.
///       That is computed here in the oracle from `powmod`/`gcd` alone and
///       never touches AY's distinct-degree loop.
///   (d) **the counter pin**: `ddf_iters` is re-derived exactly by replaying
///       the loop's stopping condition against the returned buckets.
pub(crate) fn check_ddf(g: &GenUp, sab: Sabotage) -> Outcome {
    let Some(manager) = OZpMgr::new(g.p) else {
        return Outcome::Declined("modulus refused");
    };
    let reduced = manager.reduce(&build_z(g));
    if reduced.is_zero() || reduced.degree() == Some(0) {
        return Outcome::Skipped("reduction collapsed the input");
    }
    let Some((_, monic)) = manager.monic(&reduced) else {
        return Outcome::Declined("monic refused");
    };
    let Some(square_free) = manager.square_free_decomposition(&monic) else {
        return Outcome::Declined("square-free decomposition refused");
    };
    let mut radical = manager.one();
    for (factor, _) in &square_free {
        radical = manager.mul(&radical, factor);
    }
    if radical.degree().unwrap_or(0) == 0 {
        return Outcome::Skipped("radical is constant");
    }
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_square_free_precondition(&manager, &monic, &square_free),
    ) {
        return outcome;
    }
    manager.reset_stats();
    let Some(mut buckets) = manager.distinct_degree(&radical) else {
        return Outcome::Declined("distinct_degree refused");
    };
    let iterations = manager.stats().ddf_iters;
    if sab.on() {
        if let Some(bucket) = buckets.first_mut() {
            bucket.1 += 1;
        } else {
            return Outcome::Skipped("nothing to sabotage");
        }
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_ddf_product(&manager, &radical, &buckets),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_field_degree_witness(g, &manager, &buckets),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_equal_degree(&manager, &buckets)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_ddf_counter(&manager, &radical, &buckets, iterations),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_square_free_precondition(
    manager: &OZpMgr,
    monic: &OUniZp,
    factors: &[(OUniZp, usize)],
) -> Outcome {
    let mut product = manager.one();
    let mut comparisons = 0;
    for (factor, multiplicity) in factors {
        comparisons += 1;
        let derivative = manager.derivative(factor);
        let gcd = manager.gcd(factor, &derivative);
        if derivative.is_zero() || gcd.degree() != Some(0) {
            return Divergence::outcome(
                "up-zp-ddf",
                "identity",
                format!(
                    "factor multiplicity {multiplicity} is not square-free: gcd degree {:?}",
                    gcd.degree()
                ),
                vec![
                    ("input".to_string(), render_zp(manager, monic)),
                    ("factor".to_string(), render_zp(manager, factor)),
                ],
            );
        }
        for _ in 0..*multiplicity {
            product = manager.mul(&product, factor);
        }
    }
    comparisons += 1;
    if product != *monic {
        return Divergence::outcome(
            "up-zp-ddf",
            "identity",
            "prod g_i^m_i != monic input".to_string(),
            vec![
                ("input".to_string(), render_zp(manager, monic)),
                ("product".to_string(), render_zp(manager, &product)),
            ],
        );
    }
    Outcome::Match(comparisons)
}

fn check_ddf_product(manager: &OZpMgr, radical: &OUniZp, buckets: &[(OUniZp, usize)]) -> Outcome {
    let mut product = manager.one();
    for (factor, _) in buckets {
        product = manager.mul(&product, factor);
    }
    if product != *radical {
        return Divergence::outcome(
            "up-zp-ddf",
            "identity",
            "product of distinct-degree buckets != input".to_string(),
            vec![
                ("input".to_string(), render_zp(manager, radical)),
                ("product".to_string(), render_zp(manager, &product)),
            ],
        );
    }
    Outcome::Match(1)
}

fn check_field_degree_witness(g: &GenUp, manager: &OZpMgr, buckets: &[(OUniZp, usize)]) -> Outcome {
    let x = manager.from_u64(vec![0, 1]);
    let characteristic = BigInt::from(g.p);
    let mut comparisons = 0;
    for (factor, degree) in buckets {
        let Some(factor_degree) = factor.degree() else {
            return Outcome::Skipped("empty bucket");
        };
        comparisons += 1;
        if *degree == 0 || factor_degree % *degree != 0 {
            return Divergence::outcome(
                "up-zp-ddf",
                "identity",
                format!("bucket degree {factor_degree} labelled d={degree}"),
                vec![("bucket".to_string(), render_zp(manager, factor))],
            );
        }
        let mut power = x.clone();
        for _ in 0..*degree {
            let Some(next) = manager.powmod(&power, &characteristic, factor) else {
                return Outcome::Declined("powmod refused");
            };
            power = next;
        }
        let Some((_, reduced_x)) = manager.div_rem(&x, factor) else {
            return Outcome::Declined("div_rem refused");
        };
        comparisons += 1;
        if power != reduced_x {
            return Divergence::outcome(
                "up-zp-ddf",
                "identity",
                format!("d={degree} bucket does not satisfy x^(p^d) == x"),
                vec![("bucket".to_string(), render_zp(manager, factor))],
            );
        }
        match check_proper_subfields(manager, factor, *degree, &x, &characteristic) {
            Outcome::Match(n) => comparisons += n,
            other => return other,
        }
    }
    Outcome::Match(comparisons)
}

fn check_proper_subfields(
    manager: &OZpMgr,
    factor: &OUniZp,
    degree: usize,
    x: &OUniZp,
    characteristic: &BigInt,
) -> Outcome {
    let mut comparisons = 0;
    for divisor in 1..degree {
        if !degree.is_multiple_of(divisor) {
            continue;
        }
        let mut power = x.clone();
        for _ in 0..divisor {
            let Some(next) = manager.powmod(&power, characteristic, factor) else {
                return Outcome::Declined("powmod refused");
            };
            power = next;
        }
        let gcd = manager.gcd(&manager.sub(&power, x), factor);
        comparisons += 1;
        if gcd.degree() != Some(0) {
            return Divergence::outcome(
                "up-zp-ddf",
                "identity",
                format!("d={degree} bucket has a factor of degree {divisor}"),
                vec![
                    ("bucket".to_string(), render_zp(manager, factor)),
                    ("gcd".to_string(), render_zp(manager, &gcd)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_equal_degree(manager: &OZpMgr, buckets: &[(OUniZp, usize)]) -> Outcome {
    let mut comparisons = 0;
    for (bucket, degree) in buckets {
        let Some(parts) = manager.equal_degree(bucket, *degree) else {
            return Outcome::Declined("equal_degree refused");
        };
        let mut product = manager.one();
        for factor in &parts {
            comparisons += 1;
            if factor.degree() != Some(*degree) {
                return Divergence::outcome(
                    "up-zp-ddf",
                    "identity",
                    format!(
                        "equal_degree d={degree} returned degree {:?}",
                        factor.degree()
                    ),
                    vec![
                        ("bucket".to_string(), render_zp(manager, bucket)),
                        ("factor".to_string(), render_zp(manager, factor)),
                    ],
                );
            }
            product = manager.mul(&product, factor);
        }
        comparisons += 1;
        if product != *bucket {
            return Divergence::outcome(
                "up-zp-ddf",
                "identity",
                "equal-degree factors do not multiply back".to_string(),
                vec![
                    ("bucket".to_string(), render_zp(manager, bucket)),
                    ("product".to_string(), render_zp(manager, &product)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_ddf_counter(
    manager: &OZpMgr,
    radical: &OUniZp,
    buckets: &[(OUniZp, usize)],
    actual: u64,
) -> Outcome {
    let mut remaining = radical.degree().unwrap_or(0);
    let mut expected = 0;
    let mut degree = 1;
    while remaining >= 2 * degree {
        expected += 1;
        if let Some((factor, _)) = buckets.iter().find(|(_, label)| *label == degree) {
            remaining -= factor.degree().unwrap_or(0);
        }
        degree += 1;
    }
    if actual != expected {
        return Divergence::outcome(
            "up-zp-ddf",
            "identity",
            format!("ddf_iters says {actual}, buckets imply {expected}"),
            vec![
                ("input".to_string(), render_zp(manager, radical)),
                (
                    "buckets".to_string(),
                    buckets
                        .iter()
                        .map(|(factor, label)| {
                            format!("(deg {}, d={label})", factor.degree().unwrap_or(0))
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                ),
            ],
        );
    }
    Outcome::Match(1)
}
