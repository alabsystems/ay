// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dense univariate arithmetic-substrate checks.

use super::*;

// ---------------------------------------------------------------------------
// Check 1: the Z / Z_p arithmetic substrate
// ---------------------------------------------------------------------------

/// The `Z` substrate identities, plus the `Z -> Z_p` reduction as a RING
/// HOMOMORPHISM, plus a z3-backed leg on pseudo-division.
///
/// Four statements:
///
///   (a) `content(f) * pp(f) == f` exactly, `pp` primitive with positive `lc`.
///   (b) `lc(b)^d * a == q*b + r` with `deg r < deg b` — the pseudo-division
///       identity, exactly.
///   (c) reduction mod `p` commutes with `+` and `*`. This is what makes every
///       modular algorithm legal, and it is the statement that a sloppy
///       `reduce` (say, `%` instead of `mod_floor`, which differs on negative
///       coefficients) violates.
///   (d) **z3-backed**: at a real root `alpha` of `b`, the pseudo-division
///       identity collapses to `lc(b)^d * a(alpha) == r(alpha)`, so the two
///       signs z3 computes must agree. `alpha` and both signs come from z3;
///       AY supplies only `q`, `r` and `d`.
pub(crate) fn check_substrate(z3: &Z3, g: &GenUp, sab: Sabotage) -> Outcome {
    let a = build_z(g);
    let b = OUniZ::from_coeffs(g.other.clone());
    if a.is_zero() || b.is_zero() {
        return Outcome::Skipped("degenerate operand");
    }
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(&mut comparisons, check_content_and_gcd(&a, &b)) {
        return outcome;
    }
    let Some((exponent, quotient, mut remainder)) = a.pseudo_div(&b) else {
        return Outcome::Declined("pseudo_div refused");
    };
    let Ok(exponent) = u32::try_from(exponent) else {
        return Outcome::Declined("pseudo_div exponent exceeds the oracle range");
    };
    if sab.on() {
        let mut coefficients = remainder.coeffs();
        if coefficients.is_empty() {
            coefficients.push(BigInt::one());
        } else {
            coefficients[0] += BigInt::one();
        }
        remainder = OUniZ::from_coeffs(coefficients);
    }
    let leading = b.lc().unwrap_or_else(BigInt::one);
    let pseudo = PseudoCase {
        exponent,
        quotient: &quotient,
        remainder: &remainder,
        leading: &leading,
    };
    if let Err(outcome) = add_matches(&mut comparisons, check_pseudo_division(&a, &b, &pseudo)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_reduction_homomorphism(g, &a, &b)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_z3_specialization(z3, &a, &b, &pseudo),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct PseudoCase<'a> {
    exponent: u32,
    quotient: &'a OUniZ,
    remainder: &'a OUniZ,
    leading: &'a BigInt,
}

fn check_content_and_gcd(a: &OUniZ, b: &OUniZ) -> Outcome {
    let Some((content, primitive)) = a.split_content() else {
        return Outcome::Declined("split_content refused");
    };
    if primitive.scale(&content) != *a {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            "content * primitive_part != input".to_string(),
            vec![
                ("a".to_string(), render_z(a)),
                ("content".to_string(), content.to_string()),
                ("pp".to_string(), render_z(&primitive)),
            ],
        );
    }
    if !primitive.content().is_one() || primitive.lc().is_some_and(|value| value.is_negative()) {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            format!("primitive part has content {}", primitive.content()),
            vec![
                ("a".to_string(), render_z(a)),
                ("pp".to_string(), render_z(&primitive)),
            ],
        );
    }
    let scale = BigInt::from(6);
    let (Some(gcd), Some(scaled_gcd)) = (a.gcd(b), a.scale(&scale).gcd(&b.scale(&scale))) else {
        return Outcome::Declined("gcd refused");
    };
    if scaled_gcd != gcd.scale(&scale) {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            "gcd(k*a, k*b) != k*gcd(a,b)".to_string(),
            vec![
                ("a".to_string(), render_z(a)),
                ("b".to_string(), render_z(b)),
                ("k".to_string(), scale.to_string()),
                ("gcd(a,b)".to_string(), render_z(&gcd)),
                ("gcd(ka,kb)".to_string(), render_z(&scaled_gcd)),
            ],
        );
    }
    Outcome::Match(3)
}

fn check_pseudo_division(a: &OUniZ, b: &OUniZ, pseudo: &PseudoCase<'_>) -> Outcome {
    let mut lhs = a.clone();
    for _ in 0..pseudo.exponent {
        lhs = lhs.scale(pseudo.leading);
    }
    if lhs != pseudo.quotient.mul(b).add(pseudo.remainder) {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            format!(
                "pseudo-division identity fails: lc(b)^{} * a != q*b + r",
                pseudo.exponent
            ),
            pseudo_inputs(a, b, pseudo),
        );
    }
    if let (Some(remainder_degree), Some(divisor_degree)) = (pseudo.remainder.degree(), b.degree())
    {
        if remainder_degree >= divisor_degree {
            return Divergence::outcome(
                "up-z-substrate",
                "identity",
                format!(
                    "pseudo-remainder degree {remainder_degree} >= divisor degree {divisor_degree}"
                ),
                pseudo_inputs(a, b, pseudo),
            );
        }
    }
    let mut comparisons = 2;
    for point in [-3i64, -1, 0, 2, 7].map(BigInt::from) {
        let mut lhs = a.eval(&point);
        for _ in 0..pseudo.exponent {
            lhs *= pseudo.leading;
        }
        comparisons += 1;
        if lhs != pseudo.quotient.eval(&point) * b.eval(&point) + pseudo.remainder.eval(&point) {
            return Divergence::outcome(
                "up-z-substrate",
                "identity",
                format!("pseudo-division identity fails at x = {point}"),
                pseudo_inputs(a, b, pseudo),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn pseudo_inputs(a: &OUniZ, b: &OUniZ, pseudo: &PseudoCase<'_>) -> Vec<(String, String)> {
    vec![
        ("a".to_string(), render_z(a)),
        ("b".to_string(), render_z(b)),
        ("d".to_string(), pseudo.exponent.to_string()),
        ("q".to_string(), render_z(pseudo.quotient)),
        ("r".to_string(), render_z(pseudo.remainder)),
    ]
}

fn check_reduction_homomorphism(g: &GenUp, a: &OUniZ, b: &OUniZ) -> Outcome {
    let Some(manager) = OZpMgr::new(g.p) else {
        return Outcome::Declined("modulus refused");
    };
    let (reduced_a, reduced_b) = (manager.reduce(a), manager.reduce(b));
    let lifted = manager.lift(&reduced_a);
    if manager.reduce(&lifted) != reduced_a {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            format!("reduce(lift(x)) != x mod {}", g.p),
            vec![("a".to_string(), render_z(a))],
        );
    }
    if lifted
        .coeffs()
        .iter()
        .any(|coefficient| coefficient.is_negative() || *coefficient >= BigInt::from(g.p))
    {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            format!("lift produced a coefficient outside [0, {})", g.p),
            vec![("lifted".to_string(), render_z(&lifted))],
        );
    }
    if manager.reduce(&a.add(b)) != manager.add(&reduced_a, &reduced_b) {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            format!("reduce is not additive mod {}", g.p),
            vec![
                ("a".to_string(), render_z(a)),
                ("b".to_string(), render_z(b)),
            ],
        );
    }
    if manager.reduce(&a.mul(b)) != manager.mul(&reduced_a, &reduced_b) {
        return Divergence::outcome(
            "up-z-substrate",
            "identity",
            format!("reduce is not multiplicative mod {}", g.p),
            vec![
                ("a".to_string(), render_z(a)),
                ("b".to_string(), render_z(b)),
            ],
        );
    }
    Outcome::Match(4)
}

fn check_z3_specialization(z3: &Z3, a: &OUniZ, b: &OUniZ, pseudo: &PseudoCase<'_>) -> Outcome {
    let Some(roots) = z3.roots(&to_rationals(b)) else {
        return Outcome::Skipped("z3 declined the divisor");
    };
    if roots.is_empty() {
        return Outcome::Match(0);
    }
    let mut scaled = to_rationals(a);
    let leading = BigRational::from(pseudo.leading.clone());
    for _ in 0..pseudo.exponent {
        for coefficient in &mut scaled {
            *coefficient *= &leading;
        }
    }
    let remainder = to_rationals(pseudo.remainder);
    let mut comparisons = 0;
    for (index, root) in roots.iter().copied().enumerate() {
        let (Some(lhs), Some(rhs)) = (z3.eval_sign(&scaled, root), z3.eval_sign(&remainder, root))
        else {
            return Outcome::Skipped("z3 declined an evaluation");
        };
        comparisons += 1;
        if lhs != rhs {
            return Divergence::outcome(
                "up-z-substrate",
                "z3",
                format!(
                    "at root #{index}: sign(lc^{})*a={lhs}, sign(r)={rhs}",
                    pseudo.exponent
                ),
                pseudo_inputs(a, b, pseudo),
            );
        }
    }
    Outcome::Match(comparisons)
}
