// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Representation-invariant checks for generated algebraic numbers.

use super::*;

// ===========================================================================
// Check 1 — `anum-representation`
// ===========================================================================

/// The representation and its invariant.
///
/// z3 legs: the constructed interval must contain z3's root and no other; the
/// DERIVED `root_index` must equal the root's position in z3's ascending list.
/// Identity legs: normalization is idempotent, primitive, positive-leading, and
/// square-free; refinement narrows without changing the number.
/// Guards, fired on purpose with positive controls on the same polynomial: a
/// two-root interval and a root endpoint must both be refused.
pub(crate) fn check_representation(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    let Some(roots) = z3.roots(&rationals(&g.p)) else {
        return Outcome::Skipped("z3 declined");
    };
    if roots.is_empty() {
        return Outcome::Skipped("no real roots");
    }
    let Some(norm) = anum_normalize_defining(&g.p) else {
        return Outcome::Declined("normalize_defining");
    };
    let mut comparisons = 0;

    if let Err(outcome) = add_matches(&mut comparisons, check_normalization(z3, g, &roots, &norm)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_roots(z3, g, sab, &roots)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_constructor_guards(z3, g, sab, &roots),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_normalization(z3: &Z3, g: &GenAn, roots: &[Ast], norm: &[BigInt]) -> Outcome {
    let mut n = 1;
    if anum_normalize_defining(norm).as_deref() != Some(norm) {
        return Divergence::outcome(
            "anum-representation",
            "identity",
            "normalize_defining is not idempotent".to_string(),
            inputs(g),
        );
    }
    n += 1;
    if !norm.last().is_some_and(BigInt::is_positive) {
        return Divergence::outcome(
            "anum-representation",
            "identity",
            format!(
                "normalized polynomial has non-positive lc: {}",
                render(norm)
            ),
            inputs(g),
        );
    }
    n += 1;
    let content = norm
        .iter()
        .fold(BigInt::zero(), |acc, c| num_integer::Integer::gcd(&acc, c));
    if content != BigInt::one() {
        return Divergence::outcome(
            "anum-representation",
            "identity",
            format!("normalized polynomial is not primitive: content {content}"),
            inputs(g),
        );
    }
    let Some(norm_roots) = z3.roots(&rationals(norm)) else {
        return Outcome::Skipped("z3 declined on radical");
    };
    n += 1;
    if norm_roots.len() != roots.len() {
        return Divergence::outcome(
            "anum-representation",
            "z3",
            format!(
                "radical has {} real roots, input has {}",
                norm_roots.len(),
                roots.len()
            ),
            inputs(g),
        );
    }
    Outcome::Match(n)
}

fn check_roots(z3: &Z3, g: &GenAn, sab: Sabotage, roots: &[Ast]) -> Outcome {
    let mut comparisons = 0;
    for (idx, root) in roots.iter().copied().enumerate() {
        let Some(iv) = dyadic_iv(z3, root) else {
            return Outcome::Declined("bracket");
        };
        let Some(a) = ODyadicAnum::from_poly_interval(&g.p, &iv) else {
            return Outcome::Declined("from_poly_interval");
        };
        if let Err(outcome) =
            add_matches(&mut comparisons, check_root_identity(z3, g, &a, root, idx))
        {
            return outcome;
        }
        if let Err(outcome) = add_matches(&mut comparisons, check_root_index(g, sab, &a, idx)) {
            return outcome;
        }
        if let Err(outcome) = add_matches(&mut comparisons, check_refinement(g, &a)) {
            return outcome;
        }
    }
    Outcome::Match(comparisons)
}

fn check_root_identity(z3: &Z3, g: &GenAn, a: &ODyadicAnum, root: Ast, idx: usize) -> Outcome {
    let Some(ast) = z3_of(z3, a) else {
        return Outcome::Declined("z3_of");
    };
    let Some(equal) = z3.eq(ast, root) else {
        return Outcome::Skipped("z3 errored while comparing roots");
    };
    if !equal {
        return Divergence::outcome(
            "anum-representation",
            "z3",
            format!("root #{idx}: AY's cell does not denote z3's root"),
            inputs(g),
        );
    }
    Outcome::Match(1)
}

fn check_root_index(g: &GenAn, sab: Sabotage, a: &ODyadicAnum, idx: usize) -> Outcome {
    if a.is_rational() {
        return Outcome::Match(0);
    }
    let Some(mut ay_index) = a.root_index() else {
        return Divergence::outcome(
            "anum-representation",
            "identity",
            format!(
                "root #{idx}: root_index() refused on a well-formed cell; it is derived and total"
            ),
            vec![("p".to_string(), render(&g.p))],
        );
    };
    if sab.on() {
        ay_index += 1;
    }
    if ay_index != idx + 1 {
        return Divergence::outcome(
            "anum-representation",
            "z3",
            format!(
                "root #{idx}: AY's derived root_index is {ay_index}, z3's position is {}",
                idx + 1
            ),
            inputs(g),
        );
    }
    Outcome::Match(2)
}

fn check_refinement(g: &GenAn, a: &ODyadicAnum) -> Outcome {
    if a.is_rational() {
        return Outcome::Match(0);
    }
    let target = OBq::inv_two_pow(BRACKET_BITS + 8);
    let Some(refined) = a.refine(&target) else {
        return Outcome::Declined("refine");
    };
    let mut n = 1;
    if refined.cmp_anum(a) != Some(Ordering::Equal) {
        return Divergence::outcome(
            "anum-representation",
            "identity",
            "refinement changed the number".to_string(),
            inputs(g),
        );
    }
    if let Some(iv) = refined.interval() {
        n += 1;
        if iv.width().cmp_bq(&target) == Ordering::Greater {
            return Divergence::outcome(
                "anum-representation",
                "identity",
                format!(
                    "refine did not reach the target width: {}/2^{} > 2^-{}",
                    iv.width().numerator(),
                    iv.width().k(),
                    BRACKET_BITS + 8
                ),
                inputs(g),
            );
        }
        n += 1;
        if ODyadicAnum::from_poly_interval(&refined.poly_coeffs().unwrap_or_default(), &iv)
            .is_none()
        {
            return Divergence::outcome(
                "anum-representation",
                "identity",
                "refined interval no longer isolates".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}

fn check_constructor_guards(z3: &Z3, g: &GenAn, sab: Sabotage, roots: &[Ast]) -> Outcome {
    let mut n = 0;
    if roots.len() >= 2 {
        let Some(first) = dyadic_iv(z3, roots[0]) else {
            return Outcome::Declined("bracket");
        };
        let Some(last) = dyadic_iv(z3, roots[roots.len() - 1]) else {
            return Outcome::Declined("bracket");
        };
        if let Some(span) = OBqInterval::new(&first.lo(), &last.hi()) {
            n += 1;
            let refused = ODyadicAnum::from_poly_interval(&g.p, &span).is_none();
            if if sab.on() { refused } else { !refused } {
                return Divergence::outcome(
                    "anum-representation",
                    "identity",
                    "constructor accepted an interval containing multiple roots".to_string(),
                    inputs(g),
                );
            }
        }
        n += 1;
        if ODyadicAnum::from_poly_interval(&g.p, &first).is_none() {
            return Divergence::outcome(
                "anum-representation",
                "identity",
                "constructor refused a genuinely isolating interval".to_string(),
                inputs(g),
            );
        }
    }
    match check_endpoint_guards(g) {
        Outcome::Match(m) => Outcome::Match(n + m),
        other => other,
    }
}

fn check_endpoint_guards(g: &GenAn) -> Outcome {
    let unit = ints(&[-1, 0, 1]);
    let one_iv = OBqInterval::new(
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(3)),
    );
    let mut n = 0;
    if let Some(iv) = one_iv {
        n += 1;
        if ODyadicAnum::from_poly_interval(&unit, &iv).is_some() {
            return Divergence::outcome(
                "anum-representation",
                "identity",
                "constructor accepted an interval whose endpoint is a root".to_string(),
                inputs(g),
            );
        }
    }
    if let Some(iv) = OBqInterval::new(&OBq::zero(), &OBq::from_int(BigInt::from(3))) {
        n += 1;
        if ODyadicAnum::from_poly_interval(&unit, &iv).is_none() {
            return Divergence::outcome(
                "anum-representation",
                "identity",
                "constructor refused (0, 3) for x^2 - 1".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}
