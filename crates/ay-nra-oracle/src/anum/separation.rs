// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root-separation and Sturm-count checks.

use super::*;

// ===========================================================================
// Check 5 — `anum-separation`
// ===========================================================================

/// The DERIVED liveness bound, tested as a **pure function** and validated
/// **before** the consumer that reads it.
///
/// `anum_root_separation_exponent(p)` claims that any two distinct real roots of
/// `p` differ by more than `2^-B`. z3 knows the actual roots, so the claim is
/// directly falsifiable: bracket every consecutive pair and check the gap.
///
/// This is the fifth blind-spot pattern's fix in full. `refine_step_bound`
/// shipped an off-by-one in a branch that was structurally unreachable from its
/// caller's corpus, and two attempts to reach it by reshaping the caller's input
/// failed (measured 128 of 128). The fix there was to call the pure function
/// directly; the same is done here from the start, and the assertion is made
/// BEFORE `cmp_anum` runs on the same data — otherwise a bad bound turns into a
/// decline, and a decline is not a divergence.
pub(crate) fn check_separation(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    let Some(normalized) = anum_normalize_defining(&g.p) else {
        return Outcome::Declined("normalize_defining");
    };
    let Some(mut exponent) = anum_root_separation_exponent(&normalized) else {
        return Outcome::Declined("root_separation_exponent");
    };
    if sab.on() {
        exponent = 0;
    }
    let Some(roots) = z3.roots(&rationals(&normalized)) else {
        return Outcome::Skipped("z3 declined");
    };
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_root_gap_bound(z3, g, exponent, &roots),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_sturm_contract(g, sab, &normalized, roots.len()),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_separation_consumer(z3, g, sab, &normalized, roots.len()),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_root_gap_bound(z3: &Z3, g: &GenAn, exponent: u32, roots: &[Ast]) -> Outcome {
    let limit = BigRational::new(BigInt::one(), BigInt::one() << exponent.min(4096));
    let mut brackets = Vec::with_capacity(roots.len());
    for root in roots {
        let Some(bracket) = z3.bracket(*root, BRACKET_STEPS) else {
            return Outcome::Declined("bracket");
        };
        brackets.push(bracket);
    }
    let mut comparisons = 0;
    for pair in brackets.windows(2) {
        let gap = &pair[1].0 - &pair[0].1;
        if gap <= BigRational::zero() {
            continue;
        }
        comparisons += 1;
        if gap <= limit {
            return Divergence::outcome(
                "anum-separation",
                "z3",
                format!("claimed separation 2^-{exponent}, but z3 roots are only {gap} apart"),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_sturm_contract(
    g: &GenAn,
    sab: Sabotage,
    normalized: &[BigInt],
    root_count: usize,
) -> Outcome {
    let Some(bound) = anum_cauchy_bound(normalized) else {
        return Outcome::Declined("cauchy_bound");
    };
    let lo = OBq::from_int(-bound.clone());
    let hi = OBq::from_int(bound.clone());
    let Some(mut count) = anum_sturm_count_in(normalized, &lo, &hi) else {
        return Outcome::Declined("sturm_count_in");
    };
    if sab.on() {
        count += 1;
    }
    if count != root_count {
        return Divergence::outcome(
            "anum-separation",
            "z3",
            format!("Sturm counts {count} roots in (-{bound}, {bound}), z3 finds {root_count}"),
            inputs(g),
        );
    }
    let unit = ints(&[-1, 0, 1]);
    if anum_sturm_count_in(
        &unit,
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(3)),
    )
    .is_some()
    {
        return Divergence::outcome(
            "anum-separation",
            "identity",
            "sturm_count_in accepted a root endpoint".to_string(),
            inputs(g),
        );
    }
    if anum_sturm_count_in(&unit, &OBq::zero(), &OBq::from_int(BigInt::from(3))) != Some(1) {
        return Divergence::outcome(
            "anum-separation",
            "identity",
            "sturm_count_in miscounted (0, 3) for x^2 - 1".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(3)
}

fn check_separation_consumer(
    z3: &Z3,
    g: &GenAn,
    sab: Sabotage,
    normalized: &[BigInt],
    root_count: usize,
) -> Outcome {
    if sab.on() || root_count < 2 {
        return Outcome::Match(0);
    }
    let Some((a, va, _)) = build_with(z3, normalized, 0, BracketStyle::Widest) else {
        return Outcome::Declined("build");
    };
    let Some((b, vb, _)) = build_with(z3, normalized, 1, BracketStyle::Widest) else {
        return Outcome::Declined("build");
    };
    let Some(order) = a.cmp_anum(&b) else {
        return Divergence::outcome(
            "anum-separation",
            "z3",
            "cmp_anum declined after its separation bound was validated".to_string(),
            inputs(g),
        );
    };
    let Some(z3_order) = z3_cmp(z3, va, vb) else {
        return Outcome::Skipped("z3 gave no order after separation");
    };
    if order != z3_order {
        return Divergence::outcome(
            "anum-separation",
            "z3",
            format!("consumer disagrees after validated bound: AY {order:?}, z3 {z3_order:?}"),
            inputs(g),
        );
    }
    Outcome::Match(2)
}
