// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact algebraic-number comparison checks.

use super::*;

// ===========================================================================
// Check 2 — `anum-compare`
// ===========================================================================

/// Exact comparison against `Z3_algebraic_lt` / `_gt` / `_eq`.
///
/// The case this check exists for is **equality**: two numbers with different
/// defining polynomials that denote the same root. Refinement can never
/// separate them, so an implementation that refines until separated hangs. AY
/// must answer `Equal` by certificate with **zero** bisections, and this check
/// asserts exactly that, both the verdict and the step count.
pub(crate) fn check_compare(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    let Some((a, va, _)) = build_with(z3, &g.p, 0, BracketStyle::Widest) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let Some((b, vb, _)) = build_with(z3, &g.q, 1, BracketStyle::Widest) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let mut comparisons = 0;
    let outcome = check_algebraic_pair(z3, g, sab, &a, &b, va, vb);
    match outcome {
        Outcome::Match(n) => comparisons += n,
        other => return other,
    }
    let outcome = check_rational_pair(z3, g, sab, &a, va);
    match outcome {
        Outcome::Match(n) => comparisons += n,
        other => return other,
    }
    let outcome = check_refined_reflexivity(g, sab, &a);
    match outcome {
        Outcome::Match(n) => comparisons += n,
        other => return other,
    }
    Outcome::Match(comparisons)
}

fn check_algebraic_pair(
    z3: &Z3,
    g: &GenAn,
    sab: Sabotage,
    a: &ODyadicAnum,
    b: &ODyadicAnum,
    va: Ast,
    vb: Ast,
) -> Outcome {
    let traced = a.cmp_anum_traced(b);
    if traced.is_none() && !sab.on() {
        return Divergence::outcome(
            "anum-compare",
            "z3",
            format!(
                "cmp_anum declined below the {}-bit separation ceiling",
                anum_max_separation_bits()
            ),
            inputs(g),
        );
    }
    let Some((mut ord, trace)) = traced else {
        return Outcome::Declined("cmp_anum");
    };
    if sab.on() {
        ord = match ord {
            Ordering::Less => Ordering::Greater,
            Ordering::Equal => Ordering::Less,
            Ordering::Greater => Ordering::Equal,
        };
    }
    let Some(z3_ord) = z3_cmp(z3, va, vb) else {
        return Outcome::Skipped("z3 gave no order");
    };
    if ord != z3_ord {
        return Divergence::outcome(
            "anum-compare",
            "z3",
            format!("AY says {ord:?}, z3 says {z3_ord:?}"),
            inputs(g),
        );
    }
    if sab.on() {
        return Outcome::Match(2);
    }
    check_compare_trace(g, a, b, z3_ord, trace)
}

fn check_compare_trace(
    g: &GenAn,
    a: &ODyadicAnum,
    b: &ODyadicAnum,
    z3_ord: Ordering,
    trace: ay_nra::oracle_api::OAnumTrace,
) -> Outcome {
    if z3_ord == Ordering::Equal
        && !a.is_rational()
        && !b.is_rational()
        && !trace.equal_by_certificate
    {
        return Divergence::outcome(
            "anum-compare",
            "identity",
            "equal algebraic numbers were not decided by certificate".to_string(),
            inputs(g),
        );
    }
    if trace.equal_by_certificate && (trace.steps_a != 0 || trace.steps_b != 0) {
        return Divergence::outcome(
            "anum-compare",
            "identity",
            format!(
                "certificate path bisected: steps_a={} steps_b={}",
                trace.steps_a, trace.steps_b
            ),
            inputs(g),
        );
    }
    if trace.steps_a > trace.bound || trace.steps_b > trace.bound {
        return Divergence::outcome(
            "anum-compare",
            "identity",
            format!(
                "steps exceeded the derived bound: {}/{} > {}",
                trace.steps_a, trace.steps_b, trace.bound
            ),
            inputs(g),
        );
    }
    if trace
        .sep_bits
        .is_some_and(|bits| bits > anum_max_separation_bits())
    {
        return Divergence::outcome(
            "anum-compare",
            "identity",
            "separation exponent above the declared ceiling was acted on".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(6)
}

fn check_rational_pair(z3: &Z3, g: &GenAn, sab: Sabotage, a: &ODyadicAnum, va: Ast) -> Outcome {
    let Some(point) = z3.rational(&g.point) else {
        return Outcome::Skipped("z3 rejected rational comparison point");
    };
    let rational = ODyadicAnum::rational(g.point.clone());
    let Some(order) = a.cmp_anum(&rational) else {
        return Outcome::Declined("cmp_rational");
    };
    let Some(z3_order) = z3_cmp(z3, va, point) else {
        return Outcome::Skipped("z3 gave no rational order");
    };
    if !sab.on() && order != z3_order {
        return Divergence::outcome(
            "anum-compare",
            "z3",
            format!("vs rational {}: AY {order:?}, z3 {z3_order:?}", g.point),
            inputs(g),
        );
    }
    if !sab.on() && rational.cmp_anum(a) != Some(order.reverse()) {
        return Divergence::outcome(
            "anum-compare",
            "identity",
            "comparison is not antisymmetric".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(2)
}

fn check_refined_reflexivity(g: &GenAn, sab: Sabotage, a: &ODyadicAnum) -> Outcome {
    let Some(refined) = a.refine(&OBq::inv_two_pow(BRACKET_BITS + 16)) else {
        return Outcome::Match(0);
    };
    if !sab.on() && a.cmp_anum(&refined) != Some(Ordering::Equal) {
        return Divergence::outcome(
            "anum-compare",
            "identity",
            "a number does not compare equal to its own refinement".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(1)
}
