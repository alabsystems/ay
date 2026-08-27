// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical interval-set sample selection checks.

use super::*;

// ===========================================================================
// Check 4 — `ialg-pick`
// ===========================================================================

/// The sample-point ladder.
///
/// z3 legs: every picked value must lie in the raw interval list as z3
/// computes it — a wrong sample point is a wrong decision, and the whole
/// verification-before-return discipline in `pick` exists to make this
/// impossible; and the MINIMALITY of the rung is checked by an independent
/// search that z3 adjudicates, never by reading AY's own tag.
/// Identity legs: `pick` on a non-empty set must succeed (a refusal here is a
/// divergence, see below); `pick` on the empty set must refuse;
/// `oialg_classify_value` is exercised directly on arbitrary values.
///
/// # A refusal is a divergence
///
/// `pick`'s ladder is a heuristic, but its TOTALITY on this corpus is not: the
/// dyadic rung succeeds for any interval with a non-empty interior, and the
/// algebraic rung covers the closed singleton, so the only non-empty set it can
/// refuse is one whose intervals are narrower than `2^-256`. No set built from
/// distinct roots of these small integer polynomials is. Reporting a refusal as
/// a decline would let a broken ladder — one whose bracket search silently
/// stopped finding anything — pass as silence, which is exactly how
/// `root_index` went from 111 matched to 21 matched with 0 divergences.
pub(crate) fn check_pick(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let Some(roots) = roots_of(z3, &g.p) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if roots.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pairs = pairs_from(&roots, g.strict, 100, EndpointExtent::Bounded);
    if pairs.is_empty() || !under_ceilings(&pairs) {
        return Outcome::Skipped("empty or over declared ceiling");
    }
    let Some(set) = build(&pairs) else {
        return Divergence::outcome(
            "ialg-pick",
            "z3",
            "from_parts declined under the declared ceilings".to_string(),
            inputs(g),
        );
    };
    if OIAlgSet::empty().pick().is_some() {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            "pick returned a value from the empty set".to_string(),
            inputs(g),
        );
    }
    if set.is_empty() {
        return Outcome::Skipped("set normalised to empty");
    }
    let Some(value) = set.pick() else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            format!("pick refused a non-empty set of {} intervals", set.len()),
            inputs(g),
        );
    };
    let value = sabotage_pick(value, sab);
    let Ok(value_ast) = z3_ast_of(z3, &value) else {
        return Outcome::Skipped("z3 could not name AY's pick");
    };
    let Some(in_set) = z3_member(z3, &pairs, value_ast) else {
        return Outcome::Skipped("z3 errored while testing membership");
    };
    if !in_set {
        return Divergence::outcome(
            "ialg-pick",
            "z3",
            format!(
                "pick returned {} outside the set",
                z3.ast_string(value_ast)
                    .unwrap_or_else(|| "<invalid-z3-ast>".into())
            ),
            inputs(g),
        );
    }
    let mut comparisons = 4;
    if sab.on() {
        return Outcome::Match(comparisons);
    }
    let rung = oialg_classify_value(&value);
    comparisons += 1;
    if let Err(outcome) = add_matches(&mut comparisons, check_pick_minimality(z3, g, &pairs, rung))
    {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_singleton_pick(z3, g, &roots[0])) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_value_classification(g, &roots[0].0))
    {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn sabotage_pick(value: ODyadicAnum, sab: Sabotage) -> ODyadicAnum {
    if !sab.on() {
        return value;
    }
    const SHIFT: i64 = 1_000;
    let base = value
        .to_rational()
        .unwrap_or_else(|| BigRational::from_integer(BigInt::zero()));
    ODyadicAnum::rational(base + BigRational::from_integer(BigInt::from(SHIFT)))
}

fn check_pick_minimality(z3: &Z3, g: &GenIA, pairs: &[Pair], rung: OIRung) -> Outcome {
    let mut comparisons = 0;
    if rung > OIRung::Integer {
        if let Some((lo, hi)) = integer_span(z3, pairs) {
            for integer in lo..=hi {
                let Some(candidate) =
                    z3.rational(&BigRational::from_integer(BigInt::from(integer)))
                else {
                    return Outcome::Skipped("z3 rejected a rational candidate");
                };
                let Some(in_set) = z3_member(z3, pairs, candidate) else {
                    return Outcome::Skipped("z3 errored while testing membership");
                };
                comparisons += 1;
                if in_set {
                    return Divergence::outcome(
                        "ialg-pick",
                        "z3",
                        format!("pick returned {rung:?}, but integer {integer} is in the set"),
                        inputs(g),
                    );
                }
            }
        }
    }
    match check_simple_minimality(z3, g, pairs, rung) {
        Outcome::Match(n) => Outcome::Match(comparisons + n),
        other => other,
    }
}

fn check_simple_minimality(z3: &Z3, g: &GenIA, pairs: &[Pair], rung: OIRung) -> Outcome {
    if rung <= OIRung::Simple {
        return Outcome::Match(0);
    }
    let Some((lo, hi)) = integer_span(z3, pairs) else {
        return Outcome::Match(0);
    };
    let mut comparisons = 0;
    'denominators: for denominator in 2..=oialg_max_simple_den() {
        for numerator in (lo * denominator)..=(hi * denominator) {
            if numerator.checked_mul(1).is_none() {
                break 'denominators;
            }
            let Some(candidate) = z3.rational(&BigRational::new(
                BigInt::from(numerator),
                BigInt::from(denominator),
            )) else {
                return Outcome::Skipped("z3 rejected a rational candidate");
            };
            let Some(in_set) = z3_member(z3, pairs, candidate) else {
                return Outcome::Skipped("z3 errored while testing membership");
            };
            comparisons += 1;
            if in_set {
                return Divergence::outcome(
                    "ialg-pick",
                    "z3",
                    format!("pick returned {rung:?}, but {numerator}/{denominator} is in the set"),
                    inputs(g),
                );
            }
        }
    }
    Outcome::Match(comparisons)
}

fn check_singleton_pick(z3: &Z3, g: &GenIA, root: &(ODyadicAnum, Ast)) -> Outcome {
    let singleton = OIAlgSet::from_parts(&[OIAlgInterval {
        lo: Some(root.0.clone()),
        lo_open: false,
        hi: Some(root.0.clone()),
        hi_open: false,
        lits: vec![11],
    }]);
    let Some(singleton) = singleton else {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            "a closed singleton at a root was refused".to_string(),
            inputs(g),
        );
    };
    if singleton.is_empty() || singleton.len() != 1 {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            format!("singleton normalized to {} intervals", singleton.len()),
            inputs(g),
        );
    }
    let Some(value) = singleton.pick() else {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            "pick refused a closed singleton".to_string(),
            inputs(g),
        );
    };
    let Ok(value_ast) = z3_ast_of(z3, &value) else {
        return Outcome::Skipped("z3 could not name the singleton pick");
    };
    let Some(equal) = z3.eq(value_ast, root.1) else {
        return Outcome::Skipped("z3 errored while comparing the singleton pick");
    };
    if !equal {
        return Divergence::outcome(
            "ialg-pick",
            "z3",
            format!(
                "singleton pick {} is not its root",
                z3.ast_string(value_ast)
                    .unwrap_or_else(|| "<invalid-z3-ast>".into())
            ),
            inputs(g),
        );
    }
    if oialg_classify_value(&value) != oialg_classify_value(&root.0) {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            format!(
                "singleton pick classified {:?}, root {:?}",
                oialg_classify_value(&value),
                oialg_classify_value(&root.0)
            ),
            inputs(g),
        );
    }
    Outcome::Match(5)
}

fn check_value_classification(g: &GenIA, root: &ODyadicAnum) -> Outcome {
    let integer = ODyadicAnum::rational(BigRational::from_integer(BigInt::from(-4)));
    if oialg_classify_value(&integer) != OIRung::Integer {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            "classify_value(-4) is not Integer".to_string(),
            inputs(g),
        );
    }
    let dyadic = ODyadicAnum::rational(BigRational::new(
        BigInt::one(),
        BigInt::from(oialg_max_simple_den() * 4),
    ));
    if oialg_classify_value(&dyadic) != OIRung::Dyadic {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            "a dyadic past the simple ceiling is not Dyadic".to_string(),
            inputs(g),
        );
    }
    if !root.is_rational() && oialg_classify_value(root) != OIRung::Algebraic {
        return Divergence::outcome(
            "ialg-pick",
            "identity",
            "an irrational root is not Algebraic".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(3)
}

/// The integer range worth scanning for the minimality legs, or `None` when the
/// set is too wide to scan — a bound, so this leg can never run away.
fn integer_span(z3: &Z3, pairs: &[Pair]) -> Option<(i64, i64)> {
    let mut lo = i64::MAX;
    let mut hi = i64::MIN;
    for p in pairs {
        let (l, h) = (p.lo?, p.hi?);
        let (a, _) = z3.bracket(l, 40)?;
        let (_, b) = z3.bracket(h, 40)?;
        lo = lo.min(rat_floor_i64(&a)? - 1);
        hi = hi.max(rat_ceil_i64(&b)? + 1);
    }
    if lo > hi || hi - lo > MINIMALITY_SPAN {
        return None;
    }
    Some((lo, hi))
}

fn rat_floor_i64(r: &BigRational) -> Option<i64> {
    i64::try_from(r.floor().to_integer()).ok()
}

fn rat_ceil_i64(r: &BigRational) -> Option<i64> {
    i64::try_from(r.ceil().to_integer()).ok()
}

/// z3's AST for an AY value: exact for a rational, and for an algebraic value
/// the unique root of AY's OWN defining polynomial inside AY's OWN interval.
fn z3_ast_of(z3: &Z3, a: &ODyadicAnum) -> Result<Ast, ()> {
    if let Some(r) = a.to_rational() {
        return z3.rational(&r).ok_or(());
    }
    let coeffs = rationals(&a.poly_coeffs().ok_or(())?);
    let roots = z3.roots(&coeffs).ok_or(())?;
    let iv = a.interval().ok_or(())?;
    let lo = z3.rational(&iv.lo().to_rational()).ok_or(())?;
    let hi = z3.rational(&iv.hi().to_rational()).ok_or(())?;
    let mut found = None;
    for r in roots {
        if z3.gt(r, lo).ok_or(())? && z3.lt(r, hi).ok_or(())? {
            if found.is_some() {
                return Err(());
            }
            found = Some(r);
        }
    }
    found.ok_or(())
}
