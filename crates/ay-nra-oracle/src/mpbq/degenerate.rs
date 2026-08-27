// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Degenerate-input guard and liveness checks.

use super::*;

// ===========================================================================
// Check 4 — `bq-degenerate`: the guards, and the liveness bound
// ===========================================================================

/// Every guard in the module, fired on purpose, each paired with a positive
/// control on a neighbouring well-formed input.
///
/// This check exists because of the campaign's second blind-spot pattern: **a
/// guard that never fires on the corpus, so deleting it is invisible**. Each
/// assertion below is written so that deleting the guard it targets makes this
/// check diverge.
///
/// It also carries the **liveness** assertion for the one loop whose bound is
/// not derivable from the input: `refine_until_separated` on two *identical*
/// roots can never separate them, and must return `Inconclusive` after exactly
/// the budget rather than spinning.
pub(crate) fn check_degenerate(g: &GenBq, sab: Sabotage) -> Outcome {
    let (interval, mut comparisons) = match check_interval_guards(g, sab) {
        Ok(value) => value,
        Err(outcome) => return outcome,
    };
    if let Err(outcome) = add_matches(&mut comparisons, check_representability_guards(g, sab)) {
        return outcome;
    }
    let polynomial = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let Some(unit) = OBqInterval::new(
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(2)),
    ) else {
        return Divergence::outcome(
            "bq-degenerate",
            "identity",
            "the constructor rejected the well-formed interval (1, 2)".into(),
            vec![],
        );
    };
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_refinement_target_guards(g, sab, &interval, &polynomial, &unit),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_broken_brackets(g, sab, &polynomial))
    {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_zero_polynomial_selection(g, sab, &interval),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_rational_enclosure(g, sab)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_separation_liveness(g, &polynomial, &unit),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_interval_guards(g: &GenBq, sab: Sabotage) -> Result<(OBqInterval, u64), Outcome> {
    let value = bq(&g.x);
    let equivalent = OBq::new(value.numerator() * 2, value.k() + 1);
    let below = value.sub(&OBq::from_int(BigInt::one()));
    ensure_declined(
        g,
        sab,
        OBqInterval::new(&value, &equivalent),
        "lo == hi written at different exponents",
    )?;
    ensure_declined(
        g,
        sab,
        OBqInterval::new(&value, &value),
        "lo == hi, identical",
    )?;
    ensure_declined(g, sab, OBqInterval::new(&value, &below), "lo > hi")?;
    let Some(interval) = OBqInterval::new(&below, &value) else {
        return Err(Divergence::outcome(
            "bq-degenerate",
            "identity",
            "the constructor rejected a well-formed interval".into(),
            vec![
                ("lo".into(), render_bq(&below)),
                ("hi".into(), render_bq(&value)),
            ],
        ));
    };
    Ok((interval, 4))
}

fn guard_answered<T>(sab: Sabotage, answer: Option<T>) -> bool {
    sab.on() || answer.is_some()
}

fn ensure_declined<T>(
    g: &GenBq,
    sab: Sabotage,
    answer: Option<T>,
    label: impl std::fmt::Display,
) -> Result<(), Outcome> {
    if guard_answered(sab, answer) {
        Err(guard_divergence(g, label))
    } else {
        Ok(())
    }
}

fn guard_divergence(g: &GenBq, label: impl std::fmt::Display) -> Outcome {
    Divergence::outcome(
        "bq-degenerate",
        "identity",
        format!("guard did not fire: {label}"),
        vec![("shape".into(), g.shape.to_string())],
    )
}

fn check_representability_guards(g: &GenBq, sab: Sabotage) -> Outcome {
    if sab.on() || OBq::is_representable(&g.non_dyadic) {
        return guard_divergence(g, format!("non-dyadic {} accepted", g.non_dyadic));
    }
    if !OBq::is_representable(&g.dyadic) {
        return Divergence::outcome(
            "bq-degenerate",
            "identity",
            format!("dyadic {} rejected", g.dyadic),
            vec![("r".into(), g.dyadic.to_string())],
        );
    }
    Outcome::Match(2)
}

fn check_refinement_target_guards(
    g: &GenBq,
    sab: Sabotage,
    interval: &OBqInterval,
    polynomial: &[BigInt],
    unit: &OBqInterval,
) -> Outcome {
    if guard_answered(sab, obq_refine_step_bound(&interval.width(), &OBq::zero())) {
        return guard_divergence(g, "refine_step_bound with target 0");
    }
    if guard_answered(
        sab,
        obq_refine_step_bound(&interval.width(), &OBq::inv_two_pow(3).neg()),
    ) {
        return guard_divergence(g, "refine_step_bound with a negative target");
    }
    if guard_answered(sab, obq_refine_to_width(&g.poly, interval, &OBq::zero())) {
        return guard_divergence(g, "refine_to_width with target 0");
    }
    if obq_refine_to_width(polynomial, unit, &OBq::inv_two_pow(20)).is_none() {
        return Divergence::outcome(
            "bq-degenerate",
            "identity",
            "refine_to_width declined on a sqrt(2) bracket".into(),
            vec![("target".into(), "2^-20".into())],
        );
    }
    Outcome::Match(4)
}

fn check_broken_brackets(g: &GenBq, sab: Sabotage, polynomial: &[BigInt]) -> Outcome {
    let Some(interval) = OBqInterval::new(
        &OBq::from_int(BigInt::from(2)),
        &OBq::from_int(BigInt::from(3)),
    ) else {
        return Divergence::outcome(
            "bq-degenerate",
            "identity",
            "the constructor rejected the well-formed interval (2, 3)".into(),
            vec![],
        );
    };
    let endpoint_root = [BigInt::from(-4), BigInt::zero(), BigInt::one()];
    if guard_answered(
        sab,
        obq_refine_to_width(polynomial, &interval, &OBq::inv_two_pow(8)),
    ) {
        return guard_divergence(g, "refine_to_width on an interval with no sign change");
    }
    if guard_answered(
        sab,
        obq_refine_to_width(&endpoint_root, &interval, &OBq::inv_two_pow(8)),
    ) {
        return guard_divergence(g, "refine_to_width with a root at an endpoint");
    }
    Outcome::Match(2)
}

fn check_zero_polynomial_selection(g: &GenBq, sab: Sabotage, interval: &OBqInterval) -> Outcome {
    if guard_answered(sab, obq_select_non_root(&[], interval)) {
        return guard_divergence(g, "select_non_root on the empty polynomial");
    }
    if guard_answered(
        sab,
        obq_select_non_root(&[BigInt::zero(), BigInt::zero()], interval),
    ) {
        return guard_divergence(g, "select_non_root on the zero polynomial");
    }
    Outcome::Match(2)
}

fn check_rational_enclosure(g: &GenBq, sab: Sabotage) -> Outcome {
    let lo = BigRational::new(BigInt::one(), BigInt::from(3));
    if guard_answered(sab, obq_enclose_rational(&lo, &lo, 8)) {
        return guard_divergence(g, "enclose_rational with lo == hi");
    }
    if guard_answered(
        sab,
        obq_enclose_rational(&(&lo + BigRational::one()), &lo, 8),
    ) {
        return guard_divergence(g, "enclose_rational with lo > hi");
    }
    let hi = &lo + BigRational::one();
    match obq_enclose_rational(&lo, &hi, 10) {
        Some(enclosure)
            if enclosure.lo().to_rational() <= lo && enclosure.hi().to_rational() >= hi =>
        {
            Outcome::Match(3)
        }
        Some(_) => Divergence::outcome(
            "bq-degenerate",
            "identity",
            "enclose_rational narrowed the interval".into(),
            vec![("lo".into(), lo.to_string()), ("hi".into(), hi.to_string())],
        ),
        None => Divergence::outcome(
            "bq-degenerate",
            "identity",
            "enclose_rational declined on a well-formed interval".into(),
            vec![("lo".into(), lo.to_string()), ("hi".into(), hi.to_string())],
        ),
    }
}

fn check_separation_liveness(g: &GenBq, polynomial: &[BigInt], unit: &OBqInterval) -> Outcome {
    let budget = 64;
    match obq_refine_until_separated(polynomial, unit, polynomial, unit, budget) {
        Some((OSeparation::Inconclusive, _, _, rounds)) if rounds == budget => {}
        Some((OSeparation::Inconclusive, _, _, rounds)) => {
            return Divergence::outcome(
                "bq-degenerate",
                "identity",
                format!("inconclusive after {rounds} rounds, budget was {budget}"),
                vec![],
            );
        }
        other => {
            return Divergence::outcome(
                "bq-degenerate",
                "identity",
                format!("the same root separated from itself: {other:?}"),
                vec![],
            );
        }
    }
    let mut comparisons = 2;
    let other = &g.poly2;
    let radicand = -other[0].clone();
    if radicand > BigInt::from(2) {
        let Some(wide) = OBqInterval::new(
            &OBq::from_int(BigInt::one()),
            &OBq::from_int(BigInt::from(4)),
        ) else {
            return Divergence::outcome(
                "bq-degenerate",
                "identity",
                "the constructor rejected the well-formed interval (1, 4)".into(),
                vec![],
            );
        };
        match obq_refine_until_separated(polynomial, &wide, other, &wide, 200) {
            Some((OSeparation::Ordered(Ordering::Less), a, b, _)) if a.disjoint(&b) => {
                comparisons += 2;
            }
            Some((OSeparation::Ordered(Ordering::Less), _, _, _)) => {
                return Divergence::outcome(
                    "bq-degenerate",
                    "identity",
                    "separated intervals are not disjoint".into(),
                    vec![],
                );
            }
            result => {
                return Divergence::outcome(
                    "bq-degenerate",
                    "identity",
                    format!("sqrt(2) vs sqrt({radicand}) did not separate: {result:?}"),
                    vec![],
                );
            }
        }
    }
    Outcome::Match(comparisons)
}
