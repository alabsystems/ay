// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal dyadic-selection checks.

use super::*;

// ===========================================================================
// Check 3 — `bq-select`: minimality, with the negative half
// ===========================================================================

/// An INDEPENDENT minimal-exponent search, written over `BigRational`.
///
/// Shares no code and no representation with `mpbq`'s `BigInt`-shift
/// implementation: it scales by a rational `2^k`, rounds with `BigRational`'s
/// own `floor`/`ceil`, and compares as rationals. If both agree on the minimal
/// `k` for thousands of intervals, the shift arithmetic and the rounding are
/// pinned together.
fn witness_min_k(lo: &BigRational, hi: &BigRational, ceiling: u32) -> Option<(u32, BigInt)> {
    for k in 0..=ceiling {
        let scale = BigRational::from(BigInt::one() << k);
        let ls = lo * &scale;
        let hs = hi * &scale;
        let m0: BigInt = ls.floor().to_integer() + 1;
        let m1: BigInt = hs.ceil().to_integer() - 1;
        if m0 > m1 {
            continue;
        }
        let pick = if m0.is_positive() {
            m0
        } else if m1.is_negative() {
            m1
        } else {
            BigInt::zero()
        };
        return Some((k, pick));
    }
    None
}

/// A point strictly inside the interval whose exponent is **strictly greater**
/// than `v`'s — a valid but non-minimal answer, which is exactly the defect
/// `select_small` can have.
///
/// It exists at `j = width.k() + 2`: at that scale the interval spans at least
/// four grid units, so it contains at least three interior integers and hence
/// at least one **odd** one, and an odd numerator survives normalization with
/// its exponent intact. Since `select_small`'s own answer has
/// `k <= width.k() + 1`, that `j` is always strictly larger.
fn sabotage_point(iv: &OBqInterval, v: &OBq) -> Option<OBq> {
    let top = (iv.width().k() + 2).max(v.k() + 3);
    for j in (v.k() + 1)..=top {
        let m0: BigInt = iv.lo().floor_at(j) + 1;
        let m1: BigInt = iv.hi().ceil_at(j) - 1;
        if m0 > m1 {
            continue;
        }
        let cand = if m0.is_odd() {
            m0.clone()
        } else {
            m0.clone() + 1
        };
        if cand <= m1 {
            let out = OBq::new(cand, j);
            if out.k() > v.k() && iv.contains_open(&out) {
                return Some(out);
            }
        }
    }
    None
}

/// `select_small` / `select_int` / `select_non_root`.
///
/// z3's dyadic layer is not reachable (see the module header), so the reference
/// is an exact identity plus two independent witnesses:
///
///   * **containment**, checked in `BigRational`;
///   * **minimality, both halves**. The positive half is that the answer sits
///     at exponent `k`. The negative half — the one that stops the check from
///     being satisfiable by "always return the midpoint" — is that
///     `candidate_at(iv, j)` is `None` for **every** `j < k`. The `straddle`
///     shape exists so that a simpler point genuinely does exist most of the
///     time; on the `adjacent` shape the midpoint IS the minimal answer and the
///     certificate is trivially satisfied, which is why the shape counts are
///     reported.
///   * an **independent minimal-`k` search over `BigRational`**
///     ([`witness_min_k`]), which must return the same `k` and the same value.
/// The interval `(-hi, -lo)` — the mirror image of `iv` through zero.
fn mirror_interval(iv: &OBqInterval) -> Option<OBqInterval> {
    OBqInterval::new(&iv.hi().neg(), &iv.lo().neg())
}

/// `p(-x)`: negate every odd-degree coefficient.
fn mirror_poly(p: &[BigInt]) -> Vec<BigInt> {
    p.iter()
        .enumerate()
        .map(|(i, c)| if i % 2 == 1 { -c.clone() } else { c.clone() })
        .collect()
}

pub(crate) fn check_select(g: &GenBq, sab: Sabotage) -> Outcome {
    let lo = bq(&g.iv.0);
    let hi = bq(&g.iv.1);
    let Some(interval) = OBqInterval::new(&lo, &hi) else {
        return Outcome::Skipped("interval is empty or inverted");
    };
    let Some((selected, ceiling)) = obq_select_small(&interval) else {
        return Outcome::Declined("select_small declined");
    };
    let selected = if sab.on() {
        sabotage_point(&interval, &selected).unwrap_or(selected)
    } else {
        selected
    };
    let case = SelectCase {
        g,
        lo: &lo,
        hi: &hi,
        interval: &interval,
        selected: &selected,
        ceiling,
    };
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(&mut comparisons, check_selected_containment(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_select_ceiling(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_select_minimality(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_select_int_agreement(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_adversarial_non_root(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_generated_non_root(&case)) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct SelectCase<'a> {
    g: &'a GenBq,
    lo: &'a OBq,
    hi: &'a OBq,
    interval: &'a OBqInterval,
    selected: &'a OBq,
    ceiling: u32,
}

fn select_inputs(case: &SelectCase<'_>) -> Vec<(String, String)> {
    vec![
        ("lo".into(), render_bq(case.lo)),
        ("hi".into(), render_bq(case.hi)),
    ]
}

fn check_selected_containment(case: &SelectCase<'_>) -> Outcome {
    let lo = case.lo.to_rational();
    let hi = case.hi.to_rational();
    let selected = case.selected.to_rational();
    if !(lo < selected && selected < hi) {
        return Divergence::outcome(
            "bq-select",
            "identity",
            format!(
                "selected {} is not strictly inside ({lo}, {hi})",
                render_bq(case.selected)
            ),
            select_inputs(case),
        );
    }
    if !case.interval.contains_open(case.selected) {
        return Divergence::outcome(
            "bq-select",
            "identity",
            "contains_open disagrees with the BigRational comparison".into(),
            select_inputs(case),
        );
    }
    Outcome::Match(2)
}

fn check_select_ceiling(case: &SelectCase<'_>) -> Outcome {
    if case.ceiling != case.interval.width().k() + 1 {
        return Divergence::outcome(
            "bq-select",
            "identity",
            format!(
                "ceiling {} != width.k()+1 = {}",
                case.ceiling,
                case.interval.width().k() + 1
            ),
            vec![("width".into(), render_bq(&case.interval.width()))],
        );
    }
    if case.selected.k() > case.ceiling {
        return Divergence::outcome(
            "bq-select",
            "identity",
            format!(
                "answer exponent {} exceeds ceiling {}",
                case.selected.k(),
                case.ceiling
            ),
            select_inputs(case),
        );
    }
    Outcome::Match(2)
}

fn check_select_minimality(case: &SelectCase<'_>) -> Outcome {
    let mut comparisons = 0;
    for exponent in 0..case.selected.k() {
        if let Some(numerator) = obq_candidate_at(case.interval, exponent) {
            return Divergence::outcome(
                "bq-select",
                "identity",
                format!(
                    "not minimal: answered k={} but {numerator}/2^{exponent} is inside",
                    case.selected.k()
                ),
                select_inputs(case),
            );
        }
        comparisons += 1;
    }
    let lo = case.lo.to_rational();
    let hi = case.hi.to_rational();
    match witness_min_k(&lo, &hi, case.ceiling) {
        Some((exponent, numerator)) => {
            let witness = format!("{numerator}/2^{exponent}");
            if exponent == case.selected.k() && OBq::new(numerator, exponent) == *case.selected {
                Outcome::Match(comparisons + 2)
            } else {
                Divergence::outcome(
                    "bq-select",
                    "identity",
                    format!(
                        "witness picked {witness}, AY picked {}",
                        render_bq(case.selected)
                    ),
                    select_inputs(case),
                )
            }
        }
        None => Divergence::outcome(
            "bq-select",
            "identity",
            format!(
                "independent witness found no dyadic below ceiling {}, AY picked {}",
                case.ceiling,
                render_bq(case.selected)
            ),
            select_inputs(case),
        ),
    }
}

fn check_select_int_agreement(case: &SelectCase<'_>) -> Outcome {
    if obq_select_int(case.lo, case.hi) != obq_candidate_at(case.interval, 0) {
        return Divergence::outcome(
            "bq-select",
            "identity",
            "select_int disagrees with candidate_at(iv, 0)".into(),
            select_inputs(case),
        );
    }
    Outcome::Match(1)
}

fn build_exhaustion_poly(interval: &OBqInterval) -> Option<Vec<BigInt>> {
    let lo = interval.lo().floor_at(0) + BigInt::from(1);
    let hi = interval.hi().ceil_at(0) - BigInt::from(1);
    if lo > hi {
        return None;
    }
    let levels = (interval.width().k() + 5).min(10);
    let mut polynomial = vec![BigInt::from(1)];
    let mut planted = 0;
    for exponent in 0..=levels {
        let first = interval.lo().floor_at(exponent) + BigInt::from(1);
        let last = interval.hi().ceil_at(exponent) - BigInt::from(1);
        if first > last {
            continue;
        }
        let numerator = if last <= BigInt::zero() {
            last
        } else if first >= BigInt::zero() {
            first
        } else {
            BigInt::zero()
        };
        let factor = [-numerator, BigInt::one() << exponent];
        let mut product = vec![BigInt::zero(); polynomial.len() + 1];
        for (degree, coefficient) in polynomial.iter().enumerate() {
            product[degree] += coefficient * &factor[0];
            product[degree + 1] += coefficient * &factor[1];
        }
        polynomial = product;
        planted += 1;
    }
    (planted > 0).then_some(polynomial)
}

fn check_adversarial_non_root(case: &SelectCase<'_>) -> Outcome {
    let Some(polynomial) = build_exhaustion_poly(case.interval) else {
        return Outcome::Match(0);
    };
    let Some(mirror) = mirror_interval(case.interval) else {
        return Divergence::outcome(
            "bq-select",
            "identity",
            "negating an interval did not preserve its strict order".into(),
            select_inputs(case),
        );
    };
    let intervals = [
        ("iv", case.interval.clone(), polynomial.clone()),
        ("mirror", mirror, mirror_poly(&polynomial)),
    ];
    for (label, interval, poly) in intervals {
        match obq_select_non_root(&poly, &interval) {
            Some(value)
                if interval.contains_open(&value) && obq_poly_sign_at(&poly, &value) != Some(0) => {
            }
            Some(value) => {
                return Divergence::outcome(
                    "bq-select",
                    "identity",
                    format!(
                        "select_non_root ({label}) returned {} outside, or a root",
                        render_bq(&value)
                    ),
                    vec![("poly".into(), render_poly(&poly))],
                );
            }
            None => {
                return Divergence::outcome(
                    "bq-select",
                    "identity",
                    format!("select_non_root declined on the {label} interval"),
                    vec![("poly".into(), render_poly(&poly))],
                );
            }
        }
    }
    Outcome::Match(2)
}

fn check_generated_non_root(case: &SelectCase<'_>) -> Outcome {
    let Some(value) = obq_select_non_root(&case.g.poly, case.interval) else {
        return Outcome::Match(0);
    };
    if !case.interval.contains_open(&value) {
        return Divergence::outcome(
            "bq-select",
            "identity",
            format!(
                "select_non_root returned {} outside the interval",
                render_bq(&value)
            ),
            vec![("poly".into(), render_poly(&case.g.poly))],
        );
    }
    match obq_poly_sign_at(&case.g.poly, &value) {
        Some(0) | None => {
            return Divergence::outcome(
                "bq-select",
                "identity",
                format!("select_non_root returned root {}", render_bq(&value)),
                vec![("poly".into(), render_poly(&case.g.poly))],
            );
        }
        Some(_) => {}
    }
    match (
        obq_poly_eval_at(&case.g.poly, &value),
        obq_poly_sign_at(&case.g.poly, &value),
    ) {
        (Some(value), Some(sign)) if value.sign() == sign => Outcome::Match(3),
        (value, sign) => Divergence::outcome(
            "bq-select",
            "identity",
            format!("poly_eval_at {value:?} and poly_sign_at {sign:?} disagree"),
            vec![("poly".into(), render_poly(&case.g.poly))],
        ),
    }
}
