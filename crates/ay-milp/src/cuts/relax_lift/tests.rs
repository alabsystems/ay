// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Relax-and-lift exactness and soundness regressions.

use super::*;
use crate::model::Sense;

/// `Φ` is claimed EXACT, not merely an upper bound — the whole lifting window is computed from
/// it, so an UNDER-estimate makes `γ` too large and deletes feasible points (hazard H13). This
/// is the positive control on the instrument: brute-force the same maximum by enumerating
/// every 0/1 assignment of the cover and every multiplicity vector of the lifted set, and
/// require the two to agree exactly.
#[test]
fn rl_phi_matches_full_enumeration() {
    let mut seed = 0x9E37_79B9_7F4A_7C15_u64;
    let mut rnd = || {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        (seed >> 33) as i64
    };
    let q = |n: i64, d: i64| BigRational::new(n.into(), d.into());
    let mut checked = 0usize;
    for _ in 0..300 {
        let nc = 2 + (rnd() % 5) as usize; // cover size
        let ng = (rnd() % 3) as usize; // lifted integers
        let cw: Vec<BigRational> = (0..nc).map(|_| q(1 + rnd() % 9, 1 + rnd() % 3)).collect();
        let mut sw = cw.clone();
        sw.sort();
        let mut prefix = vec![BigRational::zero()];
        for w in &sw {
            let last = prefix.last().unwrap().clone();
            prefix.push(last + w);
        }
        let lifted: Vec<RlLifted> = (0..ng)
            .map(|i| {
                let u = 1 + rnd() % 3;
                (
                    i,
                    q(1 + rnd() % 5, 1 + rnd() % 2),
                    u,
                    rnd() % (u + 1),
                    q(rnd() % 7 - 3, 1 + rnd() % 2),
                )
            })
            .collect();
        let budget = q(rnd() % 30 - 5, 1 + rnd() % 2);

        // Brute force: every subset of the cover x every multiplicity vector.
        let mut truth: Option<BigRational> = None;
        let space: i64 = lifted.iter().map(|l| l.2 + 1).product::<i64>().max(1);
        for mask in 0..(1u32 << nc) {
            for code in 0..space {
                let mut used = BigRational::zero();
                let mut val = BigRational::zero();
                let mut rest = code;
                for l in &lifted {
                    let t = rest % (l.2 + 1);
                    rest /= l.2 + 1;
                    used += &l.1 * BigRational::from_integer(t.into());
                    val += &l.4 * BigRational::from_integer((t - l.3).into());
                }
                for (b, w) in cw.iter().enumerate() {
                    if mask >> b & 1 == 1 {
                        used += w;
                        val += BigRational::from_integer(1.into());
                    }
                }
                if used <= budget && truth.as_ref().is_none_or(|t| val > *t) {
                    truth = Some(val);
                }
            }
        }
        let got = rl_phi(&prefix, &lifted, &budget);
        assert_eq!(
            got, truth,
            "phi disagreed with brute force: cw={cw:?} lifted={lifted:?} budget={budget}"
        );
        if truth.is_some() {
            checked += 1;
        }
    }
    assert!(checked > 100, "the phi control barely exercised anything");
}

/// THE VALIDITY GUARD. Single-row mixed models — both orientations, both coefficient signs,
/// binaries, small general integers, continuous columns, and DELIBERATELY FRACTIONAL bounds
/// (`lo = 1/2`, `up = 5/2`), which is the shape that shipped the MIR wrong answer.
///
/// The feasibility oracle is exact BECAUSE the model has one row: with the integral columns
/// pinned, the row's activity sweeps a closed INTERVAL as the continuous columns range over
/// their boxes, so a feasible completion exists iff that interval meets `[lb, ub]`. Any point
/// that is feasible must satisfy every emitted cut.
struct RelaxLiftCase {
    model: Model,
    spec: Vec<(Col, u8, f64, f64)>,
    coefficients: Vec<f64>,
    lower: f64,
    upper: f64,
    point: Vec<f64>,
}

fn add_relax_lift_column(
    model: &mut Model,
    random: &mut impl FnMut() -> i64,
) -> (Col, u8, f64, f64) {
    let kind = match random() % 8 {
        0..=4 => 0u8,
        5 | 6 => 1u8,
        _ => 2u8,
    };
    match kind {
        0 => (model.add_binary_col(), 0, 0.0, 1.0),
        1 => {
            let fractional = random() % 3 == 0;
            let lower = if fractional {
                0.5
            } else {
                (random() % 2) as f64
            };
            let upper = lower + (1 + random() % 3) as f64;
            (model.add_int_col(lower, upper), 1, lower, upper)
        }
        _ => {
            let lower = if random() % 2 == 0 { 0.0 } else { 0.5 };
            let upper = lower + (1 + random() % 4) as f64;
            (model.add_col(lower, upper), 2, lower, upper)
        }
    }
}

fn build_relax_lift_case(random: &mut impl FnMut() -> i64) -> RelaxLiftCase {
    let n = 4 + (random() % 4) as usize;
    let mut model = Model::new();
    let spec: Vec<_> = (0..n)
        .map(|_| add_relax_lift_column(&mut model, random))
        .collect();
    let coefficients: Vec<f64> = (0..n)
        .map(|_| {
            let value = (1 + random() % 6) as f64 / (1 + random() % 2) as f64;
            if random() % 3 == 0 {
                -value
            } else {
                value
            }
        })
        .collect();
    let terms: Vec<_> = spec
        .iter()
        .map(|item| item.0)
        .zip(coefficients.iter().copied())
        .collect();
    let (mut activity_min, mut activity_max) = (0.0, 0.0);
    for (index, item) in spec.iter().enumerate() {
        activity_min += (coefficients[index] * item.2).min(coefficients[index] * item.3);
        activity_max += (coefficients[index] * item.2).max(coefficients[index] * item.3);
    }
    let fraction = (random() % 7) as f64 / 8.0 + 0.1;
    let two_sided = random() % 4 == 0;
    let (lower, upper) = if random() % 2 == 0 {
        let bound = activity_min + (activity_max - activity_min) * fraction;
        if two_sided {
            (activity_min - 1.0, bound)
        } else {
            (f64::NEG_INFINITY, bound)
        }
    } else {
        let bound = activity_max - (activity_max - activity_min) * fraction;
        if two_sided {
            (bound, activity_max + 1.0)
        } else {
            (bound, f64::INFINITY)
        }
    };
    model.add_row(lower, upper, &terms);
    model.set_objective(&terms, Sense::Minimize);
    let point = spec
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let fraction = if random() % 4 == 0 {
                (random() % 9) as f64 / 8.0
            } else {
                0.55 + (random() % 5) as f64 / 12.0
            };
            if coefficients[index] > 0.0 {
                item.2 + (item.3 - item.2) * fraction
            } else {
                item.3 - (item.3 - item.2) * fraction
            }
        })
        .collect();
    RelaxLiftCase {
        model,
        spec,
        coefficients,
        lower,
        upper,
        point,
    }
}

fn assert_relax_lift_case(case: usize, fixture: &RelaxLiftCase, cuts: &[Cut]) {
    let n = fixture.spec.len();
    let ints: Vec<usize> = (0..n).filter(|&i| fixture.spec[i].1 != 2).collect();
    let ranges: Vec<Vec<f64>> = ints
        .iter()
        .map(|&i| {
            let (lo, up) = (fixture.spec[i].2, fixture.spec[i].3);
            let mut values = Vec::new();
            let mut value = lo.ceil();
            while value <= up + 1e-12 {
                values.push(value);
                value += 1.0;
            }
            values
        })
        .collect();
    let total: usize = ranges.iter().map(|range| range.len().max(1)).product();
    assert!(total < 100_000);
    for code in 0..total {
        let mut rest = code;
        let mut point = vec![0.0; n];
        for (k, &i) in ints.iter().enumerate() {
            let range = &ranges[k];
            if !range.is_empty() {
                point[i] = range[rest % range.len()];
                rest /= range.len();
            }
        }
        let fixed: f64 = ints
            .iter()
            .map(|&i| fixture.coefficients[i] * point[i])
            .sum();
        let (mut cmin, mut cmax) = (fixed, fixed);
        for (i, item) in fixture
            .spec
            .iter()
            .enumerate()
            .filter(|(_, item)| item.1 == 2)
        {
            cmin += (fixture.coefficients[i] * item.2).min(fixture.coefficients[i] * item.3);
            cmax += (fixture.coefficients[i] * item.2).max(fixture.coefficients[i] * item.3);
        }
        if cmax < fixture.lower - 1e-9 || cmin > fixture.upper + 1e-9 {
            continue;
        }
        for (i, item) in fixture
            .spec
            .iter()
            .enumerate()
            .filter(|(_, item)| item.1 == 2)
        {
            point[i] = if fixture.coefficients[i] >= 0.0 {
                item.2
            } else {
                item.3
            };
        }
        for cut in cuts {
            let activity: f64 = cut
                .coeffs
                .iter()
                .map(|&(column, weight)| weight * point[column.index()])
                .sum();
            assert!(
                activity <= cut.ub + 1e-6,
                "relax-and-lift deleted a feasible integer point (case {case}): \
                 point={point:?} activity={activity} > ub={} spec={:?} a={:?} \
                 row=[{},{}] cut={:?}",
                cut.ub,
                fixture.spec,
                fixture.coefficients,
                fixture.lower,
                fixture.upper,
                cut.coeffs
            );
        }
    }
}

#[test]
fn relax_lift_cuts_never_remove_an_integer_point() {
    let mut seed = 0x51DE_2026_A5_u64;
    let mut rnd = || {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        (seed >> 33) as i64
    };
    let mut fired = 0usize;
    for case in 0..4000usize {
        let fixture = build_relax_lift_case(&mut rnd);
        let cuts = separate_relax_lift(&fixture.model, &fixture.point, 1, 8);
        if cuts.is_empty() {
            continue;
        }
        fired += cuts.len();
        assert_relax_lift_case(case, &fixture, &cuts);
    }
    assert!(
        fired > 0,
        "no relax-and-lift cut was ever separated: the guard is vacuous"
    );
}

/// The family must be INERT on a model it has no structure in — a pure set-packing row with no
/// general integer and no cover — and must not panic on degenerate input.
#[test]
fn relax_lift_declines_structureless_rows() {
    let mut m = Model::new();
    let a = m.add_binary_col();
    let b = m.add_binary_col();
    let c = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0), (c, 1.0)]);
    // x* = (1/3, 1/3, 1/3) satisfies the row; the cover {a,b} gives `a + b <= 1`, which the
    // point does not violate, so nothing may be emitted.
    let cuts = separate_relax_lift(&m, &[1.0 / 3.0, 1.0 / 3.0, 1.0 / 3.0], 1, 8);
    assert!(
        cuts.is_empty(),
        "emitted a non-violated cut: {:?}",
        cuts.iter().map(|c| (&c.coeffs, c.ub)).collect::<Vec<_>>()
    );
}
