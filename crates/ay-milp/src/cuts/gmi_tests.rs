// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GMI validity and floating-point conversion regressions.

use super::*;
use crate::model::Sense;
use crate::simplex::FloatLp;

fn assert_free_column_cuts(
    rows: &[(Vec<f64>, f64, f64)],
    cuts: &[Cut],
    seed: u64,
    high: i64,
    free_high: i64,
) {
    for x0 in 0..=high {
        for x1 in 0..=high {
            for x2 in 0..=high {
                for y in -free_high..=free_high {
                    let point = [x0 as f64, x1 as f64, x2 as f64, y as f64];
                    let feasible = rows.iter().all(|(coefficients, lower, upper)| {
                        let activity: f64 = coefficients
                            .iter()
                            .zip(point)
                            .map(|(&coefficient, value)| coefficient * value)
                            .sum();
                        activity >= lower - 1e-9 && activity <= upper + 1e-9
                    });
                    if !feasible {
                        continue;
                    }
                    for cut in cuts {
                        let activity: f64 = cut
                            .coeffs
                            .iter()
                            .map(|&(column, coefficient)| coefficient * point[column.index()])
                            .sum();
                        assert!(
                            activity <= cut.ub + 1e-6 && activity >= cut.lb - 1e-6,
                            "GMI cut deleted the feasible integer point {point:?}: \
                             {} <= {activity} <= {} (seed {seed:#x})",
                            cut.lb,
                            cut.ub
                        );
                    }
                }
            }
        }
    }
}

fn assert_unbounded_column_cuts(
    case: usize,
    rows: &[(Vec<f64>, f64, f64)],
    cuts: &[Cut],
    seed: u64,
    high: i64,
) {
    for x0 in 0..=high {
        for x1 in -high..=0 {
            for x2 in 0..=high {
                for x3 in 0..=high {
                    let point = [x0 as f64, x1 as f64, x2 as f64, x3 as f64];
                    let feasible = rows.iter().all(|(coefficients, lower, upper)| {
                        let activity: f64 = coefficients
                            .iter()
                            .zip(point)
                            .map(|(&coefficient, value)| coefficient * value)
                            .sum();
                        activity >= lower - 1e-9 && activity <= upper + 1e-9
                    });
                    if !feasible {
                        continue;
                    }
                    for cut in cuts {
                        let mut activity = BigRational::zero();
                        for &(column, coefficient) in &cut.coeffs {
                            activity +=
                                exact(coefficient).unwrap() * exact(point[column.index()]).unwrap();
                        }
                        if cut.lb.is_finite() {
                            assert!(
                                activity >= exact(cut.lb).unwrap(),
                                "case {case}: a `>=` cut deleted the feasible integer \
                                 point {point:?}: activity {activity} < {} (seed {seed:#x})",
                                cut.lb
                            );
                        }
                        if cut.ub.is_finite() {
                            assert!(
                                activity <= exact(cut.ub).unwrap(),
                                "case {case}: a `<=` cut deleted the feasible integer \
                                 point {point:?}: activity {activity} > {} (seed {seed:#x})",
                                cut.ub
                            );
                        }
                    }
                }
            }
        }
    }
}

/// A GMI CUT MAY NOT DELETE AN INTEGER POINT — with FREE non-basic columns present.
///
/// `separate_gmi` used to refuse a model outright the moment any non-basic column was
/// free, because `t_j = x_j − l_j` does not exist for a column with no finite bound.
/// The refusal is now per ROW and per COEFFICIENT: a row is abandoned only when a free
/// column has a nonzero ᾱ_ij in it. That is a strictly larger set of accepted rows, so
/// it is exactly the change that could manufacture an invalid cut, and an invalid cut
/// is a wrong OPTIMAL — the one failure this engine may never have.
///
/// So: random models carrying free integer columns whose range is pinned by ROWS
/// rather than by column bounds (which is what makes them free to the LP while
/// leaving the feasible set finite and enumerable), separate GMI from the relaxation
/// optimum, then enumerate every integer point of the box and check that every point
/// the MODEL admits satisfies every cut.
#[test]
fn gmi_cuts_never_remove_an_integer_point_with_free_columns() {
    let mut seed = 0x6D11_2026_u64;
    const HI: i64 = 4;
    const FREE_HI: i64 = 3;

    let mut cases_with_cuts = 0usize;
    for _case in 0..300 {
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut m = Model::new();
        // Two ordinary bounded integer columns, one bounded continuous column...
        let b0 = m.add_int_col(0.0, HI as f64);
        let b1 = m.add_int_col(0.0, HI as f64);
        let c0 = m.add_col(0.0, HI as f64);
        // ...and a FREE integer column: infinite column bounds, so the simplex may
        // rest it non-basic at zero (`NbBound::Zero`), which is the state the old
        // model-wide bail existed for.
        let fr = m.add_int_col(f64::NEG_INFINITY, f64::INFINITY);
        let cols = [b0, b1, c0, fr];

        // The free column's range comes from ROWS, so enumeration below is complete.
        m.add_row(f64::NEG_INFINITY, FREE_HI as f64, &[(fr, 1.0)]);
        m.add_row(-(FREE_HI as f64), f64::INFINITY, &[(fr, 1.0)]);

        let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();
        for _ in 0..3 {
            let a: Vec<f64> = (0..4).map(|_| (rnd().rem_euclid(7) - 3) as f64).collect();
            if a.iter().all(|&v| v == 0.0) {
                continue;
            }
            let ub = (rnd().rem_euclid(13) - 2) as f64;
            m.add_row(
                f64::NEG_INFINITY,
                ub,
                &a.iter()
                    .enumerate()
                    .filter(|&(_, &v)| v != 0.0)
                    .map(|(j, &v)| (cols[j], v))
                    .collect::<Vec<_>>(),
            );
            rows.push((a, f64::NEG_INFINITY, ub));
        }
        if rows.is_empty() {
            continue;
        }
        let obj: Vec<(Col, f64)> = (0..4)
            .map(|j| (cols[j], (rnd().rem_euclid(5) - 2) as f64))
            .collect();
        m.set_objective(&obj, Sense::Minimize);

        let objective: Vec<(u32, f64)> = (0..m.num_cols())
            .map(|j| (j as u32, m.obj_coeff(Col(j as u32))))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let Some(lp) = FloatLp::from_model(&m, &objective, Sense::Minimize) else {
            continue;
        };
        let cand = lp.solve_bounded(&lp.lower.clone(), &lp.upper.clone(), None, None);
        if cand.status != crate::simplex::SimplexStatus::Optimal {
            continue;
        }
        let cuts = separate_gmi(&m, &lp, &cand, None, m.num_rows(), m.num_cols());
        if cuts.is_empty() {
            continue;
        }
        cases_with_cuts += 1;

        // The continuous column is swept on an integer-lattice subset of its feasible interval.
        assert_free_column_cuts(&rows, &cuts, seed, HI, FREE_HI);
    }
    // A separator that returns nothing passes a "never deletes a point" test
    // vacuously, so the test asserts it actually SEPARATED on this population —
    // otherwise the model-wide bail could come back and the guard would not notice.
    assert!(
        cases_with_cuts >= 10,
        "only {cases_with_cuts} cases produced GMI cuts; the guard is near-vacuous"
    );
}

/// THE FOUR DIRECTED-ROUNDING CORNERS, AND THE ONE REFUSAL.
///
/// [`coef_to_f64`] is the only place in this file where getting a SIGN backwards produces an
/// inequality that is stronger than the exact one it claims to represent — which is a deleted
/// optimum, reported as OPTIMAL. The brute-force guard below catches that on models; this
/// catches it on the arithmetic, where the failure message names the corner.
///
/// `1/3` is not an `f64`, so every conversion here really does move the coefficient and the
/// `err.is_zero()` short-circuit cannot make the test vacuous.
#[test]
fn coef_to_f64_rounds_the_way_the_stored_side_needs() {
    let mut m = Model::new();
    let nonneg = m.add_int_col(0.0, f64::INFINITY);
    let nonpos = m.add_int_col(f64::NEG_INFINITY, 0.0);
    let free = m.add_int_col(f64::NEG_INFINITY, f64::INFINITY);
    let straddle = m.add_int_col(-3.0, f64::INFINITY);
    let boxed = m.add_int_col(0.0, 10.0);

    let third = BigRational::new(1.into(), 3.into());
    for c in [third.clone(), -third] {
        // `>=` store: the term must never SHRINK, so a non-negative column rounds up and a
        // non-positive one rounds down.
        let (f, cost) = coef_to_f64(&m, nonneg, &c, CutSide::Ge).unwrap();
        assert!(cost.is_zero(), "a directed store owes no damage");
        assert!(
            exact(f).unwrap() >= c,
            "Ge / x>=0 must round UP: {f} vs {c}"
        );
        let (f, cost) = coef_to_f64(&m, nonpos, &c, CutSide::Ge).unwrap();
        assert!(cost.is_zero());
        assert!(
            exact(f).unwrap() <= c,
            "Ge / x<=0 must round DOWN: {f} vs {c}"
        );
        // `<=` store: the term must never GROW, so both directions flip.
        let (f, cost) = coef_to_f64(&m, nonneg, &c, CutSide::Le).unwrap();
        assert!(cost.is_zero());
        assert!(
            exact(f).unwrap() <= c,
            "Le / x>=0 must round DOWN: {f} vs {c}"
        );
        let (f, cost) = coef_to_f64(&m, nonpos, &c, CutSide::Le).unwrap();
        assert!(cost.is_zero());
        assert!(
            exact(f).unwrap() >= c,
            "Le / x<=0 must round UP: {f} vs {c}"
        );

        // No sign, no argument — and one open side is not enough if the column straddles zero.
        for col in [free, straddle] {
            for side in [CutSide::Ge, CutSide::Le] {
                assert!(
                    coef_to_f64(&m, col, &c, side).is_none(),
                    "a column with no sign must still refuse the cut"
                );
            }
        }

        // A two-sided-finite box keeps the OLD behaviour verbatim: the nearest `f64`, and the
        // span payment. Moving that to directed rounding would cost a full ulp of coefficient
        // to save a payment the box can already afford.
        let (f, cost) = coef_to_f64(&m, boxed, &c, CutSide::Ge).unwrap();
        assert_eq!(
            f,
            c.to_f64().unwrap(),
            "a boxed column takes the nearest f64"
        );
        assert_eq!(cost, (&exact(f).unwrap() - &c).abs() * exact(10.0).unwrap());
    }
}

/// A CUT MAY NOT DELETE AN INTEGER POINT WHEN A COLUMN HAS NO FINITE BOUND ON ONE SIDE.
///
/// Five emitters used to pay for their `f64` rounding over the column's SPAN and refuse the
/// whole cut when that span was infinite. [`coef_to_f64`] now rounds such a coefficient in the
/// direction the column's SIGN makes free instead, which weakens the row rather than
/// discarding it — but a flipped direction TIGHTENS it, and a tightened cut deletes an
/// optimum and reports OPTIMAL. So it is brute-forced, on both signs at once.
///
/// The model carries one integer column unbounded ABOVE (`lo = 0`) and one unbounded BELOW
/// (`up = 0`), each pinned to a finite range by a ROW rather than by its column bounds — which
/// is what leaves them unbounded to the separators while keeping the feasible set enumerable.
/// Every active family that shares the emitter is separated on the same models: the `>=` GMI
/// store and the `<=` stores (MIR, strong CG, aggregated MIR, tableau MIR, dual-aggregate MIR).
///
/// NEGATIVE CONTROL, run and recorded — BOTH directions, because a guard that cannot fail
/// proves nothing:
///   * `(CutSide::Ge, lo >= 0)` flipped to round DOWN: fails at case 46, `a >= cut deleted the
///     feasible integer point [2.0, -2.0, 0.0, 3.0]`.
///   * `(CutSide::Le, lo >= 0)` flipped to round UP: fails at case 2, `a <= cut deleted the
///     feasible integer point [3.0, -1.0, 4.0, 4.0]`.
/// Both flips were made, the failures observed, and both reverted.
///
/// The first draft of this guard could NOT fail either flip: it compared the `f64` activity
/// against `cut.lb - 1e-6`, and a wrong rounding direction is one ulp. The exact evaluation
/// below is what makes it a control, and the reason is recorded at the assertion itself.
#[test]
fn cuts_never_remove_an_integer_point_with_an_unbounded_column() {
    let mut seed = 0x11B0_2026_u64;
    const HI: i64 = 4;

    let mut touching = 0usize;
    for case in 0..300 {
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut m = Model::new();
        let up_free = m.add_int_col(0.0, f64::INFINITY); // unbounded ABOVE, x >= 0
        let dn_free = m.add_int_col(f64::NEG_INFINITY, 0.0); // unbounded BELOW, x <= 0
        let ints = m.add_int_col(0.0, HI as f64);
        let cont = m.add_col(0.0, HI as f64);
        let cols = [up_free, dn_free, ints, cont];
        let n = cols.len();

        let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();
        m.add_row(f64::NEG_INFINITY, HI as f64, &[(up_free, 1.0)]);
        rows.push((vec![1.0, 0.0, 0.0, 0.0], f64::NEG_INFINITY, HI as f64));
        m.add_row(-(HI as f64), f64::INFINITY, &[(dn_free, 1.0)]);
        rows.push((vec![0.0, 1.0, 0.0, 0.0], -(HI as f64), f64::INFINITY));

        for _ in 0..3 {
            let a: Vec<f64> = (0..n).map(|_| (rnd().rem_euclid(7) - 3) as f64).collect();
            if a.iter().all(|&v| v == 0.0) {
                continue;
            }
            let ub = (rnd().rem_euclid(13) - 4) as f64;
            let terms: Vec<_> = cols
                .iter()
                .zip(&a)
                .filter(|&(_, &v)| v != 0.0)
                .map(|(&c, &v)| (c, v))
                .collect();
            m.add_row(f64::NEG_INFINITY, ub, &terms);
            rows.push((a, f64::NEG_INFINITY, ub));
        }
        if rows.len() == 2 {
            continue;
        }
        let obj: Vec<(Col, f64)> = cols
            .iter()
            .map(|&c| (c, (rnd().rem_euclid(5) - 2) as f64))
            .collect();
        m.set_objective(&obj, Sense::Minimize);

        let objective: Vec<(u32, f64)> = (0..m.num_cols())
            .map(|j| (j as u32, m.obj_coeff(Col(j as u32))))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let Some(lp) = FloatLp::from_model(&m, &objective, Sense::Minimize) else {
            continue;
        };
        let cand = lp.solve_bounded(&lp.lower.clone(), &lp.upper.clone(), None, None);
        if cand.status != crate::simplex::SimplexStatus::Optimal {
            continue;
        }
        let x: Vec<f64> = cand.values[..n].to_vec();

        let mut cuts = separate_gmi(&m, &lp, &cand, None, m.num_rows(), m.num_cols());
        cuts.extend(separate_mir(&m, &x, m.num_rows(), 8));
        cuts.extend(separate_strongcg(&m, &x, m.num_rows(), 8));
        cuts.extend(separate_mir_agg(&m, &x, m.num_rows(), 8));
        cuts.extend(separate_mir_tableau(&m, &lp, &cand));
        cuts.extend(separate_mir_dual_agg(&m, &lp, &cand));

        touching += cuts
            .iter()
            .filter(|c| {
                c.coeffs
                    .iter()
                    .any(|&(col, a)| a != 0.0 && (col == up_free || col == dn_free))
            })
            .count();

        // EXACT, zero-tolerance evaluation catches a one-ulp wrong rounding direction.
        assert_unbounded_column_cuts(case, &rows, &cuts, seed, HI);
    }
    // Under the bail this replaces, a stored cut carrying a nonzero coefficient on either
    // unbounded column was IMPOSSIBLE — the emitter refused the whole row. So this count is
    // both the anti-vacuity check and the direct evidence that the new path is what ran.
    assert!(
        touching >= 10,
        "only {touching} cuts touched an unbounded column; the guard is near-vacuous"
    );
}
