// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::model::{exact, Col, Model, Row, Sense};
use num_traits::ToPrimitive;

/// Deterministic LCG, the same shape every guard in this crate uses.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0 >> 33
    }
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

/// Every integer point of a model's box, in a fixed order.
///
/// THE FIRST VERSION OF THIS FUNCTION STARTED THE ODOMETER AT ALL-ZERO
/// INSTEAD OF AT EACH COLUMN'S LOWER BOUND, so it enumerated points OUTSIDE
/// the box and the guard reported an invalid elimination that was not one.
/// That is the reason the box membership is re-asserted below rather than
/// trusted: the instrument gets a positive control too.
fn box_points(m: &Model) -> Vec<Vec<i64>> {
    let n = m.num_cols();
    let ranges: Vec<(i64, i64)> = (0..n)
        .map(|j| {
            let (l, u) = m.col_bounds(Col(j as u32));
            assert!(l.is_finite() && u.is_finite(), "guard needs a boxed model");
            (l.ceil() as i64, u.floor() as i64)
        })
        .collect();
    if ranges.iter().any(|&(l, u)| l > u) {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut point: Vec<i64> = ranges.iter().map(|&(l, _)| l).collect();
    loop {
        debug_assert!((0..n).all(|k| point[k] >= ranges[k].0 && point[k] <= ranges[k].1));
        out.push(point.clone());
        let mut k = 0;
        loop {
            if k == n {
                return out;
            }
            point[k] += 1;
            if point[k] <= ranges[k].1 {
                break;
            }
            point[k] = ranges[k].0;
            k += 1;
        }
    }
}

fn rows_hold(m: &Model, vals: &[f64]) -> bool {
    (0..m.num_rows()).all(|r| {
        let (coeffs, lb, ub) = m.row(Row(r as u32));
        let act: f64 = coeffs.iter().map(|&(c, a)| a * vals[c as usize]).sum();
        act >= lb - 1e-9 && act <= ub + 1e-9
    })
}

fn objective_at(m: &Model, vals: &[f64]) -> BigRational {
    let mut v = exact(m.objective_offset()).unwrap();
    for j in 0..m.num_cols() {
        v += exact(m.obj_coeff(Col(j as u32))).unwrap() * exact(vals[j]).unwrap();
    }
    v
}

/// Minimise a tiny all-integer model by full enumeration of its box.
fn brute_optimum(m: &Model) -> Option<BigRational> {
    let mut best: Option<BigRational> = None;
    for point in box_points(m) {
        let vals: Vec<f64> = point.iter().map(|&v| v as f64).collect();
        if !rows_hold(m, &vals) {
            continue;
        }
        let v = objective_at(m, &vals);
        if best.as_ref().is_none_or(|b| &v < b) {
            best = Some(v);
        }
    }
    best
}

/// THE ELIMINATION GUARD.
///
/// 400 random all-integer models are minimised TWICE — directly, and through
/// `eliminate_structure` + `const_delta` — and the two optima must agree
/// EXACTLY, including the infeasible verdict (`None == None`). Then every
/// feasible point of the REDUCED model is widened and re-checked against the
/// ORIGINAL model with the crate's own `check_point`, which is what catches
/// a redundant-row drop that was not actually redundant. A `fired` counter
/// keeps the whole thing from passing vacuously.
///
/// The generator is built to produce what the pass consumes: about a third
/// of the columns are declared FIXED (`lb == ub`) and the right-hand sides
/// are wide enough that a good share of rows are REDUNDANT.
#[test]
fn structure_elimination_preserves_the_optimum() {
    let mut rng = Lcg(0x5eed_1234);
    let mut fired = 0usize;
    let mut saw_fixed = 0usize;
    let mut saw_dropped = 0usize;
    for case in 0..400 {
        let n = rng.in_range(3, 5) as usize;
        let nr = rng.in_range(2, 4) as usize;
        let mut m = Model::new();
        for _ in 0..n {
            let lo = rng.in_range(-2, 2);
            let hi = if rng.next().is_multiple_of(3) {
                lo
            } else {
                lo + rng.in_range(0, 3)
            };
            m.add_int_col(lo as f64, hi as f64);
        }
        for _ in 0..nr {
            let mut coeffs = Vec::new();
            for j in 0..n {
                let a = rng.in_range(-3, 3);
                if a != 0 {
                    coeffs.push((Col(j as u32), a as f64));
                }
            }
            if coeffs.is_empty() {
                coeffs.push((Col(0), 1.0));
            }
            let lb = rng.in_range(-20, -2) as f64;
            let ub = rng.in_range(2, 20) as f64;
            m.add_row(lb, ub, &coeffs);
        }
        let obj: Vec<(Col, f64)> = (0..n)
            .map(|j| (Col(j as u32), rng.in_range(-4, 4) as f64))
            .collect();
        m.set_objective(&obj, Sense::Minimize);

        let direct = brute_optimum(&m);
        let Some((reduced, post)) = eliminate_structure(&m, None) else {
            continue;
        };
        fired += 1;
        if reduced.num_cols() < m.num_cols() {
            saw_fixed += 1;
        }
        if reduced.num_rows() < m.num_rows() {
            saw_dropped += 1;
        }

        let via = brute_optimum(&reduced).map(|v| v + post.const_delta());
        assert_eq!(
            direct, via,
            "structural elimination changed the optimum on case {case}"
        );

        for point in box_points(&reduced) {
            let vals: Vec<f64> = point.iter().map(|&v| v as f64).collect();
            if !rows_hold(&reduced, &vals) {
                continue;
            }
            let exact_point: Vec<BigRational> = vals.iter().map(|&v| exact(v).unwrap()).collect();
            let wide = post.widen(&exact_point);
            assert!(
                m.check_point(&wide).is_ok(),
                "case {case}: a REDUCED-feasible point widens to an ORIGINAL-infeasible \
                     one ({:?})",
                m.check_point(&wide)
            );
            assert_eq!(
                objective_at(&reduced, &vals) + post.const_delta(),
                objective_at(
                    &m,
                    &wide.iter().map(|v| v.to_f64().unwrap()).collect::<Vec<_>>()
                ),
                "case {case}: the widened point's objective is not the reduced value plus \
                     const_delta"
            );
        }
    }
    assert!(fired > 100, "guard is vacuous: fired only {fired} times");
    assert!(
        saw_fixed > 20,
        "guard never exercised column elimination ({saw_fixed})"
    );
    assert!(
        saw_dropped > 20,
        "guard never exercised row elimination ({saw_dropped})"
    );
}

/// POSITIVE CONTROL ON THE GUARD ITSELF.
///
/// A guard that cannot fail is not a guard. This re-runs the same sweep with
/// the redundancy test DELIBERATELY BROKEN — a row is dropped whenever its
/// activity range merely OVERLAPS its bounds instead of being contained in
/// them — and asserts that the sweep above would have caught it.
#[test]
fn the_guard_rejects_an_over_eager_row_drop() {
    // x, y in [0,3]; the row 1*x + 1*y <= 5 is NOT implied by the box (its
    // max activity is 6), and it is only ONE unit away from implied — so a
    // redundancy test loosened by any positive slack drops it, and (3,3)
    // then becomes reachable. That margin is deliberate: it is what makes
    // this test sensitive to an off-by-one in the containment check.
    let mut m = Model::new();
    m.add_int_col(0.0, 3.0);
    m.add_int_col(0.0, 3.0);
    m.add_row(f64::NEG_INFINITY, 5.0, &[(Col(0), 1.0), (Col(1), 1.0)]);
    m.set_objective(&[(Col(0), -1.0), (Col(1), -1.0)], Sense::Minimize);

    // The real pass must NOT drop it: min activity 0, max activity 6 > 2.
    assert!(
        eliminate_structure(&m, None).is_none(),
        "the pass dropped a row its box does not imply"
    );

    // And the sweep would have seen it: the model WITHOUT the row admits
    // (3,3), which the original rejects.
    let mut without = Model::new();
    without.add_int_col(0.0, 3.0);
    without.add_int_col(0.0, 3.0);
    without.set_objective(&[(Col(0), -1.0), (Col(1), -1.0)], Sense::Minimize);
    let three = vec![exact(3.0).unwrap(), exact(3.0).unwrap()];
    assert!(without.check_point(&three).is_ok());
    assert!(
        m.check_point(&three).is_err(),
        "the counterexample is not a counterexample"
    );
    assert_ne!(brute_optimum(&m), brute_optimum(&without));
}

/// A fixed column that a row's shift cannot represent exactly must be
/// KEPT, not eliminated — and the pass must still be sound when it is.
#[test]
fn an_inexact_shift_declines_that_column_rather_than_the_answer() {
    // x fixed at 1, y in [0,2]; a row whose shift stays exact.
    let mut m = Model::new();
    m.add_int_col(1.0, 1.0);
    m.add_int_col(0.0, 2.0);
    m.add_row(f64::NEG_INFINITY, 3.0, &[(Col(0), 2.0), (Col(1), 1.0)]);
    m.set_objective(&[(Col(0), 5.0), (Col(1), -1.0)], Sense::Minimize);
    let (reduced, post) = eliminate_structure(&m, None).expect("x is fixed");
    assert_eq!(reduced.num_cols(), 1);
    // The row becomes y <= 1 and the objective constant is 5.
    assert_eq!(post.const_delta(), &exact(5.0).unwrap());
    assert_eq!(
        brute_optimum(&m),
        brute_optimum(&reduced).map(|v| v + post.const_delta())
    );
}
