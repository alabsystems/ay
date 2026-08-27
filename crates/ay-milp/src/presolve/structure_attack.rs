// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ADVERSARIAL GUARDS for `presolve::structure`, written by a reviewer who did
//! not write the pass. Deliberately covers the dimensions the shipped guard's
//! generator does NOT reach: Maximize, equality rows, one-sided rows, empty
//! rows, duplicate rows, binary columns, a non-zero objective offset,
//! non-dyadic-friendly coefficients (0.1), and — the direction the shipped
//! guard never checks — that no ORIGINAL-feasible point is LOST.

#![cfg(test)]

use num_rational::BigRational;
use num_traits::Zero;

use super::structure::eliminate_structure;
use crate::model::{exact, Col, ColKind, Model, Row, Sense};

mod continuous;
mod corpus;
mod verdict_shape;

struct R(u64);
impl R {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
    fn chance(&mut self, k: u64) -> bool {
        self.next().is_multiple_of(k)
    }
}

/// Every integer point of a fully boxed model, odometer started at each
/// column's lower bound.
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
    let total: i64 = ranges.iter().map(|&(l, u)| u - l + 1).product();
    assert!(total < 200_000, "generator produced too large a box");
    let mut out = Vec::new();
    let mut point: Vec<i64> = ranges.iter().map(|&(l, _)| l).collect();
    loop {
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

fn exact_pt(p: &[i64]) -> Vec<BigRational> {
    p.iter()
        .map(|&v| BigRational::from_integer(v.into()))
        .collect()
}

/// The model's own exact feasibility verdict — bounds, rows AND integrality.
fn feasible(m: &Model, x: &[BigRational]) -> bool {
    m.check_point(x).is_ok()
}

fn objective_at(m: &Model, x: &[BigRational]) -> BigRational {
    let mut v = exact(m.objective_offset()).unwrap();
    for j in 0..m.num_cols() {
        v += exact(m.obj_coeff(Col(j as u32))).unwrap() * &x[j];
    }
    v
}

/// Best objective under the model's OWN sense, by full enumeration.
fn brute_best(m: &Model) -> Option<BigRational> {
    let mut best: Option<BigRational> = None;
    for p in box_points(m) {
        let x = exact_pt(&p);
        if !feasible(m, &x) {
            continue;
        }
        let v = objective_at(m, &x);
        let better = match (&best, m.sense()) {
            (None, _) => true,
            (Some(b), Sense::Minimize) => &v < b,
            (Some(b), Sense::Maximize) => &v > b,
        };
        if better {
            best = Some(v);
        }
    }
    best
}

/// Restrict a full point to the reduced column space using the postsolve map.
fn restrict(
    post: &super::structure::StructurePostsolve,
    x: &[BigRational],
    ncols: usize,
) -> Vec<BigRational> {
    let mut red = vec![BigRational::zero(); ncols];
    for (orig, slot) in post.map.iter().enumerate() {
        if let Some(nc) = slot {
            red[nc.index()] = x[orig].clone();
        }
    }
    red
}

/// A pool of coefficient values, including ones whose exact rational has a huge
/// denominator (0.1) so the shift-exactness fixpoint is actually exercised.
fn coeff(r: &mut R) -> f64 {
    match r.next() % 10 {
        0..=4 => r.range(-3, 3) as f64,
        5 => 0.5 * r.range(-5, 5) as f64,
        6 => 0.25 * r.range(-5, 5) as f64,
        7 => 0.1 * r.range(-5, 5) as f64,
        8 => 1.0 / 3.0 * r.range(-3, 3) as f64,
        _ => r.range(-8, 8) as f64,
    }
}

/// Build one adversarial all-integer model. Returns `None` when the generator
/// produced something degenerate (no columns in any row, box too large).
fn gen_model(r: &mut R) -> Model {
    let n = r.range(3, 5) as usize;
    let mut m = Model::new();
    for _ in 0..n {
        if r.chance(4) {
            m.add_binary_col();
        } else {
            let lo = r.range(-2, 2);
            let hi = if r.chance(3) { lo } else { lo + r.range(0, 3) };
            m.add_int_col(lo as f64, hi as f64);
        }
    }
    let nr = r.range(2, 4) as usize;
    let mut last: Option<(f64, f64, Vec<(Col, f64)>)> = None;
    for _ in 0..nr {
        // 1 in 8 rows is an EXACT DUPLICATE of the previous one.
        if r.chance(8) {
            if let Some((lb, ub, c)) = last.clone() {
                m.add_row(lb, ub, &c);
                continue;
            }
        }
        // 1 in 10 rows is EMPTY (satisfied — an unsatisfied one makes the model
        // infeasible and the pass declines, which is tested separately).
        if r.chance(10) {
            m.add_row(-1.0, 1.0, &[]);
            continue;
        }
        let mut c: Vec<(Col, f64)> = Vec::new();
        for j in 0..n {
            let a = coeff(r);
            if a != 0.0 {
                c.push((Col(j as u32), a));
            }
        }
        if c.is_empty() {
            c.push((Col(0), 1.0));
        }
        // Activity range over the declared box, so the RHS can be placed to make
        // the row binding, redundant, or anywhere between — deliberately.
        let (mut amin, mut amax) = (0.0f64, 0.0f64);
        for &(col, a) in &c {
            let (l, u) = m.col_bounds(col);
            if a > 0.0 {
                amin += a * l;
                amax += a * u;
            } else {
                amin += a * u;
                amax += a * l;
            }
        }
        let span = (amax - amin).max(1.0);
        let (lb, ub) = match r.next() % 5 {
            // RANGED, usually redundant
            0 => (amin - r.range(0, 3) as f64, amax + r.range(0, 3) as f64),
            // RANGED, usually cutting
            1 => (
                amin + 0.25 * span * r.range(0, 2) as f64,
                amax - 0.25 * span * r.range(0, 2) as f64,
            ),
            // EQUALITY at a point of the activity range
            2 => {
                let v = (amin + 0.5 * span * (r.range(0, 2) as f64)).round();
                (v, v)
            }
            // <= only
            3 => (f64::NEG_INFINITY, amax - 0.25 * span * r.range(0, 2) as f64),
            // >= only
            _ => (amin + 0.25 * span * r.range(0, 2) as f64, f64::INFINITY),
        };
        m.add_row(lb, ub, &c);
        last = Some((lb, ub, c));
    }
    let obj: Vec<(Col, f64)> = (0..n)
        .map(|j| (Col(j as u32), coeff(r)))
        .filter(|&(_, a)| a != 0.0)
        .collect();
    let sense = if r.chance(2) {
        Sense::Maximize
    } else {
        Sense::Minimize
    };
    m.set_objective(&obj, sense);
    if r.chance(3) {
        m.set_objective_offset(0.5 * r.range(-6, 6) as f64);
    }
    m
}

/// THE ATTACK. For 3000 adversarial models:
///  1. the optimum under the model's OWN sense must be preserved exactly;
///  2. NO ORIGINAL-FEASIBLE POINT MAY BE LOST — every one must restrict to a
///     reduced-feasible point at the same objective (the direction the shipped
///     guard does not check);
///  3. a point that propagation declared FIXED must actually be constant over
///     the whole original feasible set (this is what makes the deletion legal);
///  4. no reduced-feasible point may widen to an original-INFEASIBLE one.
#[test]
fn attack_structure_elimination() {
    let mut r = R(0xA77A_C401);
    let (mut fired, mut sf, mut sd, mut maxi, mut eq_rows) =
        (0usize, 0usize, 0usize, 0usize, 0usize);
    for case in 0..3000 {
        let m = gen_model(&mut r);
        if (0..m.num_rows()).any(|i| {
            let (_, l, u) = m.row(Row(i as u32));
            l == u && l.is_finite()
        }) {
            eq_rows += 1;
        }
        let direct = brute_best(&m);
        let Some((reduced, post)) = eliminate_structure(&m, None) else {
            continue;
        };
        fired += 1;
        if reduced.num_cols() < m.num_cols() {
            sf += 1;
        }
        if reduced.num_rows() < m.num_rows() {
            sd += 1;
        }
        if m.sense() == Sense::Maximize {
            maxi += 1;
        }

        // (1) OPTIMUM, under the model's own sense.
        let via = brute_best(&reduced).map(|v| v + post.const_delta());
        assert_eq!(
            direct,
            via,
            "case {case}: elimination changed the optimum (sense {:?})",
            m.sense()
        );

        // (2)+(3) NO WITNESS IS LOST, and every eliminated column really is
        // constant over the original feasible set.
        for p in box_points(&m) {
            let x = exact_pt(&p);
            if !feasible(&m, &x) {
                continue;
            }
            for rec in &post.recover {
                assert_eq!(
                    x[rec.col], rec.value,
                    "case {case}: column {} was ELIMINATED as fixed at {} but the original \
                     model has a feasible point with {} there",
                    rec.col, rec.value, x[rec.col]
                );
            }
            let red = restrict(&post, &x, reduced.num_cols());
            assert!(
                feasible(&reduced, &red),
                "case {case}: an ORIGINAL-feasible point does not survive into the reduced \
                 model ({:?})",
                reduced.check_point(&red)
            );
            assert_eq!(
                objective_at(&reduced, &red) + post.const_delta(),
                objective_at(&m, &x),
                "case {case}: objective not preserved on a restricted witness"
            );
        }

        // (4) NO SPURIOUS POINT IS ADMITTED.
        for p in box_points(&reduced) {
            let red = exact_pt(&p);
            if !feasible(&reduced, &red) {
                continue;
            }
            let wide = post.widen(&red);
            assert!(
                m.check_point(&wide).is_ok(),
                "case {case}: a REDUCED-feasible point widens to an ORIGINAL-INFEASIBLE one \
                 ({:?})",
                m.check_point(&wide)
            );
            assert_eq!(
                objective_at(&reduced, &red) + post.const_delta(),
                objective_at(&m, &wide),
                "case {case}: objective not preserved on a widened witness"
            );
        }
    }
    eprintln!(
        "ATTACK COVERAGE: fired {fired}/3000, col-elim {sf}, row-elim {sd}, maximize {maxi}, \
         equality-row models {eq_rows}"
    );
    assert!(fired > 300, "attack is vacuous: fired {fired}");
    assert!(sf > 50, "never exercised column elimination ({sf})");
    assert!(sd > 50, "never exercised row elimination ({sd})");
    assert!(maxi > 50, "never exercised Maximize ({maxi})");
    assert!(eq_rows > 50, "never generated an equality row ({eq_rows})");
}

/// An UNSATISFIED empty row means the model is infeasible. The pass must not
/// silently drop it (which would turn INFEASIBLE into a bogus optimum).
#[test]
fn attack_unsatisfied_empty_row_is_not_dropped() {
    let mut m = Model::new();
    m.add_int_col(0.0, 3.0);
    m.add_int_col(0.0, 3.0);
    m.add_row(2.0, 5.0, &[]); // 0 in [2,5] is FALSE
    m.add_row(f64::NEG_INFINITY, 10.0, &[(Col(0), 1.0), (Col(1), 1.0)]);
    m.set_objective(&[(Col(0), 1.0)], Sense::Minimize);
    assert!(brute_best(&m).is_none(), "the model really is infeasible");
    if let Some((reduced, post)) = eliminate_structure(&m, None) {
        assert!(
            brute_best(&reduced).is_none(),
            "an infeasible model reduced to a FEASIBLE one (const_delta {})",
            post.const_delta()
        );
    }
}

/// A column fixed at a FRACTIONAL value, declared INTEGER: the model is
/// infeasible and the pass must not manufacture an integral answer.
#[test]
fn attack_fractional_fixed_integer_column() {
    let mut m = Model::new();
    let a = m.add_int_col(0.5, 0.5);
    let b = m.add_int_col(0.0, 3.0);
    m.add_row(f64::NEG_INFINITY, 4.0, &[(a, 1.0), (b, 1.0)]);
    m.set_objective(&[(b, 1.0)], Sense::Minimize);
    if let Some((reduced, post)) = eliminate_structure(&m, None) {
        panic!(
            "declined-case escaped: reduced {}r/{}c delta {}",
            reduced.num_rows(),
            reduced.num_cols(),
            post.const_delta()
        );
    }
}

/// Sanity: `ColKind` survives the rebuild. An integral column must not come
/// back CONTINUOUS (that would legalise fractional answers).
#[test]
fn attack_column_kinds_survive() {
    let mut m = Model::new();
    let a = m.add_int_col(2.0, 2.0); // fixed, eliminated
    let b = m.add_int_col(0.0, 5.0);
    let c = m.add_binary_col();
    let d = m.add_col(0.0, 4.0);
    m.add_row(
        f64::NEG_INFINITY,
        100.0,
        &[(a, 1.0), (b, 1.0), (c, 1.0), (d, 1.0)],
    );
    m.add_row(0.0, 6.0, &[(b, 1.0), (d, 1.0)]);
    m.set_objective(&[(b, -1.0), (c, -1.0), (d, -1.0)], Sense::Minimize);
    let (reduced, post) = eliminate_structure(&m, None).expect("a is fixed");
    for j in 0..m.num_cols() {
        if let Some(nc) = post.map[j] {
            assert_eq!(
                m.col_kind(Col(j as u32)).is_integral(),
                reduced.col_kind(nc).is_integral(),
                "column {j} changed integrality across the reduction"
            );
            let (l0, u0) = m.col_bounds(Col(j as u32));
            let (l1, u1) = reduced.col_bounds(nc);
            assert!(
                l1 >= l0 - 1e-12 && u1 <= u0 + 1e-12,
                "column {j} box widened"
            );
        }
    }
    assert!(matches!(
        reduced.col_kind(post.map[2].unwrap()),
        ColKind::Binary
    ));
}
