// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial c-MIR complementation soundness sweeps.

use super::*;
use crate::model::Sense;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        let i = self.below(xs.len() as u64) as usize;
        &xs[i]
    }
}

/// What the generator built, in a form the checker can reason about without the Model.
struct Spec {
    kinds: Vec<Kind>,
    lo: Vec<f64>,
    up: Vec<f64>,
    rows: Vec<(Vec<(usize, f64)>, f64, f64)>,
    cont: usize,
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Bin,
    Int,
    Cont,
}

fn continuous_interval(spec: &Spec, point: &[f64]) -> Option<(f64, f64)> {
    let mut lower = spec.lo[spec.cont];
    let mut upper = spec.up[spec.cont];
    for (coeffs, row_lower, row_upper) in &spec.rows {
        let mut fixed = 0.0;
        let mut continuous = 0.0;
        for &(column, coefficient) in coeffs {
            if column == spec.cont {
                continuous = coefficient;
            } else {
                fixed += coefficient * point[column];
            }
        }
        if continuous == 0.0 {
            if fixed < row_lower - 1e-9 || fixed > row_upper + 1e-9 {
                return None;
            }
            continue;
        }
        let (lo, up) = if continuous > 0.0 {
            (
                (row_lower - fixed) / continuous,
                (row_upper - fixed) / continuous,
            )
        } else {
            (
                (row_upper - fixed) / continuous,
                (row_lower - fixed) / continuous,
            )
        };
        if lo.is_finite() {
            lower = lower.max(lo);
        }
        if up.is_finite() {
            upper = upper.min(up);
        }
    }
    (lower <= upper).then_some((lower, upper))
}

fn assert_endpoint_admitted(spec: &Spec, cuts: &[Cut], what: &str, point: &[f64]) -> bool {
    let mut margin = f64::INFINITY;
    for (coeffs, lower, upper) in &spec.rows {
        let activity: f64 = coeffs.iter().map(|&(j, a)| a * point[j]).sum();
        if lower.is_finite() {
            margin = margin.min(activity - lower);
        }
        if upper.is_finite() {
            margin = margin.min(upper - activity);
        }
    }
    for j in 0..spec.kinds.len() {
        if spec.lo[j].is_finite() {
            margin = margin.min(point[j] - spec.lo[j]);
        }
        if spec.up[j].is_finite() {
            margin = margin.min(spec.up[j] - point[j]);
        }
    }
    if margin < -1e-9 {
        return false;
    }
    let scale = point.iter().map(|v| v.abs()).fold(1.0, f64::max);
    for cut in cuts {
        let activity: f64 = cut.coeffs.iter().map(|&(j, a)| a * point[j.index()]).sum();
        let tolerance = 1e-6 * scale * cut.coeffs.iter().map(|&(_, a)| a.abs()).fold(1.0, f64::max);
        if activity > cut.ub + tolerance || activity < cut.lb - tolerance {
            panic!(
                "{what}: CUT DELETES A FEASIBLE POINT\n  point   {point:?}\n  \
                 feasible by margin {margin}\n  cut     {:?} in [{}, {}]\n  \
                 activity {activity}\n  rows    {:?}\n  lo {:?} up {:?}",
                cut.coeffs, cut.lb, cut.ub, spec.rows, spec.lo, spec.up
            );
        }
    }
    true
}

/// Enumerate every model-feasible point and assert each cut admits it.
///
/// `strict` is the margin by which a point must be feasible before a violation is believed --
/// it keeps a boundary point whose f64 evaluation lands a hair outside the row from being
/// reported as a soundness failure.
fn assert_admits_every_feasible_point(spec: &Spec, cuts: &[Cut], what: &str) -> usize {
    let n = spec.kinds.len();
    // The integer columns' grids.
    let mut grids: Vec<Vec<f64>> = Vec::with_capacity(n);
    for j in 0..n {
        if j == spec.cont {
            grids.push(vec![f64::NAN]); // filled per-assignment
            continue;
        }
        let a = spec.lo[j].ceil() as i64;
        let b = spec.up[j].floor() as i64;
        assert!(b - a <= 12, "grid too wide for an exhaustive proof");
        grids.push((a..=b).map(|v| v as f64).collect());
    }
    let mut idx = vec![0usize; n];
    let mut pts = 0usize;
    loop {
        // Build the integer part.
        let mut p = vec![0.0f64; n];
        for j in 0..n {
            if j != spec.cont {
                p[j] = grids[j][idx[j]];
            }
        }
        if let Some((tlo, thi)) = continuous_interval(spec, &p) {
            // A cut is LINEAR in the continuous column, so its extremes over [tlo, thi] are at
            // the endpoints; if the interval is unbounded there is nothing to check on that
            // side beyond what the endpoint gives (an unbounded ray would make any cut with a
            // nonzero coefficient there invalid, and the family refuses such rows -- checked
            // by the endpoint that IS finite).
            for &t in &[tlo, thi] {
                if !t.is_finite() {
                    continue;
                }
                p[spec.cont] = t;
                if assert_endpoint_admitted(spec, cuts, what, &p) {
                    pts += 1;
                }
            }
        }
        // odometer over the integer columns
        let mut k = 0;
        loop {
            if k == n {
                return pts;
            }
            if k == spec.cont {
                k += 1;
                continue;
            }
            idx[k] += 1;
            if idx[k] < grids[k].len() {
                break;
            }
            idx[k] = 0;
            k += 1;
        }
    }
}

fn add_random_column(
    model: &mut Model,
    random: &mut Rng,
    column: usize,
    continuous: usize,
    fractional_bounds: bool,
) -> (Kind, f64, f64) {
    if column == continuous {
        let (lo, up) = *random.pick(&[(0.0, 6.0), (-3.0, 4.0), (0.0, 10.0), (-5.0, 0.0)]);
        model.add_col(lo, up);
        return (Kind::Cont, lo, up);
    }
    match random.below(3) {
        0 => {
            model.add_binary_col();
            (Kind::Bin, 0.0, 1.0)
        }
        1 => {
            let (mut lo, mut up) =
                *random.pick(&[(0.0, 4.0), (-3.0, 3.0), (2.0, 6.0), (-4.0, 0.0)]);
            if fractional_bounds {
                if random.below(2) == 0 {
                    up += 0.5;
                }
                if random.below(2) == 0 {
                    lo -= 0.5;
                }
            }
            model.add_int_col(lo, up);
            let kind = if lo == 0.0 && up == 1.0 {
                Kind::Bin
            } else {
                Kind::Int
            };
            (kind, lo, up)
        }
        _ => {
            let (lo, up) = *random.pick(&[(0.0, 3.0), (0.0, 11.0), (-2.0, 2.0)]);
            model.add_int_col(lo, up);
            let kind = if lo == 0.0 && up == 1.0 {
                Kind::Bin
            } else {
                Kind::Int
            };
            (kind, lo, up)
        }
    }
}

/// Build a random model plus the `Spec` that mirrors it.
///
/// `frac_bounds` puts NON-INTEGRAL bounds on the integer columns -- the boundary case where
/// `t = u − x` is not an integer displacement even though the column is, which is precisely
/// what the knapsack policy's far-bound substitution leans on.
fn build(r: &mut Rng, frac_bounds: bool, vub_shape: bool) -> (Model, Spec) {
    let n = 4 + r.below(2) as usize; // 4 or 5 columns
    let cont = r.below(n as u64) as usize;
    let mut m = Model::new();
    let mut kinds = Vec::new();
    let mut lo = Vec::new();
    let mut up = Vec::new();
    for j in 0..n {
        let (kind, lower, upper) = add_random_column(&mut m, r, j, cont, frac_bounds);
        kinds.push(kind);
        lo.push(lower);
        up.push(upper);
    }
    let mut rows: Vec<(Vec<(usize, f64)>, f64, f64)> = Vec::new();
    let nrows = 2 + r.below(2) as usize;
    for k in 0..nrows {
        let mut coeffs: Vec<(usize, f64)> = Vec::new();
        if vub_shape && k == 0 {
            // x_cont − u·y <= 0, the VARIABLE UPPER BOUND the substitution keys on.
            let y = (0..n).find(|&j| kinds[j] == Kind::Bin);
            if let Some(y) = y {
                let u = *r.pick(&[2.0, 3.0, 5.0, 6.0]);
                coeffs.push((cont, 1.0));
                coeffs.push((y, -u));
                let cs: Vec<(Col, f64)> = coeffs.iter().map(|&(j, a)| (Col(j as u32), a)).collect();
                m.add_row(f64::NEG_INFINITY, 0.0, &cs);
                rows.push((coeffs, f64::NEG_INFINITY, 0.0));
                continue;
            }
        }
        for j in 0..n {
            let a = (r.below(11) as i64 - 5) as f64;
            if a != 0.0 {
                coeffs.push((j, a));
            }
        }
        if coeffs.is_empty() {
            continue;
        }
        // Range / one-sided / equality rows, and a right-hand side that is sometimes
        // fractional (the rounding's f is read off it).
        let hi = (r.below(15) as i64 - 4) as f64 + if r.below(3) == 0 { 0.5 } else { 0.0 };
        let (rlb, rub) = match r.below(4) {
            0 => (f64::NEG_INFINITY, hi),
            1 => (hi - (1 + r.below(8)) as f64, f64::INFINITY),
            2 => (hi - (1 + r.below(8)) as f64, hi),
            _ => (hi, hi), // equality
        };
        let cs: Vec<(Col, f64)> = coeffs.iter().map(|&(j, a)| (Col(j as u32), a)).collect();
        m.add_row(rlb, rub, &cs);
        rows.push((coeffs, rlb, rub));
    }
    m.set_objective(&[(Col(0), 1.0)], Sense::Minimize);
    (
        m,
        Spec {
            kinds,
            lo,
            up,
            rows,
            cont,
        },
    )
}

/// THE HARNESS. Every MIR-class separator, under BOTH complementation policies, on models
/// with integral and non-integral bounds, with and without the VUB shape.
fn sweep(seed: u64, frac_bounds: bool, vub_shape: bool, knap: bool) -> (usize, usize) {
    let mut r = Rng(seed);
    let mut cuts_seen = 0usize;
    let mut pts = 0usize;
    for _ in 0..400 {
        let (m, spec) = build(&mut r, frac_bounds, vub_shape);
        let nc = m.num_cols();
        let x: Vec<f64> = (0..nc)
            .map(|j| {
                let l = if spec.lo[j].is_finite() {
                    spec.lo[j]
                } else {
                    -5.0
                };
                let u = if spec.up[j].is_finite() {
                    spec.up[j]
                } else {
                    5.0
                };
                l + (u - l) * (r.below(100) as f64) / 100.0
            })
            .collect();
        let mut cuts = Vec::new();
        knap_scope(knap, || {
            cuts.extend(separate_mir(&m, &x, m.num_rows(), 8));
            cuts.extend(separate_strongcg(&m, &x, m.num_rows(), 8));
            cuts.extend(separate_mir_agg(&m, &x, m.num_rows(), 8));
        });
        cuts_seen += cuts.len();
        let tag = if knap { "knap" } else { "near" };
        pts += assert_admits_every_feasible_point(&spec, &cuts, tag);
    }
    (cuts_seen, pts)
}

#[test]
fn adv_integral_bounds_near() {
    let (c, p) = sweep(0xA11CE, false, false, false);
    eprintln!("adv_integral_bounds_near: {c} cuts, {p} points");
    assert!(c > 50, "harness separated almost nothing ({c})");
}

#[test]
fn adv_integral_bounds_knap() {
    let (c, p) = sweep(0xA11CE, false, false, true);
    eprintln!("adv_integral_bounds_knap: {c} cuts, {p} points");
    assert!(c > 50, "harness separated almost nothing ({c})");
}

#[test]
fn adv_vub_shape_near() {
    let (c, p) = sweep(0xBEEF01, false, true, false);
    eprintln!("adv_vub_shape_near: {c} cuts, {p} points");
}

#[test]
fn adv_vub_shape_knap() {
    let (c, p) = sweep(0xBEEF01, false, true, true);
    eprintln!("adv_vub_shape_knap: {c} cuts, {p} points");
}

#[test]
fn adv_fractional_int_bounds_near() {
    let (c, p) = sweep(0xF00D77, true, false, false);
    eprintln!("adv_fractional_int_bounds_near: {c} cuts, {p} points");
}

#[test]
fn adv_fractional_int_bounds_knap() {
    let (c, p) = sweep(0xF00D77, true, false, true);
    eprintln!("adv_fractional_int_bounds_knap: {c} cuts, {p} points");
}

#[test]
fn adv_fractional_int_bounds_vub_knap() {
    let (c, p) = sweep(0x1234ABCD, true, true, true);
    eprintln!("adv_fractional_int_bounds_vub_knap: {c} cuts, {p} points");
}

/// DEFAULT-OFF MEANS THE HISTORICAL FAMILY, BIT FOR BIT -- my own generator, all three
/// separators, coefficients compared as RAW BITS.
#[test]
fn adv_default_is_bit_identical_to_near() {
    let mut r = Rng(0x5150_2026);
    let mut n_cuts = 0;
    for _ in 0..500 {
        let (m, spec) = build(&mut r, false, true);
        let nc = m.num_cols();
        let x: Vec<f64> = (0..nc)
            .map(|j| {
                let l = if spec.lo[j].is_finite() {
                    spec.lo[j]
                } else {
                    -5.0
                };
                let u = if spec.up[j].is_finite() {
                    spec.up[j]
                } else {
                    5.0
                };
                l + (u - l) * (r.below(100) as f64) / 100.0
            })
            .collect();
        let dflt: Vec<Cut> = {
            let mut v = separate_mir(&m, &x, m.num_rows(), 8);
            v.extend(separate_strongcg(&m, &x, m.num_rows(), 8));
            v.extend(separate_mir_agg(&m, &x, m.num_rows(), 8));
            v
        };
        let near: Vec<Cut> = knap_scope(false, || {
            let mut v = separate_mir(&m, &x, m.num_rows(), 8);
            v.extend(separate_strongcg(&m, &x, m.num_rows(), 8));
            v.extend(separate_mir_agg(&m, &x, m.num_rows(), 8));
            v
        });
        assert_eq!(dflt.len(), near.len(), "default arm changed the cut count");
        for (a, b) in dflt.iter().zip(&near) {
            assert_eq!(a.coeffs.len(), b.coeffs.len());
            for (p, q) in a.coeffs.iter().zip(&b.coeffs) {
                assert_eq!(p.0.index(), q.0.index());
                assert_eq!(p.1.to_bits(), q.1.to_bits(), "coefficient differs by bits");
            }
            assert_eq!(a.ub.to_bits(), b.ub.to_bits());
            assert_eq!(a.lb.to_bits(), b.lb.to_bits());
        }
        n_cuts += dflt.len();
    }
    eprintln!("adv_default_is_bit_identical_to_near: {n_cuts} cuts compared");
    assert!(n_cuts > 100, "identity check was vacuous ({n_cuts} cuts)");
}

/// THE KNAPSACK ARM ACTUALLY CHANGES SOMETHING -- otherwise every validity sweep above is
/// vacuous. Counts models where the two policies emit different cut sets.
#[test]
fn adv_knap_arm_is_not_vacuous() {
    let mut r = Rng(0xC0FFEE_11);
    let mut differ = 0;
    let mut total = 0;
    for _ in 0..600 {
        let (m, spec) = build(&mut r, false, true);
        let nc = m.num_cols();
        let x: Vec<f64> = (0..nc)
            .map(|j| {
                let l = if spec.lo[j].is_finite() {
                    spec.lo[j]
                } else {
                    -5.0
                };
                let u = if spec.up[j].is_finite() {
                    spec.up[j]
                } else {
                    5.0
                };
                l + (u - l) * (r.below(100) as f64) / 100.0
            })
            .collect();
        let near = knap_scope(false, || separate_mir(&m, &x, m.num_rows(), 8));
        let knap = knap_scope(true, || separate_mir(&m, &x, m.num_rows(), 8));
        total += 1;
        let same = near.len() == knap.len()
            && near
                .iter()
                .zip(&knap)
                .all(|(a, b)| a.coeffs == b.coeffs && a.ub.to_bits() == b.ub.to_bits());
        if !same {
            differ += 1;
        }
    }
    eprintln!("adv_knap_arm_is_not_vacuous: {differ}/{total} models differ under the arm");
    assert!(
        differ > 0,
        "the knapsack arm never changed a single cut -- the validity sweeps are vacuous"
    );
}
