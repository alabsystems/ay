// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    add_up, gradual_underflow, separate_unit_box_hull, support_term, valid_arm, AffineArm,
    BoxHullCut,
};
use crate::ns::mul_up;
use std::collections::BTreeMap;

#[derive(Clone)]
struct Column {
    index: usize,
    arms: [f64; 4],
    sorted: [usize; 4],
}

fn supports(offsets: [f64; 4], columns: &[Column], slopes: &[f64]) -> [f64; 4] {
    let mut supports = offsets;
    for (col, slope) in columns.iter().zip(slopes) {
        for (support, coefficient) in supports.iter_mut().zip(col.arms) {
            *support += (coefficient - slope).abs();
        }
    }
    supports
}

fn maximum(values: [f64; 4]) -> f64 {
    values.into_iter().fold(f64::NEG_INFINITY, f64::max)
}

fn objective(offsets: [f64; 4], columns: &[Column], slopes: &[f64], point: &[f64]) -> f64 {
    maximum(supports(offsets, columns, slopes))
        + columns
            .iter()
            .zip(slopes)
            .map(|(col, s)| point[col.index] * s)
            .sum::<f64>()
}

// For a mixture supported uniformly on a subset of arms, the minimizer of
// x*s + mean(|a_i-s|) is a quantile of the selected coefficients.
fn quantile(column: &Column, mask: u8, point: f64) -> f64 {
    let rank = (1.0 - point) * 0.5 * f64::from(mask.count_ones());
    let mut count = 0_u32;
    let mut lower = None;
    for &arm in &column.sorted {
        if mask & (1 << arm) == 0 {
            continue;
        }
        let a = column.arms[arm];
        if let Some(b) = lower {
            return 0.5 * b + 0.5 * a;
        }
        count += 1;
        if f64::from(count) > rank {
            return a;
        }
        if f64::from(count) == rank {
            lower = Some(a);
        }
    }
    lower.unwrap_or(column.arms[column.sorted[3]])
}

// The common four-arm presentation orders two binary choices as 00,01,10,11.
// Adding the two individual separating slopes and removing their shared 00
// term provides a useful starting direction even when the arms are not additive.
fn paired_slope(arms: [AffineArm<'_>; 4], columns: &[Column], point: &[f64]) -> Option<Vec<f64>> {
    let mut slopes: Vec<_> = columns.iter().map(|col| -col.arms[0]).collect();
    for other in [1, 2] {
        let cut = separate_unit_box_hull(arms[0], arms[other], point, f64::MAX)?;
        for (index, slope) in cut.terms {
            let j = columns.binary_search_by_key(&index, |col| col.index).ok()?;
            slopes[j] += slope;
        }
    }
    Some(slopes)
}

fn polish(offsets: [f64; 4], columns: &[Column], order: &[usize], slopes: &mut [f64]) {
    let mut costs = supports(offsets, columns, slopes);
    for &j in order {
        let col = &columns[j];
        let rest = std::array::from_fn::<_, 4, _>(|i| costs[i] - (col.arms[i] - slopes[j]).abs());
        let minus = maximum(std::array::from_fn(|i| rest[i] - col.arms[i]));
        let plus = maximum(std::array::from_fn(|i| rest[i] + col.arms[i]));
        // With all other coordinates fixed the envelope is max(minus+s, plus-s).
        // Its kink minimizes the objective for every point coordinate in [-1,1].
        let kink = 0.5 * plus - 0.5 * minus;
        if kink.is_finite() {
            let s = kink.clamp(col.arms[col.sorted[0]], col.arms[col.sorted[3]]);
            costs = std::array::from_fn(|i| rest[i] + (col.arms[i] - s).abs());
            slopes[j] = s;
        }
    }
}

fn search_slopes(arms: [AffineArm<'_>; 4], columns: &[Column], point: &[f64]) -> Option<Vec<f64>> {
    let offsets = arms.map(|arm| arm.offset);
    let mut best = paired_slope(arms, columns, point);
    let mut lowest = best
        .as_ref()
        .map(|v| objective(offsets, columns, v, point))
        .filter(|v| v.is_finite())
        .unwrap_or(f64::INFINITY);
    for mask in 1..16 {
        let slopes: Vec<_> = columns
            .iter()
            .map(|col| quantile(col, mask, point[col.index]))
            .collect();
        let val = objective(offsets, columns, &slopes, point);
        if val.is_finite() && val < lowest {
            lowest = val;
            best = Some(slopes);
        }
    }
    let mut slopes = best?;
    let mut order: Vec<_> = (0..columns.len()).collect();
    let spread = |j: usize| {
        let col = &columns[j];
        col.arms[col.sorted[3]] - col.arms[col.sorted[0]]
    };
    order.sort_unstable_by(|&j, &k| spread(k).total_cmp(&spread(j)).then(j.cmp(&k)));
    let mut trial = slopes.clone();
    polish(offsets, columns, &order, &mut trial);
    if objective(offsets, columns, &trial, point) < lowest {
        slopes = trial;
    }

    Some(slopes)
}

fn fixed_slope(column: &Column, x: f64) -> Option<f64> {
    let lo = column.arms[column.sorted[0]];
    let hi = column.arms[column.sorted[3]];
    if x == 1.0 || lo == hi {
        Some(lo)
    } else if x == -1.0 {
        Some(hi)
    } else {
        None
    }
}

// At x = +1, s + |a - s| >= a with equality at s = min_i a_i
// for every arm. At x = -1 choose max_i a_i by the same argument.
// A coefficient common to all arms is also optimal for every x in the box.
// Fix those slopes and search only directions where a trade-off remains.
// Dropping their common point dot product changes no slope comparison.
fn face_slopes(arms: [AffineArm<'_>; 4], columns: &[Column], point: &[f64]) -> Option<Vec<f64>> {
    if !columns
        .iter()
        .any(|col| fixed_slope(col, point[col.index]).is_some())
    {
        return None;
    }
    let mut reduced = Vec::new();
    let mut offsets = arms.map(|a| a.offset);
    let mut terms: [Vec<(usize, f64)>; 4] = Default::default();
    for col in columns {
        if let Some(s) = fixed_slope(col, point[col.index]) {
            for (offset, a) in offsets.iter_mut().zip(col.arms) {
                *offset += (a - s).abs();
            }
        } else {
            reduced.push(col.clone());
            for (row, a) in terms.iter_mut().zip(col.arms) {
                if a != 0.0 {
                    row.push((col.index, a));
                }
            }
        }
    }
    if offsets.iter().any(|a| !a.is_finite()) {
        return None;
    }
    let mut free = if reduced.is_empty() {
        Vec::new()
    } else {
        let reduced_arms = std::array::from_fn(|i| AffineArm {
            offset: offsets[i],
            terms: &terms[i],
        });
        search_slopes(reduced_arms, &reduced, point)?
    }
    .into_iter();
    columns
        .iter()
        .map(|col| fixed_slope(col, point[col.index]).or_else(|| free.next()))
        .collect()
}

/// Separate a common upper plane for four affine arms on the same unit box.
///
/// For example, the sum of two two-way disjunctions has four joint arms.
/// The caller must establish all four source arms, including their offsets.
/// The returned plane is checked against each arm with outward arithmetic.
/// The search can leave a separable point open.
#[must_use]
pub fn separate_four_arm_unit_box_hull(
    arms: [AffineArm<'_>; 4],
    point: &[f64],
    value: f64,
) -> Option<BoxHullCut> {
    if !value.is_finite() || !gradual_underflow() || !arms.iter().all(|&a| valid_arm(a, point)) {
        return None;
    }
    let mut by_index = BTreeMap::new();
    for (i, arm) in arms.iter().enumerate() {
        for &(j, a) in arm.terms {
            by_index.entry(j).or_insert([0.0; 4])[i] = a;
        }
    }
    let columns: Vec<_> = by_index
        .into_iter()
        .map(|(index, arms)| {
            let mut sorted = [0, 1, 2, 3];
            sorted.sort_unstable_by(|&i, &j| arms[i].total_cmp(&arms[j]));
            Column {
                index,
                arms,
                sorted,
            }
        })
        .collect();
    let certify =
        |slopes| certified_cut(arms.map(|arm| arm.offset), &columns, slopes, point, value);
    // Changing the search space changes the heuristic on its remaining
    // coordinates. A failed face proposal must not hide a previous separation.
    face_slopes(arms, &columns, point)
        .and_then(&certify)
        .or_else(|| search_slopes(arms, &columns, point).and_then(certify))
}

fn certified_cut(
    offsets: [f64; 4],
    columns: &[Column],
    slopes: Vec<f64>,
    point: &[f64],
    value: f64,
) -> Option<BoxHullCut> {
    // Discard every search intercept. Each source arm is enclosed for the
    // exact binary64 coefficients that will be returned to the LP solver.
    let mut upper = offsets;
    let mut at_point = 0.0;
    let mut terms = Vec::new();
    for (col, slope) in columns.iter().zip(slopes) {
        if !slope.is_finite() {
            return None;
        }
        for (cost, a) in upper.iter_mut().zip(col.arms) {
            *cost = add_up(*cost, support_term(a, slope));
        }
        if slope != 0.0 {
            terms.push((col.index, slope));
            at_point = add_up(at_point, mul_up(slope, point[col.index]));
        }
    }
    if !upper.iter().all(|v| v.is_finite()) {
        return None;
    }
    let offset = maximum(upper);
    let limit = add_up(offset, at_point);
    (offset.is_finite() && limit.is_finite() && value > limit)
        .then_some(BoxHullCut { offset, terms })
}
