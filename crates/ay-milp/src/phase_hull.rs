// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Upper facets for affine disjunctions over a unit box.
//!
//! The caller establishes that at least one of the supplied upper bounds on a scalar
//! holds and that each referenced input is in [-1, 1]. This module separates a
//! violated affine upper bound using those premises. It introduces no columns.

use crate::ns::{mul_up, sub_up};
use std::cmp::Ordering;

#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
mod directed;
mod four_arm;
pub use four_arm::separate_four_arm_unit_box_hull;

/// One upper bound on the scalar, valid on one arm of the disjunction.
#[derive(Debug, Clone, Copy)]
pub struct AffineArm<'a> {
    /// Constant term.
    pub offset: f64,
    /// Sparse coefficients in strictly increasing input index order.
    pub terms: &'a [(usize, f64)],
}

/// The scalar is at most this affine function of the original inputs.
#[derive(Debug, Clone, PartialEq)]
pub struct BoxHullCut {
    /// Upper-rounded intercept covering every arm.
    pub offset: f64,
    /// Sparse coefficients in strictly increasing input index order.
    pub terms: Vec<(usize, f64)>,
}

#[repr(C)]
struct Axis {
    index: usize,
    left: f64,
    right: f64,
    slope: f64,
}

fn valid_arm(arm: AffineArm<'_>, point: &[f64]) -> bool {
    arm.offset.is_finite()
        && arm.terms.windows(2).all(|pair| pair[0].0 < pair[1].0)
        && arm
            .terms
            .iter()
            .all(|&(j, a)| a.is_finite() && point.get(j).is_some_and(|x| (-1.0..=1.0).contains(x)))
}

/// If the arm itself reaches the target, no plane covering it can be violated.
/// Invalid input returns `None`. An inconclusive enclosure falls through to separation.
fn arm_precludes_cut(arm: AffineArm<'_>, point: &[f64], value: f64) -> Option<bool> {
    if !arm.offset.is_finite() || !arm.terms.windows(2).all(|pair| pair[0].0 < pair[1].0) {
        return None;
    }
    let mut estimate = arm.offset;
    let mut magnitude = arm.offset.abs();
    for &(index, coefficient) in arm.terms {
        let x = *point.get(index)?;
        if !coefficient.is_finite() || !(-1.0..=1.0).contains(&x) {
            return None;
        }
        estimate += coefficient * x;
        magnitude += coefficient.abs();
    }
    // Let M = |offset| + sum |a_j| and e = EPSILON. A term in the dot product
    // sees at most n+1 roundings. For n <= 2^24, (1+e)^(n+1)-1 < 2(n+1)e.
    // Each of the 2n operations can also contribute MIN_POSITIVE of absolute
    // error, amplified by less than two. The nonnegative magnitude sum is
    // at least (1-e)^n M > M/2 (a subnormal sum of binary64s is exact).
    // The extra factor of two covers rounding while constructing the radius.
    // Keep the original path near overflow, where the magnitude may saturate.
    if arm.terms.len() > 1 << 24 || !estimate.is_finite() || magnitude >= f64::MAX / 2.0 {
        return Some(false);
    }
    let factor = 8.0 * (arm.terms.len() as f64 + 1.0);
    let radius = (factor * f64::EPSILON * magnitude + factor * f64::MIN_POSITIVE).next_up();
    Some((estimate - radius).next_down() >= value)
}

fn merged_axes(left: &[(usize, f64)], right: &[(usize, f64)]) -> Vec<Axis> {
    let mut left = left.iter().copied().peekable();
    let mut right = right.iter().copied().peekable();
    let mut axes = Vec::with_capacity(left.len().max(right.len()));
    while left.peek().is_some() || right.peek().is_some() {
        let ((index, a), b) = match (left.peek(), right.peek()) {
            (Some(&(i, a)), Some(&(j, b))) if i == j => {
                left.next();
                right.next();
                ((i, a), b)
            }
            (Some(&(i, a)), Some(&(j, _))) if i < j => {
                left.next();
                ((i, a), 0.0)
            }
            (Some(&(i, a)), None) => {
                left.next();
                ((i, a), 0.0)
            }
            (_, Some(&(j, b))) => {
                right.next();
                ((j, 0.0), b)
            }
            (None, None) => break,
        };
        axes.push(Axis {
            index,
            left: a,
            right: b,
            slope: a,
        });
    }
    axes
}

fn set_slope(a: &mut Axis, delta: f64, remaining: &mut f64) {
    let used = (*remaining).min(delta.abs());
    a.slope = if used == delta.abs() {
        a.right
    } else {
        a.left + used.copysign(delta)
    };
    *remaining -= used;
}

fn support_term(a: f64, slope: f64) -> f64 {
    match a.partial_cmp(&slope) {
        Some(Ordering::Equal) => 0.0,
        Some(Ordering::Greater) => sub_up(a, slope),
        _ => sub_up(slope, a),
    }
}

fn add_up(a: f64, b: f64) -> f64 {
    if b == 0.0 {
        a
    } else {
        (a + b).next_up()
    }
}

// Outward one-ulp arithmetic needs gradual underflow. A solver embedding AY
// can change this thread's floating-point mode between calls.
fn gradual_underflow() -> bool {
    let smallest_normal = std::hint::black_box(f64::MIN_POSITIVE);
    let half_normal = std::hint::black_box(f64::from_bits(1_u64 << 51));
    (smallest_normal * 0.5).to_bits() == half_normal.to_bits()
        && (half_normal * 2.0).to_bits() == f64::MIN_POSITIVE.to_bits()
}

/// Separate an upper facet at a candidate input and scalar value.
///
/// For arms `b_i + a_i·x`, every slope `s` gives a valid intercept
/// `max_i(b_i + ||a_i - s||_1)`. To minimize the plane at the given point,
/// the slope can stay coordinatewise between the two arm slopes. Equalizing
/// the two supports then gives a continuous knapsack problem with capacities
/// `|a_1j-a_0j|` and ordering keys `sign(a_1j-a_0j) * x_j`.
///
/// The separator uses floating point to select a slope, then independently
/// recomputes both supports with directed rounding. It returns `None` for
/// invalid data, overflow, or a point with no certified violation.
#[must_use]
pub fn separate_unit_box_hull(
    left: AffineArm<'_>,
    right: AffineArm<'_>,
    point: &[f64],
    value: f64,
) -> Option<BoxHullCut> {
    if !value.is_finite()
        || !gradual_underflow()
        || arm_precludes_cut(left, point, value)?
        || arm_precludes_cut(right, point, value)?
    {
        return None;
    }
    let mut axes = merged_axes(left.terms, right.terms);
    let mut total = 0.0;
    let mut order = Vec::with_capacity(axes.len());
    let mut box_face = true;
    for (slot, a) in axes.iter().enumerate() {
        let delta = a.right - a.left;
        if delta != 0.0 {
            total += delta.abs();
            let price = delta.signum() * point[a.index];
            box_face &= matches!(price.abs(), 0.0 | 1.0);
            order.push((price, slot, delta));
        }
    }
    // Halve before subtracting the offsets to avoid unnecessary overflow.
    let balance = right.offset * 0.5 - left.offset * 0.5 + total * 0.5;
    if !total.is_finite() || !balance.is_finite() {
        return None;
    }
    let mut remaining = balance.clamp(0.0, total);
    let by_price =
        |a: &(f64, usize, f64), b: &(f64, usize, f64)| a.0.total_cmp(&b.0).then(a.1.cmp(&b.1));
    // Only the fractional knapsack item's order statistic matters. Fully funded
    // partitions take the right slope; unfunded partitions retain the left.
    // Equal keys use slot order, just as in the sorted small-row case. Any
    // rounding at a partition boundary affects the proposal only: all arms
    // are independently enclosed below using the selected concrete slopes.
    if box_face && order.len() > 48 {
        // At a vertex of a priced box the keys occupy four total-order buckets.
        // Visit each in original slot order, including distinct signed zeros.
        for key in [-1.0_f64, -0.0, 0.0, 1.0] {
            for &(price, slot, delta) in &order {
                if remaining <= 0.0 {
                    break;
                }
                if price.to_bits() == key.to_bits() {
                    set_slope(&mut axes[slot], delta, &mut remaining);
                }
            }
        }
    } else {
        let mut pending = order.as_mut_slice();
        while remaining > 0.0 && pending.len() > 48 {
            let midpoint = pending.len() / 2;
            pending.select_nth_unstable_by(midpoint, by_price);
            let (cheaper, dearer) = pending.split_at_mut(midpoint);
            let capacity: f64 = cheaper.iter().map(|x| x.2.abs()).sum();
            if remaining < capacity {
                pending = cheaper;
            } else {
                for &(_, slot, _) in cheaper.iter() {
                    axes[slot].slope = axes[slot].right;
                }
                remaining -= capacity;
                pending = dearer;
            }
        }
        pending.sort_unstable_by(by_price);
        for &(_, slot, delta) in pending.iter() {
            if remaining <= 0.0 {
                break;
            }
            set_slope(&mut axes[slot], delta, &mut remaining);
        }
    }

    #[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
    if axes.len() >= 64 && is_x86_feature_detected!("avx512f") {
        return unsafe {
            directed::directed_support(&axes, point, left.offset, right.offset, value)
        };
    }
    let mut upper_left = left.offset;
    let mut upper_right = right.offset;
    let mut at_point = 0.0;
    let mut terms = Vec::with_capacity(axes.len());
    for a in axes {
        if !a.slope.is_finite() {
            return None;
        }
        upper_left = add_up(upper_left, support_term(a.left, a.slope));
        upper_right = add_up(upper_right, support_term(a.right, a.slope));
        if a.slope != 0.0 {
            terms.push((a.index, a.slope));
            at_point = add_up(at_point, mul_up(a.slope, point[a.index]));
        }
    }
    let offset = upper_left.max(upper_right);
    let upper = add_up(offset, at_point);
    (offset.is_finite() && upper.is_finite() && value > upper)
        .then_some(BoxHullCut { offset, terms })
}

#[cfg(test)]
mod tests;
