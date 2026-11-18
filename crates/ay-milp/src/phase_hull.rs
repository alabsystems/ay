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

fn merged_axes(left: &[(usize, f64)], right: &[(usize, f64)]) -> Vec<Axis> {
    let mut left = left.iter().copied().peekable();
    let mut right = right.iter().copied().peekable();
    let mut axes = Vec::new();
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
        || !valid_arm(left, point)
        || !valid_arm(right, point)
    {
        return None;
    }
    let mut axes = merged_axes(left.terms, right.terms);
    let mut total = 0.0;
    let mut order = Vec::with_capacity(axes.len());
    for (slot, a) in axes.iter().enumerate() {
        let delta = a.right - a.left;
        if delta != 0.0 {
            total += delta.abs();
            order.push((delta.signum() * point[a.index], slot, delta));
        }
    }
    // Halve before subtracting the offsets to avoid unnecessary overflow.
    let balance = right.offset * 0.5 - left.offset * 0.5 + total * 0.5;
    if !total.is_finite() || !balance.is_finite() {
        return None;
    }
    let mut remaining = balance.clamp(0.0, total);
    order.sort_unstable_by(|a, b| a.0.total_cmp(&b.0).then(a.1.cmp(&b.1)));
    for (_, slot, delta) in order {
        if remaining <= 0.0 {
            break;
        }
        let used = remaining.min(delta.abs());
        let a = &mut axes[slot];
        a.slope = if used == delta.abs() {
            a.right
        } else {
            a.left + used.copysign(delta)
        };
        remaining -= used;
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
