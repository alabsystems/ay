// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer division propagator: `result = x div y`, rounding towards zero
//! (FlatZinc `int_div`), `y != 0`; bounds reasoning.
//!
//! - `y != 0`: a bound of `y` at 0 moves past it;
//! - `result` lies between the least and the greatest corner quotient
//!   `x / y` over `y`'s negative and positive parts (`x / y` is monotone in
//!   each argument where `y` keeps its sign, and truncation is monotone);
//! - `x` lies in the hull of the values whose quotient by some `y` in
//!   bounds is some `result` in bounds. For `y >= 1`, `x div y = q` holds
//!   exactly for `x` in `[q*y, q*y + y - 1]` (`q > 0`), `[q*y - y + 1, q*y]`
//!   (`q < 0`) or `[-(y - 1), y - 1]` (`q = 0`); the low end grows with `q`
//!   and is linear in `y`, the high end too, so the hull is taken at
//!   `q = lb(result)`, `q = ub(result)` and the two ends of `y`'s part. A
//!   negative `y` is the positive case with `q` negated
//!   (`x div y = -(x div -y)`).
//!
//! `y` is not narrowed from `x` and `result`. Once `x` and `y` are fixed,
//! `result` is narrowed to `x div y` exactly, and `y = 0` is a conflict, so
//! a complete assignment that violates the constraint always ends in a
//! conflict. Every clause holds in every solution over the root domains for
//! the reason given with each rule.
//!
//! Before 2026-11-19 the FlatZinc front end compiled `int_div` to a table
//! and refused the model above 10,000 tuples (AY-OTHER-5).

use crate::encoder::IntegerEncoder;
use crate::propagator::{PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

use super::times::{bounds, nonzero_parts, reasons_of, Narrowing};

/// `result = x div y` (truncating), `y != 0`.
#[derive(Debug)]
pub struct Div {
    /// `[x, y, result]`.
    vars: [IntVarId; 3],
}

impl Div {
    /// Create `result = x div y`.
    pub fn new(x: IntVarId, y: IntVarId, result: IntVarId) -> Self {
        Self {
            vars: [x, y, result],
        }
    }
}

/// Least `x` with `x div y = q`, for `y >= 1`.
fn least_dividend(q: i128, y: i128) -> i128 {
    if q > 0 {
        q * y
    } else {
        q * y - (y - 1)
    }
}

/// Greatest `x` with `x div y = q`, for `y >= 1`.
fn greatest_dividend(q: i128, y: i128) -> i128 {
    if q < 0 {
        q * y
    } else {
        q * y + (y - 1)
    }
}

impl Propagator for Div {
    fn variables(&self) -> &[IntVarId] {
        &self.vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Linear
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        let [x, y, r] = self.vars;
        let mut out = Narrowing::default();
        let (xb, yb, rb) = (bounds(trail, x), bounds(trail, y), bounds(trail, r));

        // y != 0: [y >= 0] -> [y >= 1] and [y <= 0] -> [y <= -1] hold in
        // every solution. With y fixed at 0 the first is a conflict.
        if yb.0 == 0 {
            let Some(ge0) = encoder.lookup_ge(y, 0) else {
                return PropagationResult::NoChange;
            };
            out.tighten(trail, encoder, y, 1, i128::MAX, &[ge0]);
        } else if yb.1 == 0 {
            let Some(le0) = encoder.lookup_le(y, 0) else {
                return PropagationResult::NoChange;
            };
            out.tighten(trail, encoder, y, i128::MIN, -1, &[le0]);
        }
        let parts: Vec<(i128, i128)> = nonzero_parts(yb).collect();
        if parts.is_empty() {
            return out.finish();
        }

        // result from x and y.
        let mut hull: Option<(i128, i128)> = None;
        for &(y_lo, y_hi) in &parts {
            let corners = [xb.0 / y_lo, xb.0 / y_hi, xb.1 / y_lo, xb.1 / y_hi];
            let lo = corners.iter().copied().min().unwrap_or(0);
            let hi = corners.iter().copied().max().unwrap_or(0);
            hull = Some(hull.map_or((lo, hi), |(a, b)| (a.min(lo), b.max(hi))));
        }
        if let Some((lo, hi)) = hull {
            let Some(reasons) = reasons_of(trail, encoder, &[x, y]) else {
                return PropagationResult::NoChange;
            };
            out.tighten(trail, encoder, r, lo, hi, &reasons);
        }

        // x from result and y.
        let mut hull: Option<(i128, i128)> = None;
        for &(y_lo, y_hi) in &parts {
            // For y < 0, x div y = q iff x div (-y) = -q.
            let (q_lo, q_hi, d_lo, d_hi) = if y_lo > 0 {
                (rb.0, rb.1, y_lo, y_hi)
            } else {
                (-rb.1, -rb.0, -y_hi, -y_lo)
            };
            let lo = least_dividend(q_lo, d_lo).min(least_dividend(q_lo, d_hi));
            let hi = greatest_dividend(q_hi, d_lo).max(greatest_dividend(q_hi, d_hi));
            hull = Some(hull.map_or((lo, hi), |(a, b)| (a.min(lo), b.max(hi))));
        }
        if let Some((lo, hi)) = hull {
            let Some(reasons) = reasons_of(trail, encoder, &[r, y]) else {
                return PropagationResult::NoChange;
            };
            out.tighten(trail, encoder, x, lo, hi, &reasons);
        }
        out.finish()
    }

    fn name(&self) -> &'static str {
        "div"
    }
}

#[cfg(test)]
#[path = "div_tests.rs"]
mod tests;
