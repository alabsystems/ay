// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multiplication propagator: `result = x * y`, bounds reasoning.
//!
//! - `result` lies between the least and the greatest of the four corner
//!   products of `x`'s and `y`'s bounds (a bilinear function takes its
//!   extremes on a box at the corners);
//! - `x` lies between the corner quotients `result / y` (rounded inwards)
//!   when `y`'s bounds exclude 0; when they do not, but `result`'s exclude
//!   0, then `y != 0` in every solution and the same holds over `y`'s
//!   negative and positive parts; symmetrically for `y`.
//!
//! Every clause is an implication from the current bounds it reads (the
//! reasons) to a new bound, and holds in every solution over the root
//! domains: each derived interval contains every value the variable takes
//! in a solution whose other variables lie within those bounds. Once `x`
//! and `y` are fixed, `result` is narrowed to `x * y` exactly, so a complete
//! assignment that violates the constraint always ends in a conflict.
//!
//! Before 2026-11-19 the FlatZinc front end compiled `int_times` to a table
//! of every product and refused the model above 10,000 tuples (AY-OTHER-5).
//! The reasoning follows Gecode's `Int::Arithmetic::MultBnd` and Chuffed's
//! `times` propagator (sign cases, corner products).

use ay_sat::Literal;

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// `result = x * y`.
#[derive(Debug)]
pub struct Times {
    /// `[x, y, result]`.
    vars: [IntVarId; 3],
}

impl Times {
    /// Create `result = x * y`.
    pub fn new(x: IntVarId, y: IntVarId, result: IntVarId) -> Self {
        Self {
            vars: [x, y, result],
        }
    }
}

impl Propagator for Times {
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

        // result from x and y: the corner products.
        let products = [xb.0 * yb.0, xb.0 * yb.1, xb.1 * yb.0, xb.1 * yb.1];
        let lo = products.iter().copied().min().unwrap_or(0);
        let hi = products.iter().copied().max().unwrap_or(0);
        let Some(reasons) = reasons_of(trail, encoder, &[x, y]) else {
            return PropagationResult::NoChange;
        };
        out.tighten(trail, encoder, r, lo, hi, &reasons);

        // x from result and y, y from result and x.
        for (target, other, other_bounds) in [(x, y, yb), (y, x, xb)] {
            if let Some((lo, hi)) = quotient_hull(rb, other_bounds) {
                let Some(reasons) = reasons_of(trail, encoder, &[r, other]) else {
                    return PropagationResult::NoChange;
                };
                out.tighten(trail, encoder, target, lo, hi, &reasons);
            }
        }
        out.finish()
    }

    fn name(&self) -> &'static str {
        "times"
    }
}

/// Current bounds of `var`, widened to `i128` so that products and
/// quotients of two `i64` bounds cannot overflow.
pub(super) fn bounds(trail: &IntegerTrail, var: IntVarId) -> (i128, i128) {
    (i128::from(trail.lb(var)), i128::from(trail.ub(var)))
}

/// The bound literals `[v >= lb]` and `[v <= ub]` of each of `vars`;
/// `None` when one is not encoded (cannot happen for bounds inside the root
/// domain, which the dense order encoding covers).
pub(super) fn reasons_of(
    trail: &IntegerTrail,
    encoder: &IntegerEncoder,
    vars: &[IntVarId],
) -> Option<Vec<Literal>> {
    let mut reasons = Vec::with_capacity(2 * vars.len());
    for &var in vars {
        reasons.push(encoder.lookup_ge(var, trail.lb(var))?);
        reasons.push(encoder.lookup_le(var, trail.ub(var))?);
    }
    Some(reasons)
}

/// `floor(n / d)` for `d != 0`.
pub(super) fn floor_div(n: i128, d: i128) -> i128 {
    let q = n / d;
    if (n % d != 0) && ((n < 0) != (d < 0)) {
        q - 1
    } else {
        q
    }
}

/// `ceil(n / d)` for `d != 0`.
pub(super) fn ceil_div(n: i128, d: i128) -> i128 {
    let q = n / d;
    if (n % d != 0) && ((n < 0) == (d < 0)) {
        q + 1
    } else {
        q
    }
}

/// The parts of an interval without 0: its negative and its positive part.
pub(super) fn nonzero_parts((lo, hi): (i128, i128)) -> impl Iterator<Item = (i128, i128)> {
    [(lo, hi.min(-1)), (lo.max(1), hi)]
        .into_iter()
        .filter(|(lo, hi)| lo <= hi)
}

/// The integers `q` with `q * d = n` for some `n` in `num` and `d` in
/// `den`, as an interval: the corner quotients rounded inwards, over `den`'s
/// parts without 0. `None` when `den` and `num` both contain 0 (then `q` is
/// unconstrained: `q * 0 = 0`). An empty result is `(lo, hi)` with
/// `lo > hi`.
pub(super) fn quotient_hull(num: (i128, i128), den: (i128, i128)) -> Option<(i128, i128)> {
    let den_has_zero = den.0 <= 0 && 0 <= den.1;
    let num_has_zero = num.0 <= 0 && 0 <= num.1;
    if den_has_zero && num_has_zero {
        return None;
    }
    let mut hull: Option<(i128, i128)> = None;
    for (d_lo, d_hi) in nonzero_parts(den) {
        // n / d is monotone in n and in d over a box where d keeps its sign,
        // so its extremes are at the corners.
        let corners = [(num.0, d_lo), (num.0, d_hi), (num.1, d_lo), (num.1, d_hi)];
        let lo = corners
            .iter()
            .map(|&(n, d)| ceil_div(n, d))
            .min()
            .unwrap_or(0);
        let hi = corners
            .iter()
            .map(|&(n, d)| floor_div(n, d))
            .max()
            .unwrap_or(0);
        hull = Some(match hull {
            None => (lo, hi),
            Some((a, b)) => (a.min(lo), b.max(hi)),
        });
    }
    // `den` is exactly {0} and `num` excludes 0: no quotient at all.
    Some(hull.unwrap_or((1, 0)))
}

/// Clauses gathered by one propagation, or the conflict that ended it.
#[derive(Default)]
pub(super) struct Narrowing {
    clauses: Vec<Vec<Literal>>,
    conflict: Option<Vec<Literal>>,
}

impl Narrowing {
    /// `reasons` (true on the trail) imply `var` in `[lo, hi]`: narrow
    /// `var`'s bounds to it, or record a conflict when that leaves nothing.
    pub(super) fn tighten(
        &mut self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        var: IntVarId,
        lo: i128,
        hi: i128,
        reasons: &[Literal],
    ) {
        if self.conflict.is_some() {
            return;
        }
        let (lb, ub) = bounds(trail, var);
        if lo > hi || lo > ub || hi < lb {
            // Nothing in [lo, hi] (the reasons alone are contradictory), or
            // nothing in it within var's current bounds: the reasons and
            // var's own bound on the far side cannot both hold.
            let mut conflict = reasons.to_vec();
            if lo <= hi {
                let own = if lo > ub {
                    encoder.lookup_le(var, trail.ub(var))
                } else {
                    encoder.lookup_ge(var, trail.lb(var))
                };
                let Some(own) = own else {
                    return;
                };
                conflict.push(own);
            }
            self.conflict = Some(Explanation::new(conflict).into_conflict_clause());
            return;
        }
        // lb < lo <= ub and lb <= hi < ub fit in i64.
        if lo > lb {
            if let Some(conclusion) = i64::try_from(lo)
                .ok()
                .and_then(|lo| encoder.lookup_ge(var, lo))
            {
                self.clauses
                    .push(Explanation::new(reasons.to_vec()).into_clause(conclusion));
            }
        }
        if hi < ub {
            if let Some(conclusion) = i64::try_from(hi)
                .ok()
                .and_then(|hi| encoder.lookup_le(var, hi))
            {
                self.clauses
                    .push(Explanation::new(reasons.to_vec()).into_clause(conclusion));
            }
        }
    }

    /// The propagation result: the conflict if one was found, else the
    /// clauses.
    pub(super) fn finish(self) -> PropagationResult {
        if let Some(conflict) = self.conflict {
            PropagationResult::Conflict(conflict)
        } else if self.clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(self.clauses)
        }
    }
}

#[cfg(test)]
#[path = "times_tests.rs"]
mod tests;
