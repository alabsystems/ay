// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCALED chord mode (#nra-joint-refinement, `z = v/w`).
//!
//! The plan's residual curve is not always a conic in the pair it moves.
//! `skoSS² + skoX² = 1` with `skoX := 1 − skoSM²` eliminated
//! (`sqrt-problem-13-sqrt1`) leaves the QUARTIC `skoSS² − 2·skoSM² + skoSM⁴ =
//! 0`: a line through a rational point of it meets it up to four times, so
//! the plain chord sweep's quadratic fit declines. The change of variables
//! `skoSS = z·skoSM` divides out `skoSM²` and leaves the circle
//! `z² + skoSM² = 2`, whose rational points are dense: `(1, 1)` seeds it, and
//! the chord of every rational slope through the seed meets it again in a
//! rational `(z, w)`, installed as `(z·w, w)`.
//!
//! Both orientations are tried — the algebraic value scaled by the partner
//! (`α = z·β`) and the partner scaled by the algebraic value (`β = z·α`) —
//! because which of the pair the NRA lane leaves algebraic is not fixed.
//! The scaled residual `R(z, w) = residual(α, β) / w²` is only ever evaluated
//! at `w ≠ 0`; a sample that would divide by zero declines.
//!
//! Candidate generation ONLY, like the rest of the joint pass: every proposal
//! goes through `try_joint_assignment` — exact residual pre-check of the
//! ORIGINAL equality, declared-sort gate, bit cap and the parent's exact
//! whole-model re-check — and a declined proposal leaves the algebraic model
//! bit-for-bit intact. The quadratic fit is a budget filter, not a proof.

use ay_core::TermId;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::math::{quadratic_fit, rat, rational_roots, seed_values};
use super::{
    narrow, rational_bits, simplest_rational_in_open, Plan, RefineVar, MAX_JOINT_CANDIDATE_BITS,
    MAX_JOINT_ROUNDS, MAX_SEPARATION_ROUNDS, MAX_SIMPLEST_STEPS,
};
use crate::executor::Executor;

/// Which member of the moved pair carries the scale factor `z`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Scale {
    /// `α = z·w` with `w = β`: the algebraic value is scaled by the partner.
    Alpha,
    /// `β = z·w` with `w = α`: the partner is scaled by the algebraic value.
    Partner,
}

impl Scale {
    /// The `(α, β)` pair the scaled point `(z, w)` stands for.
    pub(super) fn unscale(self, z: &BigRational, w: &BigRational) -> (BigRational, BigRational) {
        match self {
            Scale::Alpha => (z * w, w.clone()),
            Scale::Partner => (w.clone(), z * w),
        }
    }
}

/// `(min, max)` of two rationals.
fn ordered(a: BigRational, b: BigRational) -> (BigRational, BigRational) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

/// Enclosures `([z_lo, z_hi], [w_lo, w_hi])` of the model point in scaled
/// coordinates, from the algebraic value's interval `(lo, hi)` and the
/// partner's exact value `b`. `None` at `b = 0`, and while `(lo, hi)` still
/// reaches 0 in the `Partner` orientation — `z = b/α` needs `α`'s sign.
pub(super) fn model_enclosure(
    scale: Scale,
    lo: &BigRational,
    hi: &BigRational,
    b: &BigRational,
) -> Option<((BigRational, BigRational), (BigRational, BigRational))> {
    if b.is_zero() {
        return None;
    }
    match scale {
        Scale::Alpha => Some((ordered(lo / b, hi / b), (b.clone(), b.clone()))),
        Scale::Partner => {
            // `b/x` is monotone on an interval of constant sign; both
            // endpoints must be nonzero to be divided by.
            if !(lo.is_positive() || hi.is_negative()) {
                return None;
            }
            Some((ordered(b / hi, b / lo), (lo.clone(), hi.clone())))
        }
    }
}

/// Enclosure `(t_lo, t_hi)` of the chord slope `(w̄ − w₀) / (z̄ − z₀)` from
/// the seed `(z₀, w₀)` to the model point. Interval division over a box whose
/// denominator excludes 0 is monotone in each coordinate, so the corners
/// bound it. `None` while the `z` enclosure still contains `z₀`.
pub(super) fn slope_enclosure(
    scale: Scale,
    lo: &BigRational,
    hi: &BigRational,
    b: &BigRational,
    seed: (&BigRational, &BigRational),
) -> Option<(BigRational, BigRational)> {
    let ((z_lo, z_hi), (w_lo, w_hi)) = model_enclosure(scale, lo, hi, b)?;
    let (z0, w0) = seed;
    if &z_lo <= z0 && &z_hi >= z0 {
        return None;
    }
    let (d_lo, d_hi) = (z_lo - z0, z_hi - z0);
    let (n_lo, n_hi) = (w_lo - w0, w_hi - w0);
    let corners = [&n_lo / &d_lo, &n_lo / &d_hi, &n_hi / &d_lo, &n_hi / &d_hi];
    let t_lo = corners.iter().min()?.clone();
    let t_hi = corners.iter().max()?.clone();
    Some((t_lo, t_hi))
}

impl Executor {
    /// The SCALED sweep over the partners the plain chord sweep declined on,
    /// in both orientations. `true` means a proposal passed the exact
    /// whole-model gate and IS the model; on `false` nothing was installed.
    pub(super) fn joint_scaled_chords(
        &mut self,
        plan: &Plan,
        state: &mut [RefineVar],
        partners: &[TermId],
    ) -> bool {
        for &beta in partners {
            for scale in [Scale::Alpha, Scale::Partner] {
                if self.poll_evaluation_stop().is_err() {
                    return false;
                }
                // Start from the fresh isolating interval: the plain sweep's
                // narrowing would only inflate the chord denominators.
                let Some(var) = state.first_mut() else {
                    return false;
                };
                if var.exact.is_some() {
                    return false;
                }
                let (lo, hi) = var.alpha.interval();
                (var.lo, var.hi) = (lo.clone(), hi.clone());
                if self.scaled_chord_rounds(plan, state, beta, scale) {
                    return true;
                }
            }
        }
        false
    }

    /// One orientation for one partner: seed, separate, sweep.
    fn scaled_chord_rounds(
        &mut self,
        plan: &Plan,
        state: &mut [RefineVar],
        beta: TermId,
        scale: Scale,
    ) -> bool {
        let Some(b) = plan.values.get(&beta).cloned() else {
            return false;
        };
        if b.is_zero() {
            return false;
        }
        let Some((z0, w0)) = self.scaled_seed(plan, beta, scale) else {
            return false;
        };
        // A horizontal chord (`w̄ = w₀`) on a genuine conic would make the
        // model point rational too; nothing to sweep.
        if scale == Scale::Alpha && b == w0 {
            return false;
        }
        let enclosure = |state: &[RefineVar]| {
            slope_enclosure(scale, &state[0].lo, &state[0].hi, &b, (&z0, &w0))
        };
        for _ in 0..MAX_SEPARATION_ROUNDS {
            if enclosure(state).is_some() || !narrow(state) {
                break;
            }
        }
        let mut last: Option<BigRational> = None;
        for round in 0..MAX_JOINT_ROUNDS {
            if self.poll_evaluation_stop().is_err() {
                return false;
            }
            if round > 0 && !narrow(state) {
                return false;
            }
            let Some((t_lo, t_hi)) = enclosure(state) else {
                continue;
            };
            let Some(t) = simplest_rational_in_open(&t_lo, &t_hi, MAX_SIMPLEST_STEPS) else {
                continue;
            };
            if last.as_ref() == Some(&t) {
                continue;
            }
            last = Some(t.clone());
            let Some((a, bb)) = self.scaled_second_point(plan, beta, scale, (&z0, &w0), &t) else {
                continue;
            };
            if self.try_joint_assignment(plan, Some(beta), &a, Some(&bb)) {
                return true;
            }
        }
        false
    }

    /// The scaled residual `residual(α, β) / w²` at the scaled point
    /// `(z, w)`; `None` at `w = 0` (fail closed, never divide by zero).
    fn scaled_residual(
        &mut self,
        plan: &Plan,
        beta: TermId,
        scale: Scale,
        z: &BigRational,
        w: &BigRational,
    ) -> Option<BigRational> {
        if w.is_zero() {
            return None;
        }
        let (a, b) = scale.unscale(z, w);
        let residual = self.residual_at(plan, Some(beta), &a, Some(&b))?;
        Some(residual / (w * w))
    }

    /// A rational point `(z, w)` on the scaled curve: fix `w` at a simple
    /// nonzero rational and solve the quadratic in `z` exactly. Every returned
    /// point is confirmed by an exact evaluation of the ORIGINAL residual.
    fn scaled_seed(
        &mut self,
        plan: &Plan,
        beta: TermId,
        scale: Scale,
    ) -> Option<(BigRational, BigRational)> {
        let model_values: Vec<BigRational> = plan.values.values().cloned().collect();
        for w in seed_values(&model_values) {
            if w.is_zero() {
                continue;
            }
            let mut at = Vec::with_capacity(4);
            for z in [0, 1, -1, 2] {
                at.push(self.scaled_residual(plan, beta, scale, &rat(z), &w));
            }
            let [Some(at0), Some(at1), Some(at_m1), Some(at2)] = &at[..] else {
                continue;
            };
            let Some((c0, c1, c2)) = quadratic_fit(at0, at1, at_m1, at2) else {
                continue;
            };
            for z in rational_roots(&c0, &c1, &c2) {
                if rational_bits(&z) > MAX_JOINT_CANDIDATE_BITS {
                    continue;
                }
                let (a, b) = scale.unscale(&z, &w);
                if let Some(residual) = self.residual_at(plan, Some(beta), &a, Some(&b)) {
                    if residual.is_zero() {
                        return Some((z, w));
                    }
                }
            }
        }
        None
    }

    /// The second intersection of the scaled curve with the line of slope `t`
    /// through the seed, returned UNSCALED as `(α, β)`. Rational whenever the
    /// scaled restriction is a genuine quadratic — confirmed on four samples
    /// here, and exactly by the caller's acceptance gate.
    fn scaled_second_point(
        &mut self,
        plan: &Plan,
        beta: TermId,
        scale: Scale,
        seed: (&BigRational, &BigRational),
        t: &BigRational,
    ) -> Option<(BigRational, BigRational)> {
        let (z0, w0) = seed;
        let mut at = Vec::with_capacity(4);
        for lambda in [0, 1, -1, 2] {
            let l = rat(lambda);
            let (z, w) = (z0 + &l, w0 + t * &l);
            at.push(self.scaled_residual(plan, beta, scale, &z, &w)?);
        }
        let (c0, c1, c2) = quadratic_fit(&at[0], &at[1], &at[2], &at[3])?;
        // The seed must be ON the curve, and the line must meet it twice.
        if !c0.is_zero() || c2.is_zero() {
            return None;
        }
        let lambda = -c1 / c2;
        if lambda.is_zero() {
            return None;
        }
        let (z, w) = (z0 + &lambda, w0 + t * &lambda);
        if w.is_zero() {
            return None;
        }
        Some(scale.unscale(&z, &w))
    }
}

#[cfg(test)]
mod tests;
