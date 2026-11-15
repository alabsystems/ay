// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `IStar` — the fast lane for [`RStar`](crate::rstar::RStar).
//!
//! `RStar` stores its rational part as a [`num_rational::BigRational`], so every
//! addition and comparison in the engine's inner loop allocates on the heap. In
//! difference logic that inner loop is the whole cost: a Dijkstra over slacks
//! computes `π(from) + w − π(to)` for every edge it scans.
//!
//! Real QF_RDL benchmarks do not need that generality. Across the SMT-LIB
//! QF_RDL division every constant is a small integer (`0`, `5`, `14`, …) — the
//! rationals never actually appear. `IStar` is the same `ℚ[ε]` group with the
//! rational part narrowed to `i128`, so the arithmetic stays in registers.
//!
//! Semantics are identical to `RStar`: an element is `q + eps·ε` ordered
//! lexicographically (`q` first, then `eps`), added component-wise, with `ε > 0`
//! smaller than every positive rational. `x − y < c` is `x − y <= c − ε`, i.e.
//! weight `(c, -1)`; a non-strict bound has `eps = 0`. A cycle is negative iff
//! its sum is `< (0, 0)` — either the integer part is negative, or it is zero
//! and the ε-count is negative, which is the case where strict bounds alone
//! force `0 < 0`.
//!
//! # Overflow is a hard error, never a wrong answer
//!
//! Saturating or wrapping here would silently corrupt the order relation and
//! could turn an infeasible system into a "feasible" one — the worst failure a
//! solver has. So both components use checked arithmetic and panic on overflow,
//! and the caller is expected to select this lane only after confirming the
//! problem's constants are integral and small (see
//! [`IStar::fits_fast_lane`]). With every `|c| <= 2^62` and simple paths of at
//! most `|V|` edges, an `i128` accumulator cannot overflow for any realistic
//! graph, so the panic is unreachable in the selected regime rather than a
//! latent crash.

use num_rational::BigRational;
use num_traits::{One, ToPrimitive};

use crate::atom::Negate;
use crate::weight::Weight;

/// Largest magnitude a constant may have to be admitted to the fast lane.
///
/// Chosen so that summing `|V|` of them cannot overflow the `i128`
/// accumulator: `2^62 * 2^30 = 2^92 < 2^127`, leaving ample headroom for graphs
/// far larger than any SMT-LIB instance.
pub const FAST_LANE_LIMIT: i128 = 1i128 << 62;

/// A value in `ℤ[ε]` ordered lexicographically: `(integer, ε-coefficient)`.
///
/// The fast-arithmetic counterpart of [`crate::rstar::RStar`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct IStar {
    /// The integral part.
    pub q: i128,
    /// The infinitesimal coefficient; `ε` is positive.
    pub eps: i64,
}

impl IStar {
    /// `q + eps·ε`.
    pub const fn new(q: i128, eps: i64) -> Self {
        Self { q, eps }
    }

    /// A finite (no-ε) integral value.
    pub const fn finite(q: i128) -> Self {
        Self { q, eps: 0 }
    }

    /// Can this rational be represented exactly, and safely, in the fast lane?
    ///
    /// Requires an integral value (denominator 1) whose magnitude is within
    /// [`FAST_LANE_LIMIT`]. Anything else — a genuine fraction, or a constant so
    /// large that path sums could approach the `i128` bound — must use the exact
    /// [`RStar`](crate::rstar::RStar) lane instead.
    pub fn fits_fast_lane(q: &BigRational) -> Option<i128> {
        if !q.denom().is_one() {
            return None;
        }
        let n = q.numer().to_i128()?;
        // `unsigned_abs`, not `abs`: `i128::MIN` has no positive i128 and is
        // rejected here like every other giant.
        if n.unsigned_abs() >= FAST_LANE_LIMIT.unsigned_abs() {
            return None;
        }
        Some(n)
    }

    /// Realize as a rational by substituting `ε := delta`.
    pub fn realize_with(&self, delta: &BigRational) -> BigRational {
        BigRational::from_integer(self.q.into())
            + BigRational::from_integer(self.eps.into()) * delta
    }
}

impl Weight for IStar {
    #[inline]
    fn zero() -> Self {
        Self { q: 0, eps: 0 }
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        Self {
            q: self
                .q
                .checked_add(other.q)
                .expect("IStar integer overflow; the fast lane admits only |c| < 2^62"),
            eps: self
                .eps
                .checked_add(other.eps)
                .expect("IStar epsilon-count overflow (i64)"),
        }
    }
}

impl Negate for IStar {
    #[inline]
    fn negate(&self) -> Option<Self> {
        // Neither `i128::MIN` nor an ε-count of `i64::MIN` has a negation in
        // its width; refuse rather than wrap (sign flip) or saturate (off by
        // one).
        Some(Self {
            q: self.q.checked_neg()?,
            eps: self.eps.checked_neg()?,
        })
    }

    #[inline]
    fn can_negate(&self) -> bool {
        self.q != i128::MIN && self.eps != i64::MIN
    }
}

/// Choose a positive `δ` realizing the ε-parts of a set of slacks, mirroring
/// [`crate::rstar::pick_delta_from_slacks`] for the integral lane.
///
/// A slack `(g, k)` with `g > 0` and `k < 0` requires `δ < g / (-k)` for the
/// realized value to stay non-negative; the result is half the tightest such
/// bound, or `1` when no slack constrains it.
pub fn pick_delta_from_slacks(slacks: &[(i128, i64)]) -> BigRational {
    let mut bound: Option<BigRational> = None;
    for &(g, k) in slacks {
        if g > 0 && k < 0 {
            // `-k` as `unsigned_abs` (equal for `k < 0`): `i64::MIN` has no
            // positive i64.
            let limit = BigRational::from_integer(g.into())
                / BigRational::from_integer(k.unsigned_abs().into());
            // Keep the tighter (smaller) bound.
            if bound.as_ref().is_none_or(|b| limit < *b) {
                bound = Some(limit);
            }
        }
    }
    if let Some(b) = bound {
        b / BigRational::from_integer(2.into())
    } else {
        BigRational::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordering_is_lexicographic_with_epsilon_as_tiebreak() {
        // The property the whole strict-inequality encoding rests on.
        assert!(IStar::new(0, -1) < IStar::new(0, 0));
        assert!(IStar::new(0, 0) < IStar::new(0, 1));
        assert!(IStar::new(-1, 5) < IStar::new(0, -5));
        assert_eq!(IStar::new(3, -2), IStar::new(3, -2));
    }

    #[test]
    fn a_zero_sum_cycle_of_strict_bounds_is_negative() {
        // x < y and y < x: integer parts cancel, two ε's decide it.
        let sum = IStar::new(0, -1).add(&IStar::new(0, -1));
        assert_eq!(sum, IStar::new(0, -2));
        assert!(sum < <IStar as Weight>::zero());
    }

    #[test]
    fn non_strict_zero_cycle_is_not_negative() {
        let sum = IStar::finite(0).add(&IStar::finite(0));
        assert!(sum >= <IStar as Weight>::zero());
    }

    #[test]
    fn fast_lane_admits_integers_and_rejects_fractions_and_giants() {
        let int = BigRational::from_integer(14.into());
        assert_eq!(IStar::fits_fast_lane(&int), Some(14));

        let half = BigRational::new(1.into(), 2.into());
        assert_eq!(
            IStar::fits_fast_lane(&half),
            None,
            "a genuine fraction must fall back to the exact lane"
        );

        let giant = BigRational::from_integer(num_bigint::BigInt::from(1) << 100);
        assert_eq!(
            IStar::fits_fast_lane(&giant),
            None,
            "a constant near the accumulator bound must fall back"
        );
    }

    #[test]
    fn fast_lane_rejects_the_most_negative_i128() {
        // `i128::MIN.abs()` overflowed; it is a giant like any other.
        let min = BigRational::from_integer(i128::MIN.into());
        assert_eq!(IStar::fits_fast_lane(&min), None);
        let edge = BigRational::from_integer((-FAST_LANE_LIMIT).into());
        assert_eq!(IStar::fits_fast_lane(&edge), None);
        let inside = BigRational::from_integer((1 - FAST_LANE_LIMIT).into());
        assert_eq!(IStar::fits_fast_lane(&inside), Some(1 - FAST_LANE_LIMIT));
    }

    #[test]
    fn pick_delta_accepts_the_most_negative_eps_count() {
        // `-k` overflowed for `k = i64::MIN`; the bound is g / 2^63.
        let d = pick_delta_from_slacks(&[(1, i64::MIN), (1, -1)]);
        let two_pow_63 = BigRational::from_integer(num_bigint::BigInt::from(1u64 << 63));
        assert_eq!(d, BigRational::new(1.into(), 2.into()) / two_pow_63);
    }

    #[test]
    fn negate_round_trips() -> Result<(), String> {
        let v = IStar::new(7, -1);
        let neg = v.negate().ok_or("IStar(7, -1) must negate")?;
        let back = neg.negate().ok_or("IStar(-7, 1) must negate")?;
        if back != v {
            return Err(format!("double negation of {v:?} gave {back:?}"));
        }
        let sum = v.add(&neg);
        if sum != <IStar as Weight>::zero() {
            return Err(format!("{v:?} + -{v:?} gave {sum:?}, not zero"));
        }
        Ok(())
    }

    #[test]
    fn negate_refuses_the_unrepresentable_parts() -> Result<(), String> {
        // `-i128::MIN` and `-i64::MIN` have no value in their width: `None`,
        // never a wrapped (sign-flipped) or saturated (off-by-one) weight.
        for w in [IStar::new(i128::MIN, 0), IStar::new(0, i64::MIN)] {
            if let Some(n) = w.negate() {
                return Err(format!("{w:?} negated to {n:?}; expected None"));
            }
            if w.can_negate() {
                return Err(format!("{w:?} claims to be negatable"));
            }
        }
        let edge = IStar::new(i128::MIN + 1, i64::MIN + 1);
        if !edge.can_negate() {
            return Err(format!("{edge:?} claims to be unnegatable"));
        }
        let want = IStar::new(i128::MAX, i64::MAX);
        match edge.negate() {
            Some(n) if n == want => Ok(()),
            got => Err(format!("{edge:?} negated to {got:?}; expected {want:?}")),
        }
    }
}
