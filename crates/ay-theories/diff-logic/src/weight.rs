//! Weight abstraction for difference-logic edge weights.
//!
//! Difference logic constraints have the shape `x - y <= c`, where `c` is drawn
//! from a totally ordered abelian group. For QF_IDL the weights are integers
//! (`i64` for the fast path, [`num_bigint::BigInt`] for the unbounded path); for
//! QF_RDL they are rationals ([`num_rational::BigRational`]).
//!
//! The [`Weight`] trait captures exactly the operations the difference-logic
//! engine needs: addition (to accumulate path lengths), comparison (to detect a
//! shorter path / a negative cycle), a zero element (the super-source distance),
//! and — for the strict-`<` translation over integers — an "epsilon" predecessor
//! that turns `x - y < c` into `x - y <= c'` for the largest `c' < c`.
//!
//! Rationals are dense, so there is no integral predecessor; strict rational
//! constraints are handled separately (see [`crate::atom`]) and `strict_pred`
//! is intentionally absent from the rational path.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// Edge weight in a difference-logic graph: a totally ordered abelian group.
pub trait Weight: Clone + Ord + std::fmt::Debug {
    /// The additive identity (used as the super-source distance and the
    /// running cycle sum).
    fn zero() -> Self;

    /// `self + other`. Must be associative/commutative; overflow is a bug in the
    /// caller's domain choice (use `BigInt`/`BigRational` if `i64` can overflow).
    fn add(&self, other: &Self) -> Self;

    /// `self < other`.
    fn lt(&self, other: &Self) -> bool {
        self < other
    }
}

/// Integer weights whose constraints support strict-to-non-strict rewriting.
///
/// Over the integers, `x - y < c` is equivalent to `x - y <= c - 1`. Types that
/// implement this trait expose that predecessor so the atom translator can keep
/// the graph in pure `<=` form.
pub trait IntWeight: Weight {
    /// The largest value strictly less than `self` (i.e. `self - 1`).
    fn strict_pred(&self) -> Self;
}

impl Weight for i64 {
    #[inline]
    fn zero() -> Self {
        0
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        // Saturating add would silently corrupt soundness; callers that risk
        // i64 overflow must use BigInt. We use checked_add + expect so an
        // overflow surfaces loudly rather than wrapping into a wrong answer.
        self.checked_add(*other)
            .expect("i64 difference-logic weight overflow; use BigInt for unbounded ranges")
    }
}

impl IntWeight for i64 {
    #[inline]
    fn strict_pred(&self) -> Self {
        self.checked_sub(1)
            .expect("i64 difference-logic weight underflow; use BigInt for unbounded ranges")
    }
}

impl Weight for BigInt {
    #[inline]
    fn zero() -> Self {
        <Self as Zero>::zero()
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        self + other
    }
}

impl IntWeight for BigInt {
    #[inline]
    fn strict_pred(&self) -> Self {
        self - <Self as One>::one()
    }
}

impl Weight for BigRational {
    #[inline]
    fn zero() -> Self {
        <Self as Zero>::zero()
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        self + other
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::FromPrimitive;

    #[test]
    fn i64_group_laws() {
        assert_eq!(<i64 as Weight>::zero(), 0);
        assert_eq!(Weight::add(&3i64, &4), 7);
        assert!(Weight::lt(&(-1i64), &0));
        assert_eq!(IntWeight::strict_pred(&5i64), 4);
    }

    #[test]
    fn bigint_group_laws() {
        let a = BigInt::from(10);
        let b = BigInt::from(-3);
        assert_eq!(Weight::add(&a, &b), BigInt::from(7));
        assert_eq!(IntWeight::strict_pred(&a), BigInt::from(9));
        assert_eq!(<BigInt as Weight>::zero(), BigInt::from(0));
    }

    #[test]
    fn rational_group_laws() {
        let a = BigRational::from_f64(0.5).unwrap();
        let b = BigRational::from_f64(0.25).unwrap();
        assert_eq!(Weight::add(&a, &b), BigRational::from_f64(0.75).unwrap());
        assert!(Weight::lt(&<BigRational as Weight>::zero(), &a));
    }
}
