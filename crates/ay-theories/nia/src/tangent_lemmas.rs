//! Tangent plane helpers for NIA solver
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! Tangent plane constraints are applied in
//! `lib.rs::add_tangent_constraints_for_incorrect_monomials()`.
//! This module provides the mathematical helpers used by that check.
//!
//! For a monomial m = x*y at model point (a, b), the tangent plane is:
//!
//!   T(x,y) = a*y + b*x - a*b
//!
//! This provides a linear approximation:
//! - If a*b >= 0 (same signs): m >= T(x,y) (underestimate)
//! - If a*b <= 0 (opposite signs): m <= T(x,y) (overestimate)
//!
//! The lemma cuts off the current model if it violates the plane constraint.
//!
//! Based on Z3's `nla_tangent_lemmas.cpp`.

#[cfg(any(test, kani))]
use num_rational::BigRational;

/// Compute tangent plane value at point (a, b) for input (x, y)
///
/// T(x, y) = a*y + b*x - a*b
#[cfg(any(test, kani))]
pub(crate) fn tangent_plane(
    a: &BigRational,
    b: &BigRational,
    x: &BigRational,
    y: &BigRational,
) -> BigRational {
    a * y + b * x - a * b
}

/// Determine if the tangent plane gives an under or overestimate
///
/// At point (a, b):
/// - If (x-a) and (y-b) have same sign: underestimate (m >= T)
/// - If (x-a) and (y-b) have opposite signs: overestimate (m <= T)
#[cfg(any(test, kani))]
pub(crate) fn is_underestimate(
    a: &BigRational,
    b: &BigRational,
    x: &BigRational,
    y: &BigRational,
) -> bool {
    use num_traits::Signed;
    let dx = x - a;
    let dy = y - b;
    // Same sign check: positive product
    (dx.signum() * dy.signum()).is_positive()
}

#[cfg(test)]
#[path = "tangent_lemmas_tests.rs"]
mod tests;
