// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public façade over the exact real-algebraic engine (`algebraic.rs` +
//! `univariate.rs`) for the RCF / algebraic-number C-API in `ay-ffi`.
//!
//! Everything the FFI needs beyond the already-`pub` [`RealScalar`] /
//! [`crate::RealAlgebraic`] / [`crate::RealAlgebraicValue`] API is exposed here
//! as thin wrappers over `pub(crate)` engine internals: real-root isolation, the
//! fail-closed isolating-interval constructor, exact polynomial sign, k-th
//! roots, and the Thom derivative-tower sign encoding. No new mathematics — only
//! visibility.
//!
//! Every function keeps the engine's fail-closed contract: it returns `None` on
//! a refinement cap or an unrepresentable request, and NEVER a wrong value, so
//! the FFI can map `None` to `Z3_EXCEPTION` without ever fabricating an
//! algebraic number, sign, or ordering.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::algebraic::{RealAlgebraic, RealScalar};
use crate::univariate::{isolate_roots, square_free_part, RootMarker, UniPoly};

/// The exact scalar `0`.
fn rat_zero() -> RealScalar {
    RealScalar::Rational(BigRational::zero())
}

/// Exact sign (`-1` / `0` / `+1`) of a scalar, or `None` on a refinement cap.
/// A `0` is only ever returned via the engine's GCD-certified zero test.
pub fn sign(s: &RealScalar) -> Option<i32> {
    Some(match s.cmp_exact(&rat_zero())? {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    })
}

/// Canonicalize a scalar: an algebraic value is reduced to identity-residue
/// form over its canonical defining polynomial (or collapses to a rational when
/// the value is actually rational); a rational is returned unchanged. `None`
/// only on a refinement cap. Producing every stored scalar through this makes
/// the classification / introspection surface exact and total.
pub fn canonicalize(s: &RealScalar) -> Option<RealScalar> {
    match s {
        RealScalar::Rational(r) => Some(RealScalar::Rational(r.clone())),
        // Canonicalization is an explicit introspection boundary, so it may
        // spend the bounded rational-root certificate that arithmetic inner
        // loops intentionally avoid.
        RealScalar::Algebraic(v) => v.to_number_for_output(),
    }
}

/// `true` iff the (canonicalized) scalar is rational. `None` on a refinement cap.
pub fn is_rational(s: &RealScalar) -> Option<bool> {
    Some(matches!(canonicalize(s)?, RealScalar::Rational(_)))
}

/// The rational value of `s` as `(numerator, denominator)` with a positive
/// denominator, when `s` is rational; `None` when it is a genuine irrational
/// algebraic (or on a refinement cap).
pub fn as_rational(s: &RealScalar) -> Option<(BigInt, BigInt)> {
    match canonicalize(s)? {
        RealScalar::Rational(r) => Some((r.numer().clone(), r.denom().clone())),
        RealScalar::Algebraic(_) => None,
    }
}

/// Integer coefficients (low-to-high) of a defining polynomial of `s`: the
/// square-free integer defining polynomial for a genuine algebraic value, or
/// `den*x - num` (coefficients `[-num, den]`) for a rational. `None` on a
/// refinement cap.
pub fn defining_coeffs(s: &RealScalar) -> Option<Vec<BigInt>> {
    match canonicalize(s)? {
        RealScalar::Rational(r) => Some(vec![-r.numer().clone(), r.denom().clone()]),
        RealScalar::Algebraic(v) => Some(v.alpha().poly_coeffs()),
    }
}

/// 1-based root index of `s` among the ascending real roots of its defining
/// polynomial. A rational is the unique root of `den*x - num`, so its index is
/// `1`. `None` on a refinement cap.
pub fn root_index(s: &RealScalar) -> Option<usize> {
    match canonicalize(s)? {
        RealScalar::Rational(_) => Some(1),
        RealScalar::Algebraic(v) => Some(v.alpha().root_index()),
    }
}

/// Open isolating interval `(lo, hi)` of a genuine algebraic value; `None` for a
/// rational (a point, not an interval) or on a refinement cap.
pub fn interval(s: &RealScalar) -> Option<(BigRational, BigRational)> {
    match canonicalize(s)? {
        RealScalar::Rational(_) => None,
        RealScalar::Algebraic(v) => {
            let (lo, hi) = v.alpha().interval();
            Some((lo.clone(), hi.clone()))
        }
    }
}

/// z3 `root-obj` rendering of a genuine algebraic value (e.g.
/// `(root-obj (+ (^ x 2) (- 2)) 2)` for √2); `None` for a rational (render it
/// as a fraction instead) or on a refinement cap.
pub fn root_obj_string(s: &RealScalar) -> Option<String> {
    match canonicalize(s)? {
        RealScalar::Rational(_) => None,
        RealScalar::Algebraic(v) => Some(v.alpha().to_smtlib()),
    }
}

/// Real roots (ascending) of the univariate polynomial with rational
/// coefficients `coeffs` (low-to-high), as exact scalars. `None` on a
/// refinement cap; the zero polynomial is rejected (infinitely many roots).
pub fn real_roots(coeffs: &[BigRational]) -> Option<Vec<RealScalar>> {
    let p = UniPoly::from_coeffs(coeffs.to_vec());
    if p.is_zero() {
        return None;
    }
    let sf = square_free_part(&p)?;
    if sf.degree().unwrap_or(0) < 1 {
        return Some(Vec::new()); // non-zero constant: no real roots
    }
    let markers = isolate_roots(&sf)?;
    let mut out = Vec::with_capacity(markers.len());
    for mk in markers {
        match mk {
            RootMarker::Rational(r) => out.push(RealScalar::Rational(r)),
            RootMarker::Interval(lo, hi) => {
                let alg = RealAlgebraic::from_isolating_interval(&sf, &lo, &hi)?;
                out.push(RealScalar::Algebraic(alg.as_value()));
            }
        }
    }
    Some(out)
}

/// The real k-th root `a^(1/k)`:
///
/// * `k == 0` → `None` (undefined);
/// * `k == 1` → `a`;
/// * even `k` with `a < 0` → `None` (no real root);
/// * otherwise the unique real root with the sign of `a` (the non-negative root
///   for even `k`, `a > 0`; the unique real root for odd `k`).
///
/// `None` on a refinement cap. `a^(1/k)` is a root of `q(x^k)` where `q` is a
/// defining polynomial of `a`; the correct branch is selected by verifying
/// `root^k == a` exactly.
pub fn nth_root(a: &RealScalar, k: u32) -> Option<RealScalar> {
    if k == 0 {
        return None;
    }
    if k == 1 {
        return Some(a.clone());
    }
    let sa = sign(a)?;
    if sa == 0 {
        return Some(rat_zero());
    }
    if sa < 0 && k.is_multiple_of(2) {
        return None;
    }
    let q = defining_coeffs(a)?;
    let k = k as usize;
    // q(x^k): the coefficient of x^{i} in q lands on x^{i*k}.
    let mut sub = vec![BigRational::zero(); (q.len() - 1) * k + 1];
    for (i, c) in q.iter().enumerate() {
        sub[i * k] = BigRational::from_integer(c.clone());
    }
    let roots = real_roots(&sub)?;
    for r in roots {
        let sr = sign(&r)?;
        // Wrong sign branch: skip (e.g. the negative even root, or a real k-th
        // root of a DIFFERENT conjugate of `a`).
        if (sa > 0 && sr <= 0) || (sa < 0 && sr >= 0) {
            continue;
        }
        // Exact certificate that this branch really is `a^(1/k)`: r^k == a.
        let mut pw = RealScalar::Rational(BigRational::one());
        let mut ok = true;
        for _ in 0..k {
            match pw.mul(&r) {
                Some(v) => pw = v,
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if ok && pw.cmp_exact(a)? == Ordering::Equal {
            return Some(r);
        }
    }
    None
}

/// Thom sign-condition encoding of an algebraic number: for the defining
/// polynomial `p` of degree `d`, the pairs `(coeffs(p^(j)), sign(p^(j)(a)))` for
/// `j = 1 ..= d-1`. These derivative signs uniquely pin the root among all real
/// roots of `p` (Thom's lemma), realizing z3's `Z3_rcf_*_sign_condition_*`
/// representation. Empty for a rational (degree-1 defining polynomial). `None`
/// on a refinement cap.
pub fn thom_sign_conditions(s: &RealScalar) -> Option<Vec<(Vec<BigInt>, i32)>> {
    match canonicalize(s)? {
        RealScalar::Rational(_) => Some(Vec::new()),
        RealScalar::Algebraic(v) => {
            let alpha = v.alpha();
            let coeffs: Vec<BigRational> = alpha
                .poly_coeffs()
                .into_iter()
                .map(BigRational::from_integer)
                .collect();
            let p = UniPoly::from_coeffs(coeffs);
            let d = p.degree().unwrap_or(0);
            let mut conds = Vec::new();
            let mut deriv = p.derivative();
            for _ in 1..d {
                // The derivative of an integer polynomial is integer (denom 1).
                let dc: Vec<BigInt> = deriv.coeffs().iter().map(|c| c.numer().clone()).collect();
                let sg = alpha.sign_of_poly(&deriv)?;
                conds.push((dc, sg));
                deriv = deriv.derivative();
            }
            Some(conds)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    /// √2 is the 2nd real root of x^2 - 2 (ascending: -√2, √2).
    fn sqrt2() -> RealScalar {
        let roots = real_roots(&[r(-2), r(0), r(1)]).expect("isolates");
        assert_eq!(roots.len(), 2);
        roots.into_iter().nth(1).unwrap()
    }

    #[test]
    fn real_roots_of_x2_minus_2() {
        let s = sqrt2();
        assert_eq!(sign(&s), Some(1));
        assert_eq!(is_rational(&s), Some(false));
        assert_eq!(root_index(&s), Some(2));
        assert_eq!(
            root_obj_string(&s).as_deref(),
            Some("(root-obj (+ (^ x 2) (- 2)) 2)")
        );
        // √2 * √2 == 2 exactly.
        let sq = s.mul(&s).and_then(|v| canonicalize(&v)).unwrap();
        assert!(matches!(sq, RealScalar::Rational(ref q) if *q == r(2)));
        // √2 + (−√2) == 0.
        let sum = s.add(&s.neg()).and_then(|v| canonicalize(&v)).unwrap();
        assert_eq!(sign(&sum), Some(0));
        // √2 < 3/2 but √2 > 7/5.
        let three_halves = RealScalar::Rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
        let seven_fifths = RealScalar::Rational(BigRational::new(BigInt::from(7), BigInt::from(5)));
        assert_eq!(s.cmp_exact(&three_halves), Some(Ordering::Less));
        assert_eq!(s.cmp_exact(&seven_fifths), Some(Ordering::Greater));
    }

    #[test]
    fn nth_root_of_two_is_sqrt2() {
        let two = RealScalar::Rational(r(2));
        let root = nth_root(&two, 2).expect("√2 exists");
        assert_eq!(
            root_obj_string(&root).as_deref(),
            Some("(root-obj (+ (^ x 2) (- 2)) 2)")
        );
        // Perfect powers collapse to rationals: 4^(1/2) = 2, 8^(1/3) = 2.
        let four = RealScalar::Rational(r(4));
        assert!(
            matches!(canonicalize(&nth_root(&four, 2).unwrap()).unwrap(), RealScalar::Rational(ref q) if *q == r(2))
        );
        let eight = RealScalar::Rational(r(8));
        assert!(
            matches!(canonicalize(&nth_root(&eight, 3).unwrap()).unwrap(), RealScalar::Rational(ref q) if *q == r(2))
        );
        // Odd root of a negative: (-8)^(1/3) = -2.
        let neg8 = RealScalar::Rational(r(-8));
        assert!(
            matches!(canonicalize(&nth_root(&neg8, 3).unwrap()).unwrap(), RealScalar::Rational(ref q) if *q == r(-2))
        );
        // Even root of a negative: no real root.
        assert!(nth_root(&RealScalar::Rational(r(-2)), 2).is_none());
    }

    #[test]
    fn thom_conditions_pin_sqrt2() {
        // Defining poly x^2 - 2 (degree 2) → one sign condition (p' = 2x).
        let s = sqrt2();
        let conds = thom_sign_conditions(&s).expect("computable");
        assert_eq!(conds.len(), 1);
        // p'(√2) = 2√2 > 0.
        assert_eq!(conds[0].1, 1);
        // −√2: p'(−√2) = −2√2 < 0 (Thom distinguishes the two roots).
        let neg = real_roots(&[r(-2), r(0), r(1)])
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        let cneg = thom_sign_conditions(&neg).expect("computable");
        assert_eq!(cneg[0].1, -1);
        // A rational has no sign conditions.
        assert_eq!(
            thom_sign_conditions(&RealScalar::Rational(r(3))),
            Some(vec![])
        );
    }
}
