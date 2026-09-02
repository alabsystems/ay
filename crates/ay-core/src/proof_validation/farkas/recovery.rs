// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact recovery of a missing equality multiplier in a Farkas certificate.

use std::collections::BTreeSet;

use num_rational::{BigRational, Rational64};
use num_traits::{Signed, ToPrimitive, Zero};

use super::{
    normalized_constraint_alternatives, rational64_to_bigrational,
    verify_farkas_conflict_lits_full, LinearExpr,
};
use crate::{FarkasAnnotation, TermId, TermStore, TheoryLit};

/// Recover the exact multiplier of one asserted equality in a partially known
/// Farkas combination.
///
/// `farkas` supplies the already-certified multipliers for every other row;
/// its entry at `equality_index` is ignored. The remaining weighted rows must
/// leave a residual linear expression that is an exact scalar multiple of the
/// equality. The recovered multiplier is stored as a non-negative magnitude
/// (equality orientation is sign-free) and the complete certificate is replayed
/// against `conflict` before it is returned.
///
/// This is intentionally limited to one positive equality and otherwise
/// ordinary linear constraints. A non-linear substitution, a disequality,
/// non-proportional residuals, overflow outside [`Rational64`], or a
/// non-contradicting result returns `None`.
#[must_use]
pub fn recover_single_equality_farkas(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    equality_index: usize,
) -> Option<FarkasAnnotation> {
    if conflict.len() != farkas.coefficients.len() || equality_index >= conflict.len() {
        return None;
    }

    let mut base = LinearExpr::zero();
    let mut equality = None;
    for (index, (literal, coefficient)) in
        conflict.iter().zip(farkas.coefficients.iter()).enumerate()
    {
        if index != equality_index && *coefficient < Rational64::zero() {
            return None;
        }
        let alternatives =
            normalized_constraint_alternatives(terms, literal.term, literal.value).ok()?;
        let mut alternative_iter = alternatives.iter();
        if index == equality_index {
            let (Some(oriented), Some(_), None) = (
                alternative_iter.next(),
                alternative_iter.next(),
                alternative_iter.next(),
            ) else {
                return None;
            };
            equality = Some(oriented.expr.clone());
        } else {
            let (Some(constraint), None) = (alternative_iter.next(), alternative_iter.next())
            else {
                return None;
            };
            base.add_scaled(&constraint.expr, &rational64_to_bigrational(coefficient));
        }
    }
    let equality = equality?;

    // Solve base + mu * equality = constant exactly. Every variable row must
    // imply the same `mu`; variables absent from the equality must already be
    // eliminated by the known inequality multipliers.
    let variables: BTreeSet<TermId> = base
        .coeffs
        .keys()
        .chain(equality.coeffs.keys())
        .copied()
        .collect();
    let mut multiplier: Option<BigRational> = None;
    for variable in variables {
        let base_coefficient = base
            .coeffs
            .get(&variable)
            .cloned()
            .unwrap_or_else(BigRational::zero);
        let equality_coefficient = equality
            .coeffs
            .get(&variable)
            .cloned()
            .unwrap_or_else(BigRational::zero);
        if equality_coefficient.is_zero() {
            if !base_coefficient.is_zero() {
                return None;
            }
            continue;
        }
        let candidate = -base_coefficient / equality_coefficient;
        if multiplier
            .as_ref()
            .is_some_and(|existing| existing != &candidate)
        {
            return None;
        }
        multiplier = Some(candidate);
    }

    let magnitude = multiplier.unwrap_or_else(BigRational::zero).abs();
    let numerator = magnitude.numer().to_i64()?;
    let denominator = magnitude.denom().to_i64()?;
    let mut recovered = farkas.clone();
    *recovered.coefficients.get_mut(equality_index)? = Rational64::new(numerator, denominator);

    verify_farkas_conflict_lits_full(terms, conflict, &recovered).ok()?;
    Some(recovered)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::*;
    use crate::Sort;

    #[test]
    fn recovers_scaled_equality_multiplier_exactly() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let two = terms.mk_int(BigInt::from(2));
        let two_x = terms.mk_mul(vec![two, x]);
        let equality = terms.mk_eq(two_x, y);
        let positive = terms.mk_gt(x, zero);
        let non_positive = terms.mk_le(y, zero);
        let conflict = vec![
            TheoryLit::new(equality, true),
            TheoryLit::new(positive, true),
            TheoryLit::new(non_positive, true),
        ];
        let partial = FarkasAnnotation::new(vec![
            Rational64::from(0),
            Rational64::from(1),
            Rational64::new(1, 2),
        ]);

        let recovered = recover_single_equality_farkas(&terms, &conflict, &partial, 0)
            .expect("the residual is exactly one half of the scaled equality");
        assert_eq!(
            recovered.coefficients,
            vec![
                Rational64::new(1, 2),
                Rational64::from(1),
                Rational64::new(1, 2),
            ]
        );
    }
}
