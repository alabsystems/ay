// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-model replay for integer cuts, distinct from LP-valid CertifiedRow.

use std::time::Instant;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::cert::{check_branch_derivation, CertificateError, Multiplier};
use crate::model::{Col, Model, Row};
use crate::BoundSide;

/// Exact derivation of an integer cut. Additional rounding/disjunction rules
/// can extend this language without weakening the existing LP row contract.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IntegerCutProof {
    /// Multiply a source row side by a positive rational, check that all
    /// resulting coefficients are integral on integral columns, round its
    /// lower bound upward, then positively scale and weaken the result.
    SourceRowRounding {
        /// Caller-model row; no internal or branch-local row is admitted.
        row: Row,
        /// Orientation of that source fact.
        side: BoundSide,
        /// Positive scaling before integer rounding.
        multiplier: BigRational,
        /// Exact lower bound before rounding, bound to the caller's source.
        unrounded_bound: BigRational,
        /// Positive scaling after integer rounding.
        output_scale: BigRational,
    },
    /// VIPR-style "unsplit" over one elementary integer disjunction
    /// (Cheung, Gleixner and Steffy, *Verifying Integer Programming Results*,
    /// IPCO 2017): every integer point has `x_column <= floor` or
    /// `x_column >= floor + 1`, and each branch separately derives the cut.
    ///
    /// Each branch is a list of positive multipliers over the caller model's
    /// row facts and column-bound facts. Column facts are priced at the
    /// caller's own exact box, except that `column`'s upper bound is
    /// `min(ub, floor)` in `low` and its lower bound is `max(lb, floor + 1)`
    /// in `high`. A branch either combines to exactly the cut's coefficients
    /// with a bound at least the cut's `lb`, or to a Farkas contradiction
    /// (the branch is empty). Only `column`'s integrality is a premise: the
    /// other columns may be continuous, which is what lets this rule certify
    /// mixed-integer rounding, Gomory and disjunctive cuts on big-M
    /// indicator rows that [`Self::SourceRowRounding`] must refuse.
    ElementarySplit {
        /// Integral caller-model column the disjunction splits.
        column: Col,
        /// The split point `k`: branches `x <= k` and `x >= k + 1`.
        floor: BigInt,
        /// Derivation on the `x_column <= floor` branch.
        low: Vec<Multiplier>,
        /// Derivation on the `x_column >= floor + 1` branch.
        high: Vec<Multiplier>,
    },
}

/// A lower row `coeffs*x >= lb` with exact integer-cut replay data.
///
/// Verification reads the caller's model facts and integrality declarations.
/// No separator, solver verdict, embedded model or "global" label is trusted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedIntegerCut {
    /// Sorted, nonzero coefficients in caller column order.
    pub coeffs: Vec<(u32, BigRational)>,
    /// Exact lower bound of the actual adopted row side.
    pub lb: BigRational,
    /// Independently replayable derivation.
    pub proof: IntegerCutProof,
}

/// A failed integer-cut replay establishes no row authority.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum IntegerCutVerificationError {
    /// Source row, side or coefficient data changed or is malformed.
    #[error("integer cut does not match its caller-model source fact")]
    SourceChanged,
    /// A rounding premise lacks integral coefficients or integral columns.
    #[error("integer cut rounding requires integral coefficients on integral columns")]
    NonIntegralPremise,
    /// Invalid scaling, coefficient identity or weakening.
    #[error("integer cut conclusion does not follow from its rounding proof")]
    InvalidConclusion,
    /// Cooperative verification reached the original absolute deadline.
    #[error("integer cut replay deadline expired")]
    Interrupted,
}

#[cfg(test)]
thread_local! {
    static TEST_POLLS_LEFT: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

fn poll(deadline: Option<Instant>) -> Result<(), IntegerCutVerificationError> {
    #[cfg(test)]
    TEST_POLLS_LEFT.with(|remaining| match remaining.get() {
        Some(0) => Err(IntegerCutVerificationError::Interrupted),
        Some(left) => {
            remaining.set(Some(left - 1));
            Ok(())
        }
        None => Ok(()),
    })?;
    if deadline.is_some_and(|end| Instant::now() >= end) {
        Err(IntegerCutVerificationError::Interrupted)
    } else {
        Ok(())
    }
}

fn source_side(
    model: &Model,
    row: Row,
    side: BoundSide,
    deadline: Option<Instant>,
) -> Result<(Vec<(u32, BigRational)>, BigRational), IntegerCutVerificationError> {
    poll(deadline)?;
    let actual = model
        .row_at(row.index())
        .ok_or(IntegerCutVerificationError::SourceChanged)?;
    let (entries, lower, upper) = model.row(actual);
    if let Some(overrides) = model.exact_rows.get(&(row.index() as u32)) {
        for (index, column) in overrides.coeffs.keys().enumerate() {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            if entries.binary_search_by_key(column, |&(c, _)| c).is_err() {
                return Err(IntegerCutVerificationError::SourceChanged);
            }
        }
    }
    let (bound, sign) = match side {
        BoundSide::Lower => (model.row_lb_exact(row.index(), lower), BigRational::one()),
        BoundSide::Upper => (
            model.row_ub_exact(row.index(), upper).map(|x| -x),
            -BigRational::one(),
        ),
    };
    let bound = bound.ok_or(IntegerCutVerificationError::SourceChanged)?;
    if !bound.denom().is_positive() {
        return Err(IntegerCutVerificationError::SourceChanged);
    }
    let mut coeffs = Vec::with_capacity(entries.len());
    let mut previous = None;
    for (index, &(column, advice)) in entries.iter().enumerate() {
        if index & 0xff == 0 {
            poll(deadline)?;
        }
        if !advice.is_finite()
            || model.col_at(column as usize).is_none()
            || previous.is_some_and(|old| old >= column)
        {
            return Err(IntegerCutVerificationError::SourceChanged);
        }
        previous = Some(column);
        let coefficient = model.row_coeff_exact(row.index(), column, advice);
        if !coefficient.denom().is_positive() {
            return Err(IntegerCutVerificationError::SourceChanged);
        }
        let coefficient = coefficient * &sign;
        if !coefficient.is_zero() {
            coeffs.push((column, coefficient));
        }
    }
    Ok((coeffs, bound))
}

impl CertifiedIntegerCut {
    /// Independently replay this integer cut against the supplied caller model.
    pub fn verify(&self, model: &Model) -> Result<(), IntegerCutVerificationError> {
        self.verify_with_deadline(model, None)
    }

    /// Replay under the caller's existing absolute deadline; expiry is refusal.
    pub fn verify_with_deadline(
        &self,
        model: &Model,
        deadline: Option<Instant>,
    ) -> Result<(), IntegerCutVerificationError> {
        poll(deadline)?;
        let (row, side, multiplier, unrounded_bound, output_scale) = match &self.proof {
            IntegerCutProof::SourceRowRounding {
                row,
                side,
                multiplier,
                unrounded_bound,
                output_scale,
            } => (row, side, multiplier, unrounded_bound, output_scale),
            IntegerCutProof::ElementarySplit {
                column,
                floor,
                low,
                high,
            } => return self.verify_split(model, *column, floor, low, high, deadline),
        };
        if !multiplier.denom().is_positive()
            || !output_scale.denom().is_positive()
            || !unrounded_bound.denom().is_positive()
            || !self.lb.denom().is_positive()
            || !multiplier.is_positive()
            || !output_scale.is_positive()
        {
            return Err(IntegerCutVerificationError::InvalidConclusion);
        }
        for (index, (_, coefficient)) in self.coeffs.iter().enumerate() {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            if !coefficient.denom().is_positive() {
                return Err(IntegerCutVerificationError::InvalidConclusion);
            }
        }
        let (source, bound) = source_side(model, *row, *side, deadline)?;
        if &bound * multiplier != *unrounded_bound
            || source.len() != self.coeffs.len()
            || source.is_empty()
        {
            return Err(IntegerCutVerificationError::SourceChanged);
        }
        for (index, ((column, a), (claimed_column, claimed_a))) in
            source.iter().zip(&self.coeffs).enumerate()
        {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            let integer_a = a * multiplier;
            if !integer_a.is_integer() || !model.col_kind(Col(*column)).is_integral() {
                return Err(IntegerCutVerificationError::NonIntegralPremise);
            }
            if column != claimed_column || &integer_a * output_scale != *claimed_a {
                return Err(IntegerCutVerificationError::InvalidConclusion);
            }
        }
        let rounded =
            BigRational::from_integer(unrounded_bound.numer().div_ceil(unrounded_bound.denom()));
        if self.lb > rounded * output_scale {
            return Err(IntegerCutVerificationError::InvalidConclusion);
        }
        poll(deadline)
    }

    /// Replay an [`IntegerCutProof::ElementarySplit`] against `model`.
    ///
    /// The only integrality premise is `column`'s; both branch boxes are
    /// rebuilt here from the caller's own column bounds, so an artifact cannot
    /// smuggle in a narrower box than the recipient actually has.
    fn verify_split(
        &self,
        model: &Model,
        column: Col,
        floor: &BigInt,
        low: &[Multiplier],
        high: &[Multiplier],
        deadline: Option<Instant>,
    ) -> Result<(), IntegerCutVerificationError> {
        if self.coeffs.is_empty() || !self.lb.denom().is_positive() {
            return Err(IntegerCutVerificationError::InvalidConclusion);
        }
        let mut previous = None;
        for (index, (c, a)) in self.coeffs.iter().enumerate() {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            if !a.denom().is_positive()
                || a.is_zero()
                || previous.is_some_and(|old| old >= *c)
                || *c as usize >= model.num_cols()
            {
                return Err(IntegerCutVerificationError::InvalidConclusion);
            }
            previous = Some(*c);
        }
        if model.col_at(column.index()).is_none() {
            return Err(IntegerCutVerificationError::SourceChanged);
        }
        if !model.col_kind(column).is_integral() {
            return Err(IntegerCutVerificationError::NonIntegralPremise);
        }
        let n = model.num_cols();
        let mut col_lb = Vec::with_capacity(n);
        let mut col_ub = Vec::with_capacity(n);
        for j in 0..n {
            if j & 0xff == 0 {
                poll(deadline)?;
            }
            let (lower, upper) = model.col_bounds(Col(j as u32));
            if lower.is_nan() || upper.is_nan() {
                return Err(IntegerCutVerificationError::SourceChanged);
            }
            col_lb.push(crate::model::exact(lower));
            col_ub.push(crate::model::exact(upper));
        }
        let split_low = BigRational::from_integer(floor.clone());
        let split_high = BigRational::from_integer(floor + 1);
        let j = column.index();
        // Charge the verifier's work in coarse units against the original
        // absolute deadline (and the deterministic test budget).
        let mut pending = 0usize;
        let mut work = |units: usize| -> Result<(), CertificateError> {
            pending = pending.saturating_add(units.max(1));
            if pending >= 0x100 {
                pending = 0;
                poll(deadline).map_err(|_| CertificateError::DeadlineExceeded)?;
            }
            Ok(())
        };
        for branch in [BoundSide::Upper, BoundSide::Lower] {
            let (multipliers, original) = match branch {
                BoundSide::Upper => (low, col_ub[j].clone()),
                BoundSide::Lower => (high, col_lb[j].clone()),
            };
            let tightened = match (branch, original.clone()) {
                (BoundSide::Upper, Some(u)) => u.min(split_low.clone()),
                (BoundSide::Upper, None) => split_low.clone(),
                (BoundSide::Lower, Some(l)) => l.max(split_high.clone()),
                (BoundSide::Lower, None) => split_high.clone(),
            };
            match branch {
                BoundSide::Upper => col_ub[j] = Some(tightened),
                BoundSide::Lower => col_lb[j] = Some(tightened),
            }
            let checked = check_branch_derivation(
                multipliers,
                model,
                &col_lb,
                &col_ub,
                &self.coeffs,
                &self.lb,
                &mut work,
            );
            match branch {
                BoundSide::Upper => col_ub[j] = original,
                BoundSide::Lower => col_lb[j] = original,
            }
            match checked {
                Ok(_) => {}
                Err(CertificateError::DeadlineExceeded) => {
                    return Err(IntegerCutVerificationError::Interrupted)
                }
                Err(
                    CertificateError::MissingFact { .. }
                    | CertificateError::InfiniteBound { .. }
                    | CertificateError::MalformedModel { .. }
                    | CertificateError::MalformedBoundOverride { .. },
                ) => return Err(IntegerCutVerificationError::SourceChanged),
                Err(_) => return Err(IntegerCutVerificationError::InvalidConclusion),
            }
        }
        poll(deadline)
    }

    /// Reconstruct a supported rank-one proof of an ACTUAL adopted row side.
    /// Unsupported derivations remain explicit omissions in the capture report.
    pub(crate) fn reconstruct(
        model: &Model,
        coeffs: Vec<(u32, BigRational)>,
        lb: BigRational,
        deadline: Option<Instant>,
    ) -> Result<Option<Self>, IntegerCutVerificationError> {
        poll(deadline)?;
        if !lb.denom().is_positive() || coeffs.is_empty() {
            return Ok(None);
        }
        let mut previous = None;
        for (index, (column, coefficient)) in coeffs.iter().enumerate() {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            if !coefficient.denom().is_positive()
                || coefficient.is_zero()
                || previous.is_some_and(|old| old >= *column)
            {
                return Ok(None);
            }
            previous = Some(*column);
        }
        // Normalize the stored rational normal into a primitive integer normal.
        let mut denominator = BigInt::one();
        for (index, (_, coefficient)) in coeffs.iter().enumerate() {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            denominator = denominator.lcm(coefficient.denom());
        }
        let mut divisor = BigInt::zero();
        for (index, (_, coefficient)) in coeffs.iter().enumerate() {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            divisor = divisor.gcd(&(coefficient.numer() * (&denominator / coefficient.denom())));
        }
        let normalization = BigRational::new(denominator, divisor.abs());
        let output_scale = normalization.recip();
        let mut primitive = Vec::with_capacity(coeffs.len());
        for (index, (column, coefficient)) in coeffs.iter().enumerate() {
            if index & 0xff == 0 {
                poll(deadline)?;
            }
            primitive.push((*column, coefficient * &normalization));
        }
        for index in 0..model.num_rows() {
            poll(deadline)?;
            let row = Row(index as u32);
            for side in [BoundSide::Lower, BoundSide::Upper] {
                let (source, bound) = match source_side(model, row, side, deadline) {
                    Ok(fact) => fact,
                    Err(IntegerCutVerificationError::Interrupted) => {
                        return Err(IntegerCutVerificationError::Interrupted)
                    }
                    Err(_) => continue,
                };
                if source.len() != primitive.len()
                    || source.first().map(|x| x.0) != primitive.first().map(|x| x.0)
                {
                    continue;
                }
                let multiplier = &primitive[0].1 / &source[0].1;
                if !multiplier.is_positive() {
                    continue;
                }
                let mut same_normal = true;
                for (index, ((c, a), (d, b))) in source.iter().zip(&primitive).enumerate() {
                    if index & 0xff == 0 {
                        poll(deadline)?;
                    }
                    if c != d || a * &multiplier != *b {
                        same_normal = false;
                        break;
                    }
                }
                if !same_normal {
                    continue;
                }
                let unrounded_bound = bound * &multiplier;
                // Export genuine rounding strength, never an unrelated LP row.
                if unrounded_bound.is_integer() || lb <= &unrounded_bound * &output_scale {
                    continue;
                }
                let mut retained_coeffs = Vec::with_capacity(coeffs.len());
                for (index, coefficient) in coeffs.iter().enumerate() {
                    if index & 0xff == 0 {
                        poll(deadline)?;
                    }
                    retained_coeffs.push(coefficient.clone());
                }
                let cut = Self {
                    coeffs: retained_coeffs,
                    lb: lb.clone(),
                    proof: IntegerCutProof::SourceRowRounding {
                        row,
                        side,
                        multiplier,
                        unrounded_bound,
                        output_scale: output_scale.clone(),
                    },
                };
                match cut.verify_with_deadline(model, deadline) {
                    Ok(()) => return Ok(Some(cut)),
                    Err(IntegerCutVerificationError::Interrupted) => {
                        return Err(IntegerCutVerificationError::Interrupted)
                    }
                    Err(_) => {}
                }
            }
        }
        poll(deadline)?;
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_cut_deadline_interrupts_initial_public_coefficient_scan() {
        // The absent source row would otherwise produce SourceChanged. Exhaust
        // a deterministic budget inside the public coefficient scan first.
        let cut = CertifiedIntegerCut {
            coeffs: (0..1024)
                .map(|column| (column, BigRational::one()))
                .collect(),
            lb: BigRational::one(),
            proof: IntegerCutProof::SourceRowRounding {
                row: Row(0),
                side: BoundSide::Lower,
                multiplier: BigRational::one(),
                unrounded_bound: BigRational::new(1.into(), 2.into()),
                output_scale: BigRational::one(),
            },
        };
        TEST_POLLS_LEFT.with(|remaining| remaining.set(Some(2)));
        let result = cut.verify(&Model::new());
        TEST_POLLS_LEFT.with(|remaining| remaining.set(None));
        assert_eq!(result, Err(IntegerCutVerificationError::Interrupted));
        assert_eq!(
            cut.verify(&Model::new()),
            Err(IntegerCutVerificationError::SourceChanged)
        );
    }

    #[test]
    fn rank_one_rounding_covers_both_sides_and_refuses_negative_scaling() {
        for (lower, upper, sign, rhs) in
            [(1.0, f64::INFINITY, 1, 1), (f64::NEG_INFINITY, 3.0, -1, -1)]
        {
            let mut model = Model::new();
            let x = model.add_binary_col();
            let y = model.add_binary_col();
            model.add_row(lower, upper, &[(x, 2.0), (y, 2.0)]);
            let a = BigRational::from_integer(sign.into());
            let cut = CertifiedIntegerCut::reconstruct(
                &model,
                vec![(x.0, a.clone()), (y.0, a)],
                BigRational::from_integer(rhs.into()),
                None,
            )
            .unwrap()
            .unwrap();
            cut.verify(&model).unwrap();
            for xv in 0..=1 {
                for yv in 0..=1 {
                    let point = [
                        BigRational::from_integer(xv.into()),
                        BigRational::from_integer(yv.into()),
                    ];
                    if model.check_point(&point).is_ok() {
                        let activity: BigRational = cut
                            .coeffs
                            .iter()
                            .map(|(c, a)| a * &point[*c as usize])
                            .sum();
                        assert!(activity >= cut.lb);
                    }
                }
            }
            if sign == -1 {
                // Dropping either positivity premise would accept a cut
                // excluding the actual source witness (0,0).
                let zero = [BigRational::zero(), BigRational::zero()];
                model.check_point(&zero).unwrap();
                let mut negative_before = cut.clone();
                for (_, a) in &mut negative_before.coeffs {
                    *a = -a.clone();
                }
                negative_before.lb = BigRational::from_integer(2.into());
                let IntegerCutProof::SourceRowRounding {
                    multiplier,
                    unrounded_bound,
                    ..
                } = &mut negative_before.proof
                else {
                    panic!("rank-one reconstruction yields a rounding proof");
                };
                *multiplier = -multiplier.clone();
                *unrounded_bound = -unrounded_bound.clone();
                assert_eq!(
                    negative_before.verify(&model),
                    Err(IntegerCutVerificationError::InvalidConclusion)
                );
                let mut negative_after = cut;
                for (_, a) in &mut negative_after.coeffs {
                    *a = -a.clone();
                }
                negative_after.lb = BigRational::one();
                let IntegerCutProof::SourceRowRounding { output_scale, .. } =
                    &mut negative_after.proof
                else {
                    panic!("rank-one reconstruction yields a rounding proof");
                };
                *output_scale = -output_scale.clone();
                assert_eq!(
                    negative_after.verify(&model),
                    Err(IntegerCutVerificationError::InvalidConclusion)
                );
                let half = BigRational::new(1.into(), 2.into());
                let scaled = CertifiedIntegerCut::reconstruct(
                    &model,
                    vec![(x.0, -half.clone()), (y.0, -half.clone())],
                    -half,
                    None,
                )
                .unwrap()
                .unwrap();
                scaled.verify(&model).unwrap();
            }
        }
    }

    #[test]
    fn source_rounding_honors_exact_side_store_and_integral_kind() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let row = model.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0)]);
        let coeffs = vec![(x.0, BigRational::from_integer((-1).into()))];
        let lb = BigRational::from_integer((-1).into());
        let cut = CertifiedIntegerCut::reconstruct(&model, coeffs.clone(), lb.clone(), None)
            .unwrap()
            .unwrap();
        cut.verify(&model).unwrap();
        model.record_inexact_row_bound(row, false, BigRational::from_integer(4.into()));
        assert!(
            cut.verify(&model).is_err(),
            "rounded float proxy cannot hide a changed exact premise"
        );
        model.record_inexact_row_bound(row, false, BigRational::new(5.into(), 2.into()));
        let exact_cut = CertifiedIntegerCut::reconstruct(&model, coeffs, lb, None)
            .unwrap()
            .unwrap();
        exact_cut.verify(&model).unwrap();
        model.cols[x.index()].kind = crate::ColKind::Continuous;
        assert_eq!(
            exact_cut.verify(&model),
            Err(IntegerCutVerificationError::NonIntegralPremise)
        );
    }
}
