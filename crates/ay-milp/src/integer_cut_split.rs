// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof SEARCH for [`IntegerCutProof::ElementarySplit`].
//!
//! A root cut that mixes continuous and integral columns (big-M mixed-integer
//! rounding, Gomory, lifted indicator cuts) has no source-row rounding proof,
//! but it is usually a split cut on one integral column: valid on
//! `x_j <= k` and on `x_j >= k + 1` separately. This module finds such a
//! column and the two branch derivations.
//!
//! Everything here is advice. The float LP chooses candidate columns and
//! proposes dual vectors; [`bound_multipliers_from_duals`] turns a dual into
//! exact multipliers whose combination equals the cut's coefficients by
//! construction; a phase-I ray becomes an exact Farkas witness. Only an
//! artifact that then passes [`CertifiedIntegerCut::verify_with_deadline`]
//! against the caller's model is returned. A float that lies costs a
//! candidate, never validity.
//!
//! The search is bounded: one root LP, then at most
//! [`MAX_SPLIT_CANDIDATES`] columns with two branch LPs each, all under the
//! caller's absolute deadline.

use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::cert::{check_branch_derivation, BranchConclusion, CertificateError, Multiplier};
use crate::integer_cut::{CertifiedIntegerCut, IntegerCutProof, IntegerCutVerificationError};
use crate::model::{exact, Col, Model, Row, Sense};
use crate::opt_cert::{bound_multipliers_from_duals, grid_ladder, DEFAULT_DUAL_GRID_BITS};
use crate::simplex::{Candidate, FloatLp, SimplexStatus};
use crate::tree_cert::exact_farkas_from_float_ray_grid;

/// Integral columns tried per cut, most fractional at the relaxation first.
pub(crate) const MAX_SPLIT_CANDIDATES: usize = 8;

/// A column value this close to an integer is not a split candidate.
const FRACTIONAL_TOLERANCE: f64 = 1e-6;

/// Largest split point handled; beyond it `f64` cannot name `k` exactly.
const MAX_SPLIT_MAGNITUDE: f64 = 9.007_199_254_740_992e15; // 2^53

fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|end| Instant::now() >= end)
}

/// Search for an elementary split proof of the lower row `coeffs·x >= lb`
/// over `model`. `Ok(None)` means no proof was found within the candidate
/// budget; `Err(Interrupted)` means the deadline expired first.
pub(crate) fn reconstruct_split(
    model: &Model,
    coeffs: &[(u32, BigRational)],
    lb: &BigRational,
    deadline: Option<Instant>,
) -> Result<Option<CertifiedIntegerCut>, IntegerCutVerificationError> {
    if expired(deadline) {
        return Err(IntegerCutVerificationError::Interrupted);
    }
    let n = model.num_cols();
    let m = model.num_rows();
    if coeffs.is_empty() || n == 0 || !lb.denom().is_positive() {
        return Ok(None);
    }
    let mut objective = Vec::with_capacity(coeffs.len());
    let mut obj_min = vec![BigRational::zero(); n];
    let mut previous = None;
    for (column, a) in coeffs {
        let Some(weight) = a.to_f64() else {
            return Ok(None);
        };
        if *column as usize >= n
            || a.is_zero()
            || !a.denom().is_positive()
            || !weight.is_finite()
            || previous.is_some_and(|old| old >= *column)
        {
            return Ok(None);
        }
        previous = Some(*column);
        objective.push((*column, weight));
        obj_min[*column as usize] = a.clone();
    }
    let Some(lp) = FloatLp::from_model_with_deadline(model, &objective, Sense::Minimize, deadline)
    else {
        return if expired(deadline) {
            Err(IntegerCutVerificationError::Interrupted)
        } else {
            Ok(None)
        };
    };
    let mut lower = Vec::with_capacity(n + m);
    let mut upper = Vec::with_capacity(n + m);
    let mut col_lb = Vec::with_capacity(n);
    let mut col_ub = Vec::with_capacity(n);
    for j in 0..n {
        let (l, u) = model.col_bounds(Col(j as u32));
        if l.is_nan() || u.is_nan() {
            return Ok(None);
        }
        lower.push(l);
        upper.push(u);
        col_lb.push(exact(l));
        col_ub.push(exact(u));
    }
    for r in 0..m {
        let (_, l, u) = model.row(Row(r as u32));
        lower.push(l);
        upper.push(u);
    }
    let root = lp.solve_bounded(&lower, &upper, None, deadline);
    if root.status != SimplexStatus::Optimal || root.values.len() < n {
        return if expired(deadline) {
            Err(IntegerCutVerificationError::Interrupted)
        } else {
            Ok(None)
        };
    }

    // Candidate columns: integral and fractional at the relaxation's point.
    // A column the cut mentions is preferred; then the most fractional.
    let mut in_support = vec![false; n];
    for (column, _) in coeffs {
        in_support[*column as usize] = true;
    }
    let mut candidates: Vec<(usize, f64, (bool, f64))> = Vec::new();
    for (j, &v) in root.values.iter().enumerate().take(n) {
        if !model.col_kind(Col(j as u32)).is_integral() || !v.is_finite() {
            continue;
        }
        let distance = (v - v.round()).abs();
        if distance <= FRACTIONAL_TOLERANCE || v.abs() >= MAX_SPLIT_MAGNITUDE {
            continue;
        }
        candidates.push((j, v.floor(), (in_support[j], distance)));
    }
    candidates.sort_by(|a, b| {
        b.2 .0
            .cmp(&a.2 .0)
            .then(
                b.2 .1
                    .partial_cmp(&a.2 .1)
                    .unwrap_or(std::cmp::Ordering::Equal),
            )
            .then(a.0.cmp(&b.0))
    });
    candidates.truncate(MAX_SPLIT_CANDIDATES);

    let warm = (root.basis.clone(), root.at.clone());
    for (j, k, _) in candidates {
        if expired(deadline) {
            return Err(IntegerCutVerificationError::Interrupted);
        }
        let Some(k_int) = k.to_i64().map(BigInt::from) else {
            continue;
        };
        let mut branches: Vec<Vec<Multiplier>> = Vec::with_capacity(2);
        for low_branch in [true, false] {
            let (mut lo, mut up) = (lower.clone(), upper.clone());
            let (mut blb, mut bub) = (col_lb.clone(), col_ub.clone());
            if low_branch {
                up[j] = up[j].min(k);
                let split = BigRational::from_integer(k_int.clone());
                bub[j] = Some(bub[j].take().map_or(split.clone(), |u| u.min(split)));
            } else {
                lo[j] = lo[j].max(k + 1.0);
                let split = BigRational::from_integer(&k_int + 1);
                blb[j] = Some(blb[j].take().map_or(split.clone(), |l| l.max(split)));
            }
            let cand = lp.solve_bounded(
                &lo,
                &up,
                Some((warm.0.as_slice(), warm.1.as_slice())),
                deadline,
            );
            let proof = branch_proof(
                model, j, &lo, &up, &blb, &bub, &obj_min, coeffs, lb, &cand, deadline,
            )?;
            match proof {
                Some(multipliers) => branches.push(multipliers),
                None => break,
            }
        }
        if branches.len() != 2 {
            continue;
        }
        let high = branches.pop().unwrap_or_default();
        let low = branches.pop().unwrap_or_default();
        let cut = CertifiedIntegerCut {
            coeffs: coeffs.to_vec(),
            lb: lb.clone(),
            proof: IntegerCutProof::ElementarySplit {
                column: Col(j as u32),
                floor: k_int,
                low,
                high,
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
    if expired(deadline) {
        Err(IntegerCutVerificationError::Interrupted)
    } else {
        Ok(None)
    }
}

/// Turn one branch LP's result into exact branch multipliers, checked at the
/// branch's exact box. `None` when the float result yields no proof.
#[allow(clippy::too_many_arguments)]
fn branch_proof(
    model: &Model,
    column: usize,
    lo: &[f64],
    up: &[f64],
    col_lb: &[Option<BigRational>],
    col_ub: &[Option<BigRational>],
    obj_min: &[BigRational],
    coeffs: &[(u32, BigRational)],
    lb: &BigRational,
    cand: &Candidate,
    deadline: Option<Instant>,
) -> Result<Option<Vec<Multiplier>>, IntegerCutVerificationError> {
    let mut work = |_: usize| -> Result<(), CertificateError> {
        if expired(deadline) {
            Err(CertificateError::DeadlineExceeded)
        } else {
            Ok(())
        }
    };
    let mut accept = |multipliers: &[Multiplier]| -> Result<bool, IntegerCutVerificationError> {
        match check_branch_derivation(multipliers, model, col_lb, col_ub, coeffs, lb, &mut work) {
            Ok(BranchConclusion::Dominates | BranchConclusion::Empty) => Ok(true),
            Err(CertificateError::DeadlineExceeded) => {
                Err(IntegerCutVerificationError::Interrupted)
            }
            Err(_) => Ok(false),
        }
    };
    match cand.status {
        SimplexStatus::Optimal if cand.duals.len() == model.num_rows() => {
            for bits in grid_ladder(DEFAULT_DUAL_GRID_BITS) {
                for sign in [1.0f64, -1.0] {
                    if let Some(multipliers) = bound_multipliers_from_duals(
                        model,
                        obj_min,
                        &cand.duals,
                        sign,
                        col_lb,
                        col_ub,
                        bits,
                    ) {
                        if accept(&multipliers)? {
                            return Ok(Some(multipliers));
                        }
                    }
                }
            }
            Ok(None)
        }
        SimplexStatus::PrimalInfeasible if cand.farkas.len() == model.num_rows() => {
            // The ray helper prices columns at its model's own box, so give it
            // a copy carrying exactly this branch's bound on `column`.
            let mut branch = model.clone();
            branch.set_col_bounds(Col(column as u32), lo[column], up[column]);
            for bits in grid_ladder(DEFAULT_DUAL_GRID_BITS) {
                if let Some(farkas) = exact_farkas_from_float_ray_grid(&branch, &cand.farkas, bits)
                {
                    if accept(&farkas.multipliers)? {
                        return Ok(Some(farkas.multipliers));
                    }
                }
            }
            Ok(None)
        }
        _ => {
            if expired(deadline) {
                Err(IntegerCutVerificationError::Interrupted)
            } else {
                Ok(None)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BoundSide;

    fn one() -> BigRational {
        BigRational::from_integer(1.into())
    }

    /// `x` continuous in [0,1], `z` binary, `x <= z`, `x + z >= 1`.
    /// `z = 0` forces `x <= 0` and `x >= 1`, so every integer point has
    /// `z >= 1`; the LP point (1/2, 1/2) does not. Both rows mention the
    /// continuous `x`, so source-row rounding must refuse this cut.
    fn mixed() -> (Model, Col, Col) {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let z = model.add_binary_col();
        model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0), (z, -1.0)]);
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (z, 1.0)]);
        (model, x, z)
    }

    #[test]
    fn split_proves_a_mixed_cut_that_rank_one_rounding_refuses() {
        let (model, x, z) = mixed();
        let half = BigRational::new(1.into(), 2.into());
        let mut relaxation = model.clone();
        relaxation.cols[z.index()].kind = crate::ColKind::Continuous;
        relaxation
            .check_point(&[half.clone(), half.clone()])
            .unwrap();
        let coeffs = vec![(z.0, one())];
        assert_eq!(
            CertifiedIntegerCut::reconstruct(&model, coeffs.clone(), one(), None),
            Ok(None),
            "rank-one rounding has no all-integral source row here"
        );
        let cut = reconstruct_split(&model, &coeffs, &one(), None)
            .unwrap()
            .expect("elementary split on z proves z >= 1");
        cut.verify(&model).unwrap();
        let IntegerCutProof::ElementarySplit { column, floor, .. } = &cut.proof else {
            panic!("expected a split proof: {:?}", cut.proof);
        };
        assert_eq!((*column, floor.clone()), (z, BigInt::from(0)));
        // The cut removes the LP point and keeps the integer point (0, 1).
        assert!(half < cut.lb);
        model.check_point(&[BigRational::zero(), one()]).unwrap();
        // Deadline already passed: refusal, never authority.
        assert_eq!(
            cut.verify_with_deadline(&model, Some(Instant::now())),
            Err(IntegerCutVerificationError::Interrupted)
        );
        let _ = x;
    }

    #[test]
    fn split_replay_rejects_tampering_and_changed_premises() {
        let (model, x, z) = mixed();
        let coeffs = vec![(z.0, one())];
        let cut = reconstruct_split(&model, &coeffs, &one(), None)
            .unwrap()
            .unwrap();
        // A stronger bound than either branch derives.
        let mut stronger = cut.clone();
        stronger.lb = BigRational::from_integer(2.into());
        assert!(stronger.verify(&model).is_err());
        // Moving the split point: `z <= 1` is no longer an empty branch.
        let mut moved = cut.clone();
        if let IntegerCutProof::ElementarySplit { floor, .. } = &mut moved.proof {
            *floor += 1;
        }
        assert!(moved.verify(&model).is_err());
        // Scaling one multiplier breaks the exact identity.
        let mut scaled = cut.clone();
        if let IntegerCutProof::ElementarySplit { low, .. } = &mut scaled.proof {
            low[0].coeff = &low[0].coeff * BigRational::from_integer(2.into());
        }
        assert!(scaled.verify(&model).is_err());
        // A non-positive multiplier is never accepted.
        let mut negative = cut.clone();
        if let IntegerCutProof::ElementarySplit { high, .. } = &mut negative.proof {
            high.push(Multiplier {
                fact: crate::FactRef::ColBound {
                    col: x,
                    side: BoundSide::Lower,
                },
                coeff: -one(),
            });
        }
        assert!(negative.verify(&model).is_err());
        // The split column must be integral in the RECIPIENT.
        let mut continuous = model.clone();
        continuous.cols[z.index()].kind = crate::ColKind::Continuous;
        assert_eq!(
            cut.verify(&continuous),
            Err(IntegerCutVerificationError::NonIntegralPremise)
        );
        // Relaxing the premise row admits (0, 0), which violates z >= 1.
        let mut relaxed = Model::new();
        let rx = relaxed.add_col(0.0, 1.0);
        let rz = relaxed.add_binary_col();
        relaxed.add_row(f64::NEG_INFINITY, 0.0, &[(rx, 1.0), (rz, -1.0)]);
        relaxed.add_row(0.0, f64::INFINITY, &[(rx, 1.0), (rz, 1.0)]);
        relaxed
            .check_point(&[BigRational::zero(), BigRational::zero()])
            .unwrap();
        assert!(cut.verify(&relaxed).is_err());
        // A narrower recipient box keeps every premise: still valid.
        let mut child = model.clone();
        child.set_col_bounds(x, 0.25, 1.0);
        cut.verify(&child).unwrap();
    }

    #[test]
    fn split_search_declines_a_cut_that_is_not_valid() {
        let (model, _, z) = mixed();
        // `z >= 2` excludes the integer point (0, 1): no proof may exist.
        let two = BigRational::from_integer(2.into());
        assert_eq!(
            reconstruct_split(&model, &[(z.0, one())], &two, None),
            Ok(None)
        );
    }
}
