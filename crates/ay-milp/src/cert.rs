// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-level certificates: evidence as data.
//!
//! Every certificate refers only to [`Model`] rows and column bounds — never
//! to solver state — so `verify` is an independent exact-rational check a
//! caller can rerun without trusting the search that produced the evidence.
//! This separation is the crate's "evidence is data" contract.
//!
//! Orientation convention: each referenced bound is turned into a `>= 0` fact
//! (mirroring `ay_lra::OptimalityCertificate`'s atom orientation):
//!
//! - row `r` lower side:  `a_r·x − lb_r >= 0`
//! - row `r` upper side:  `ub_r − a_r·x >= 0`
//! - col `c` lower side:  `x_c − lb_c >= 0`
//! - col `c` upper side:  `ub_c − x_c >= 0`
//!
//! A [`FarkasCertificate`] exhibits positive multipliers whose oriented
//! combination is the contradiction `0 >= positive constant`. An
//! [`OptimalityCertificate`] exhibits positive multipliers whose oriented
//! combination is exactly `objective − bound` (Minimize) or
//! `bound − objective` (Maximize), which proves `bound` is a valid objective
//! bound for every feasible point.

use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::model::{exact, Col, Model, Row, Sense};

/// Which side of a range bound a fact refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundSide {
    /// The `>= lb` side.
    Lower,
    /// The `<= ub` side.
    Upper,
}

/// A reference to one oriented model fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FactRef {
    /// One side of a row's range bound.
    RowBound {
        /// The row.
        row: Row,
        /// Which side.
        side: BoundSide,
    },
    /// One side of a column's bound.
    ColBound {
        /// The column.
        col: Col,
        /// Which side.
        side: BoundSide,
    },
}

/// A positive multiplier applied to one oriented model fact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Multiplier {
    /// The fact being scaled.
    pub fact: FactRef,
    /// The (strictly positive) multiplier.
    pub coeff: BigRational,
}

/// Why a certificate failed to verify.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CertificateError {
    /// A multiplier was zero or negative.
    #[error("multiplier {index} is not strictly positive")]
    NonpositiveMultiplier {
        /// Index into the certificate's multiplier list.
        index: usize,
    },
    /// A multiplier references the infinite side of a bound (no such fact).
    #[error("multiplier {index} references an infinite bound")]
    InfiniteBound {
        /// Index into the certificate's multiplier list.
        index: usize,
    },
    /// A multiplier references a row/column outside the model.
    #[error("multiplier {index} references a missing row/column")]
    MissingFact {
        /// Index into the certificate's multiplier list.
        index: usize,
    },
    /// The combined linear form has a nonzero coefficient where the identity
    /// requires zero (Farkas) or the objective coefficient (optimality).
    #[error("combined linear form does not match on column {col}")]
    CoefficientMismatch {
        /// The column whose combined coefficient is wrong.
        col: usize,
    },
    /// The combined constant does not complete the required identity.
    #[error("combined constant does not match")]
    ConstantMismatch,
    /// A Farkas combination that is not actually contradictory.
    #[error("combination is not a contradiction")]
    NotContradictory,
    /// A tree certificate splits on a column that is missing, not integral,
    /// or splits at a non-integer cut — the two branches would not cover the
    /// parent's integer domain, so the split proves nothing.
    #[error("split {index} on column {col} is not a valid integer split")]
    InvalidSplit {
        /// Pre-order index of the offending split in the tree.
        index: usize,
        /// The column the split names.
        col: usize,
    },
    /// A tree certificate's leaf evidence failed under its branch bounds.
    #[error("leaf {index}: {error}")]
    LeafRejected {
        /// Pre-order index of the offending leaf in the tree.
        index: usize,
        /// What the leaf's Farkas verification reported.
        error: Box<CertificateError>,
    },
}

/// An exact infeasibility witness: positive multipliers over model facts
/// whose oriented combination is `constant >= 0` with a negative constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FarkasCertificate {
    /// The positive multipliers.
    pub multipliers: Vec<Multiplier>,
}

impl FarkasCertificate {
    /// Independently verify this certificate against `model` using exact
    /// arithmetic. No solver state is consulted.
    pub fn verify(&self, model: &Model) -> Result<(), CertificateError> {
        let combo = combine(&self.multipliers, model)?;
        Self::check_contradiction(&combo)
    }

    /// As [`Self::verify`], but with the model's COLUMN bounds replaced by
    /// `col_lb`/`col_ub` (`None` = that side is infinite). This is the leaf
    /// check of a [`crate::tree_cert::MilpInfeasibilityCertificate`]: a leaf
    /// lives under its branch's accumulated bound tightenings, so its Farkas
    /// facts must be priced at THOSE bounds, exactly. Row facts are unchanged.
    pub(crate) fn verify_with_col_bounds(
        &self,
        model: &Model,
        col_lb: &[Option<BigRational>],
        col_ub: &[Option<BigRational>],
    ) -> Result<(), CertificateError> {
        let combo = combine_bounded(&self.multipliers, model, Some((col_lb, col_ub)))?;
        Self::check_contradiction(&combo)
    }

    /// The Farkas identity: every combined coefficient exactly zero, combined
    /// constant strictly negative (`0 >= positive` after re-orientation).
    fn check_contradiction(combo: &Combination) -> Result<(), CertificateError> {
        for (col, coeff) in combo.coeffs.iter().enumerate() {
            if !coeff.is_zero() {
                return Err(CertificateError::CoefficientMismatch { col });
            }
        }
        if combo.constant.is_negative() {
            Ok(())
        } else {
            Err(CertificateError::NotContradictory)
        }
    }
}

/// An exact dual bound witness for an optimum of an explicit linear
/// objective: positive multipliers over model facts whose oriented
/// combination equals `objective − bound` (Minimize) or `bound − objective`
/// (Maximize).
///
/// The certificate names its own objective (sorted, exact coefficients) so
/// it works both for the model objective and for the per-column objectives
/// of `tighten_col_bounds`. It excludes any constant offset: the session
/// layer folds offsets into the reported `Outcome` value, while the
/// certificate bounds the pure linear form. Together with a feasible point
/// achieving `bound` (carried separately in [`crate::Outcome::Optimal`]),
/// this proves optimality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptimalityCertificate {
    /// The direction this bound is proved for.
    pub sense: Sense,
    /// The objective this certificate bounds: sorted, duplicate-free exact
    /// coefficients over columns.
    pub objective: Vec<(u32, BigRational)>,
    /// The proved bound on `objective·x` over all feasible points: a lower
    /// bound for Minimize, an upper bound for Maximize.
    pub bound: BigRational,
    /// The positive multipliers.
    pub multipliers: Vec<Multiplier>,
}

impl OptimalityCertificate {
    /// Independently verify this certificate against `model` using exact
    /// arithmetic. No solver state is consulted.
    ///
    /// Checks the polynomial identity
    /// `Σ coeff_i · oriented_i == objective − bound` (Minimize) or
    /// `== bound − objective` (Maximize).
    pub fn verify(&self, model: &Model) -> Result<(), CertificateError> {
        let combo = combine(&self.multipliers, model)?;
        // Accumulate (not assign) so a duplicated column sums, exactly as
        // `combine` builds the multiplier side — otherwise an objective with
        // repeated columns would be checked against only its last entry.
        let mut want = vec![BigRational::zero(); model.num_cols()];
        for &(c, ref a) in &self.objective {
            let slot = want
                .get_mut(c as usize)
                .ok_or(CertificateError::CoefficientMismatch { col: c as usize })?;
            match self.sense {
                Sense::Minimize => *slot += a.clone(),
                Sense::Maximize => *slot -= a.clone(),
            }
        }
        for (col, (combined, wanted)) in combo.coeffs.iter().zip(&want).enumerate() {
            if combined != wanted {
                return Err(CertificateError::CoefficientMismatch { col });
            }
        }
        let want_const = match self.sense {
            Sense::Minimize => -self.bound.clone(),
            Sense::Maximize => self.bound.clone(),
        };
        if combo.constant == want_const {
            Ok(())
        } else {
            Err(CertificateError::ConstantMismatch)
        }
    }

    /// Re-express this optimality bound as a [`CertifiedRow`] containing the
    /// valid inequality established by the dual proof.
    ///
    /// A Minimize certificate proves `objective·x >= bound` directly. A
    /// Maximize certificate proves `objective·x <= bound`, re-oriented to the
    /// row's lower-bound form as `(−objective)·x >= −bound`. In BOTH cases the
    /// same positive multipliers already combine to the row's `coeffs·x − lb`,
    /// so the produced row verifies against the model with no re-derivation.
    #[must_use]
    pub fn into_certified_row(self) -> CertifiedRow {
        let (coeffs, lb) = match self.sense {
            Sense::Minimize => (self.objective, self.bound),
            Sense::Maximize => (
                self.objective.into_iter().map(|(c, a)| (c, -a)).collect(),
                -self.bound,
            ),
        };
        CertifiedRow {
            coeffs,
            lb,
            multipliers: self.multipliers,
        }
    }
}

/// A cut row together with the exact derivation that proves it valid for the
/// model.
///
/// The derivation multipliers prove `coeffs·x − lb >= 0` for every point
/// satisfying the model's constraints: their oriented combination must equal
/// `coeffs·x − lb`. The native branch-and-cut engine may populate these rows;
/// the exact-only solver path does not emit cuts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedRow {
    /// Cut coefficients, sorted by column index.
    pub coeffs: Vec<(u32, BigRational)>,
    /// The proved lower bound: `coeffs·x >= lb`.
    pub lb: BigRational,
    /// Positive multipliers over model facts deriving the cut.
    pub multipliers: Vec<Multiplier>,
}

impl CertifiedRow {
    /// Independently verify the derivation against `model`.
    pub fn verify(&self, model: &Model) -> Result<(), CertificateError> {
        let combo = combine(&self.multipliers, model)?;
        // Accumulate (not assign) so a duplicated column sums, matching how
        // `combine` builds the multiplier side: the row `coeffs·x` means the
        // SUM over repeated columns, and `verify` must check that meaning.
        let mut want = vec![BigRational::zero(); model.num_cols()];
        for &(c, ref a) in &self.coeffs {
            let slot = want
                .get_mut(c as usize)
                .ok_or(CertificateError::CoefficientMismatch { col: c as usize })?;
            *slot += a.clone();
        }
        for (col, (combined, wanted)) in combo.coeffs.iter().zip(&want).enumerate() {
            if combined != wanted {
                return Err(CertificateError::CoefficientMismatch { col });
            }
        }
        if combo.constant == -self.lb.clone() {
            Ok(())
        } else {
            Err(CertificateError::ConstantMismatch)
        }
    }
}

/// The exact combined linear form `coeffs·x + constant` of a multiplier set.
struct Combination {
    coeffs: Vec<BigRational>,
    constant: BigRational,
}

/// Accumulate `Σ coeff_i · oriented_i` exactly. Errors on nonpositive
/// multipliers, references to infinite bounds, or out-of-range facts.
fn combine(multipliers: &[Multiplier], model: &Model) -> Result<Combination, CertificateError> {
    combine_bounded(multipliers, model, None)
}

/// [`combine`], with the model's column bounds optionally OVERRIDDEN by
/// exact-rational effective bounds (`None` entry = infinite on that side).
/// The tree-certificate walk supplies the branch-tightened bounds this way,
/// so a leaf's Farkas identity is priced at the leaf's box with no float
/// round-trip: the override values never pass through `f64`.
fn combine_bounded(
    multipliers: &[Multiplier],
    model: &Model,
    col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
) -> Result<Combination, CertificateError> {
    let mut coeffs = vec![BigRational::zero(); model.num_cols()];
    let mut constant = BigRational::zero();
    for (index, m) in multipliers.iter().enumerate() {
        if !m.coeff.is_positive() {
            return Err(CertificateError::NonpositiveMultiplier { index });
        }
        match m.fact {
            FactRef::RowBound { row, side } => {
                if row.index() >= model.num_rows() {
                    return Err(CertificateError::MissingFact { index });
                }
                let (row_coeffs, lb, ub) = model.row(row);
                // VERDICT-CRITICAL: re-price the certificate against the TRUE
                // model. When a coefficient/bound is a rounded `f64` proxy, the
                // exact-rational side-store holds the truth, so a certificate is
                // never re-verified against a rounded matrix.
                let bound = match side {
                    BoundSide::Lower => model.row_lb_exact(row.index(), lb),
                    BoundSide::Upper => model.row_ub_exact(row.index(), ub),
                }
                .ok_or(CertificateError::InfiniteBound { index })?;
                // Lower: +a·x − lb ; Upper: −a·x + ub.
                let sign_pos = matches!(side, BoundSide::Lower);
                for &(c, a) in row_coeffs {
                    let a = model.row_coeff_exact(row.index(), c, a);
                    let term = &m.coeff * a;
                    if sign_pos {
                        coeffs[c as usize] += term;
                    } else {
                        coeffs[c as usize] -= term;
                    }
                }
                if sign_pos {
                    constant -= &m.coeff * bound;
                } else {
                    constant += &m.coeff * bound;
                }
            }
            FactRef::ColBound { col, side } => {
                if col.index() >= model.num_cols() {
                    return Err(CertificateError::MissingFact { index });
                }
                let bound = match col_bounds {
                    Some((lbs, ubs)) => match side {
                        BoundSide::Lower => lbs[col.index()].clone(),
                        BoundSide::Upper => ubs[col.index()].clone(),
                    },
                    None => {
                        let (lb, ub) = model.col_bounds(col);
                        match side {
                            BoundSide::Lower => exact(lb),
                            BoundSide::Upper => exact(ub),
                        }
                    }
                }
                .ok_or(CertificateError::InfiniteBound { index })?;
                // Lower: +x − lb ; Upper: −x + ub.
                match side {
                    BoundSide::Lower => {
                        coeffs[col.index()] += &m.coeff;
                        constant -= &m.coeff * bound;
                    }
                    BoundSide::Upper => {
                        coeffs[col.index()] -= &m.coeff;
                        constant += &m.coeff * bound;
                    }
                }
            }
        }
    }
    Ok(Combination { coeffs, constant })
}
