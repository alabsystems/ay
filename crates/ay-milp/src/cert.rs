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

use ay_lra::rational::Rational;
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
    /// A caller-supplied effective column-bound box does not match the model
    /// arity.
    #[error(
        "column-bound override has {lower} lower and {upper} upper entries for {expected} columns"
    )]
    MalformedBoundOverride {
        /// Number of columns in the model being verified.
        expected: usize,
        /// Number of lower-bound entries supplied.
        lower: usize,
        /// Number of upper-bound entries supplied.
        upper: usize,
    },
    /// The model data being replayed is structurally malformed. Public model
    /// constructors reject these states; the verifier still fails closed if
    /// corrupted in-crate data reaches it.
    #[error("multiplier {index} encountered malformed model data: {msg}")]
    MalformedModel {
        /// Index into the certificate's multiplier list.
        index: usize,
        /// Human-readable structural failure.
        msg: String,
    },
    /// A resource-bounded verifier reached its absolute deadline.
    #[error("certificate verification deadline exceeded")]
    DeadlineExceeded,
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
        let mut unlimited = |_| Ok(());
        self.verify_with_work_inner(model, &mut unlimited)
    }

    pub(crate) fn verify_with_work<F>(
        &self,
        model: &Model,
        work: &mut F,
    ) -> Result<(), CertificateError>
    where
        F: FnMut(usize) -> Result<(), CertificateError> + ?Sized,
    {
        self.verify_with_work_inner(model, work)
    }

    fn verify_with_work_inner<F>(&self, model: &Model, work: &mut F) -> Result<(), CertificateError>
    where
        F: FnMut(usize) -> Result<(), CertificateError> + ?Sized,
    {
        let combo = combine_with_work_inner(&self.multipliers, model, work)?;
        Self::check_contradiction_with_work(&combo, work)
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
        let mut unlimited = |_| Ok(());
        Self::check_contradiction_with_work(combo, &mut unlimited)
    }

    fn check_contradiction_with_work<F>(
        combo: &Combination,
        work: &mut F,
    ) -> Result<(), CertificateError>
    where
        F: FnMut(usize) -> Result<(), CertificateError> + ?Sized,
    {
        for (col, coeff) in combo.coeffs.iter().enumerate() {
            if col & 0xff == 0 {
                work(0x100.min(combo.coeffs.len().saturating_sub(col)))?;
            }
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
        let mut unlimited = |_| Ok(());
        self.verify_with_work_inner(model, &mut unlimited)
    }

    /// Resource-bounded twin of [`Self::verify`] for speculative solver
    /// routes.  The ordinary public replay remains unchanged; this entry only
    /// adds cooperative checks against one already-pinned absolute deadline.
    pub(crate) fn verify_with_deadline(
        &self,
        model: &Model,
        deadline: Option<std::time::Instant>,
    ) -> Result<(), CertificateError> {
        let mut bounded = |_| {
            if deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
                Err(CertificateError::DeadlineExceeded)
            } else {
                Ok(())
            }
        };
        self.verify_with_work_inner(model, &mut bounded)
    }

    pub(crate) fn verify_with_work<F>(
        &self,
        model: &Model,
        work: &mut F,
    ) -> Result<(), CertificateError>
    where
        F: FnMut(usize) -> Result<(), CertificateError> + ?Sized,
    {
        self.verify_with_work_inner(model, work)
    }

    fn verify_with_work_inner<F>(&self, model: &Model, work: &mut F) -> Result<(), CertificateError>
    where
        F: FnMut(usize) -> Result<(), CertificateError> + ?Sized,
    {
        work(1)?;
        let combo = combine_with_work_inner(&self.multipliers, model, work)?;
        // Accumulate (not assign) so a duplicated column sums, exactly as
        // `combine` builds the multiplier side — otherwise an objective with
        // repeated columns would be checked against only its last entry.
        work(model.num_cols())?;
        let mut want = vec![BigRational::zero(); model.num_cols()];
        for (index, &(c, ref a)) in self.objective.iter().enumerate() {
            if index & 0xff == 0 {
                work(0x100.min(self.objective.len().saturating_sub(index)))?;
            }
            let slot = want
                .get_mut(c as usize)
                .ok_or(CertificateError::CoefficientMismatch { col: c as usize })?;
            match self.sense {
                Sense::Minimize => *slot += a.clone(),
                Sense::Maximize => *slot -= a.clone(),
            }
        }
        for (col, (combined, wanted)) in combo.coeffs.iter().zip(&want).enumerate() {
            if col & 0xff == 0 {
                work(0x100.min(combo.coeffs.len().saturating_sub(col)))?;
            }
            if combined != wanted {
                return Err(CertificateError::CoefficientMismatch { col });
            }
        }
        work(1)?;
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

    /// Verify a BOUND LEAF: prove that no point of `model` lying inside the box
    /// `col_lb`/`col_ub` has objective better than `z_star`.
    ///
    /// This is the dual-side counterpart of
    /// [`FarkasCertificate::verify_with_col_bounds`]. A Farkas leaf says "this
    /// region is EMPTY"; a bound leaf says "this region cannot BEAT `z_star`".
    /// Together with a checked primal witness attaining `z_star`, a tree whose
    /// every leaf is one or the other proves OPTIMALITY — with no cutoff row and
    /// no objective lattice, so it applies to models with continuous columns.
    ///
    /// # Soundness: DERIVE, never READ
    ///
    /// Weak duality makes the arithmetic sound for ANY multipliers, so the only
    /// way to forge a bound leaf is to make the checker read a FACT from the
    /// emitter instead of deriving it. An adversarial review found five such
    /// holes in the obvious design; each is closed here, and the closure is the
    /// reason this is a separate function rather than a flag on
    /// [`Self::verify_with_work`]:
    ///
    /// * **The box is a PARAMETER, never recorded.** Callers must pass a box
    ///   they reconstructed themselves from the model's own column bounds
    ///   intersected with the branch path. Recording it is the fatal forgery:
    ///   with `x in [0,10]` integer, `y` continuous, row `y - x <= 0`, minimise
    ///   `-y`, a single leaf recording `x in [0,0]` "proves" `obj >= 0` while the
    ///   true optimum is `-10`. Direction is what makes this safe: pricing over
    ///   too LOOSE a box fails the coefficient identity (false reject), while too
    ///   TIGHT a box would be a false ACCEPT. Pinned by
    ///   `a_bound_leaf_cannot_forge_optimality_by_shrinking_the_box`.
    /// * **`z_star` is a PARAMETER**, threaded from the verdict the primal
    ///   witness is pinned to. Recording it per leaf lets a forger write a small
    ///   value in the block and a large one on the verdict line.
    /// * **The objective is read from `model`**, never from a certificate field.
    ///   [`Self::verify_with_work_inner`] builds its target from
    ///   `self.objective`, so a record carrying an EMPTY objective and a zero
    ///   bound verifies against every model; that is correct for a standalone
    ///   optimality certificate, which is checked against its own claim, and
    ///   wrong for a leaf, which is checked against the model.
    /// * **The objective OFFSET is applied.** `Outcome::Optimal.value` includes
    ///   it and the multiplier algebra excludes it. With offset `-100` and
    ///   `z_star = 50`, a leaf whose linear bound is `60` passes a naive
    ///   `60 >= 50` while the region can hold a point of objective `-40`.
    /// * **Inequality, not equality.** A standalone certificate checks its bound
    ///   EXACTLY; a leaf only needs to dominate `z_star`, so a leaf that proves
    ///   MORE than required must still pass.
    ///
    /// The fifth hole — type conflation — cannot be closed here: a bound leaf
    /// must never be reachable as a `tree_cert::TreeNode`, because that type's
    /// `Ok(())` MEANS "the model has no feasible point". Keeping this function
    /// out of `TreeNode` is the fix, and is why no variant was added there.
    pub(crate) fn verify_bound_leaf(
        multipliers: &[Multiplier],
        model: &Model,
        col_lb: &[Option<BigRational>],
        col_ub: &[Option<BigRational>],
        z_star: &BigRational,
    ) -> Result<(), CertificateError> {
        let combo = combine_bounded(multipliers, model, Some((col_lb, col_ub)))?;
        let sense = model.sense();

        // (c) THE OBJECTIVE COMES FROM THE MODEL. Same accumulation and the same
        // zero-proxy rule as `Model::objective_value_at`, so a column with an
        // exact override that rounded to 0.0 in advice is still counted.
        let mut want = vec![BigRational::zero(); model.num_cols()];
        for (j, spec) in model.cols.iter().enumerate() {
            if spec.obj != 0.0 || model.exact_obj.contains_key(&(j as u32)) {
                let a = model.obj_coeff_exact_at(j as u32, spec.obj);
                match sense {
                    Sense::Minimize => want[j] += a,
                    Sense::Maximize => want[j] -= a,
                }
            }
        }
        for (col, (combined, wanted)) in combo.coeffs.iter().zip(&want).enumerate() {
            if combined != wanted {
                return Err(CertificateError::CoefficientMismatch { col });
            }
        }

        // The combination establishes `want . x >= -combo.constant` over the box.
        // In the Minimize frame `want` IS the objective, so the region's linear
        // objective is bounded below by `-combo.constant`; in the Maximize frame
        // `want` is its negation, so the objective is bounded ABOVE by
        // `combo.constant`.
        //
        // (d) THE OFFSET IS APPLIED so the comparison happens in the same frame
        // as `Outcome::Optimal.value` and the primal witness.
        // `combine_bounded` works in `ay_lra::rational::Rational`; the model's
        // offset and the caller's `z_star` are `BigRational`. Convert INTO the
        // combination's type (`From<BigRational> for Rational`, rational.rs:665)
        // so the comparison is exact on both sides -- never through f64.
        let offset = Rational::from(model.obj_offset_exact());
        let target = Rational::from(z_star.clone());
        let dominates = match sense {
            Sense::Minimize => (-combo.constant.clone()) + offset >= target,
            Sense::Maximize => combo.constant.clone() + offset <= target,
        };
        if dominates {
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
    /// Materialize the valid lower row proved by a positive combination of
    /// model facts.
    ///
    /// This is the projection primitive used by decomposition lanes: after a
    /// Farkas proof against a fixed master assignment, callers may remove the
    /// assignment-only bound facts and retain the remaining combination as a
    /// globally valid row.  The combination is recomputed here against the
    /// caller's original model; no coefficient or constant supplied by the
    /// decomposition is trusted.
    pub(crate) fn from_multipliers(
        model: &Model,
        multipliers: Vec<Multiplier>,
    ) -> Result<Self, CertificateError> {
        let combo = combine(&multipliers, model)?;
        let coeffs = combo
            .coeffs
            .iter()
            .enumerate()
            .filter(|(_, coeff)| !coeff.is_zero())
            .map(|(column, coeff)| (column as u32, coeff.to_big()))
            .collect();
        let row = Self {
            coeffs,
            lb: -combo.constant.to_big(),
            multipliers,
        };
        // Keep this constructor proof-producing rather than proposal-producing:
        // every returned value has passed the same independent identity check
        // exposed by the public verifier.
        row.verify(model)?;
        Ok(row)
    }

    /// Independently verify the derivation against `model`.
    pub fn verify(&self, model: &Model) -> Result<(), CertificateError> {
        let combo = combine(&self.multipliers, model)?;
        self.check_identity(model, &combo)
    }

    /// Compose this proved lower row with the upper side of `upper_row` into
    /// an exact Farkas leaf under `branch_bounds`.
    ///
    /// `branch_bounds` are exact child-node assumptions, expressed as
    /// `(column, side, value)`. They are intersected with `model`'s own box.
    /// For example, the low child of an integer split at `k` supplies
    /// `(col, BoundSide::Upper, k)`, while the high child supplies
    /// `(col, BoundSide::Lower, k + 1)`.
    ///
    /// The intended identity is
    ///
    /// ```text
    ///   proved:       q·x - gamma >= 0
    ///   upper_row:     beta - q·x >= 0
    ///   --------------------------------
    ///                         beta - gamma >= 0
    /// ```
    ///
    /// and therefore yields a contradiction exactly when `gamma > beta`.
    /// No shape or threshold claim is trusted: this method first verifies the
    /// [`CertifiedRow`] under the branch-tightened exact box, then appends one
    /// multiplier for `upper_row`, and finally verifies the resulting
    /// [`FarkasCertificate`] under that same box. A stale child proof, a
    /// coefficient mismatch, a missing/infinite row upper bound, an invalid
    /// column handle, or a non-strict bound all return `None`.
    ///
    /// The returned certificate deliberately contains only model fact
    /// references, just like any other Farkas leaf. Its conditional bounds
    /// come from its position in a [`crate::TreeNode`]; whole-tree
    /// verification independently re-prices it under the actual split path.
    #[must_use]
    pub fn into_farkas_against_row_upper(
        self,
        model: &Model,
        upper_row: Row,
        branch_bounds: &[(Col, BoundSide, BigRational)],
    ) -> Option<FarkasCertificate> {
        let (col_lb, col_ub) = effective_col_bounds(model, branch_bounds)?;
        self.verify_with_col_bounds(model, &col_lb, &col_ub).ok()?;

        let mut multipliers = self.multipliers;
        multipliers.push(Multiplier {
            fact: FactRef::RowBound {
                row: upper_row,
                side: BoundSide::Upper,
            },
            coeff: BigRational::from_integer(1.into()),
        });
        let farkas = FarkasCertificate { multipliers };
        farkas
            .verify_with_col_bounds(model, &col_lb, &col_ub)
            .ok()?;
        Some(farkas)
    }

    /// [`Self::verify`], with column facts priced at a branch-tightened exact
    /// box. This is private because a bare [`CertifiedRow`] does not carry the
    /// assumptions that make such a conditional proof meaningful; the public
    /// composition API above immediately closes it into a Farkas leaf.
    fn verify_with_col_bounds(
        &self,
        model: &Model,
        col_lb: &[Option<BigRational>],
        col_ub: &[Option<BigRational>],
    ) -> Result<(), CertificateError> {
        let combo = combine_bounded(&self.multipliers, model, Some((col_lb, col_ub)))?;
        self.check_identity(model, &combo)
    }

    /// Check that `combo` is exactly `self.coeffs·x - self.lb`.
    fn check_identity(&self, model: &Model, combo: &Combination) -> Result<(), CertificateError> {
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

/// Intersect exact branch assumptions into the model's own exact column box.
///
/// This deliberately mirrors the tree verifier's bound walk. The helper is
/// fail-closed on a missing column, and never widens a model bound.
fn effective_col_bounds(
    model: &Model,
    branch_bounds: &[(Col, BoundSide, BigRational)],
) -> Option<(Vec<Option<BigRational>>, Vec<Option<BigRational>>)> {
    let n = model.num_cols();
    let mut lb: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(model.col_bounds(Col(j as u32)).0))
        .collect();
    let mut ub: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(model.col_bounds(Col(j as u32)).1))
        .collect();
    for (col, side, value) in branch_bounds {
        let slot = match side {
            BoundSide::Lower => lb.get_mut(col.index())?,
            BoundSide::Upper => ub.get_mut(col.index())?,
        };
        *slot = Some(match slot.take() {
            Some(previous) => match side {
                BoundSide::Lower => previous.max(value.clone()),
                BoundSide::Upper => previous.min(value.clone()),
            },
            None => value.clone(),
        });
    }
    Some((lb, ub))
}

/// The exact combined linear form `coeffs·x + constant` of a multiplier set.
struct Combination {
    coeffs: Vec<Rational>,
    constant: Rational,
}

/// Accumulate `Σ coeff_i · oriented_i` exactly. Errors on nonpositive
/// multipliers, references to infinite bounds, or out-of-range facts.
fn combine(multipliers: &[Multiplier], model: &Model) -> Result<Combination, CertificateError> {
    let mut unlimited = |_| Ok(());
    combine_bounded_with_work(multipliers, model, None, &mut unlimited)
}

fn combine_with_work_inner<F>(
    multipliers: &[Multiplier],
    model: &Model,
    work: &mut F,
) -> Result<Combination, CertificateError>
where
    F: FnMut(usize) -> Result<(), CertificateError> + ?Sized,
{
    combine_bounded_with_work(multipliers, model, None, work)
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
    let mut unlimited = |_| Ok(());
    combine_bounded_with_work(multipliers, model, col_bounds, &mut unlimited)
}

fn combine_bounded_with_work<F>(
    multipliers: &[Multiplier],
    model: &Model,
    col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
    work: &mut F,
) -> Result<Combination, CertificateError>
where
    F: FnMut(usize) -> Result<(), CertificateError> + ?Sized,
{
    work(1)?;
    if let Some((lbs, ubs)) = col_bounds {
        let expected = model.num_cols();
        if lbs.len() != expected || ubs.len() != expected {
            return Err(CertificateError::MalformedBoundOverride {
                expected,
                lower: lbs.len(),
                upper: ubs.len(),
            });
        }
    }

    work(model.num_cols())?;
    let mut coeffs = vec![Rational::zero(); model.num_cols()];
    let mut constant = Rational::zero();
    for (index, m) in multipliers.iter().enumerate() {
        work(1)?;
        if !m.coeff.is_positive() {
            return Err(CertificateError::NonpositiveMultiplier { index });
        }
        let multiplier = Rational::from(&m.coeff);
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
                    BoundSide::Lower => row_bound_exact_small(model, row.index(), lb, side, index)?,
                    BoundSide::Upper => row_bound_exact_small(model, row.index(), ub, side, index)?,
                };
                // Lower: +a·x − lb ; Upper: −a·x + ub.
                let sign_pos = matches!(side, BoundSide::Lower);
                let oriented = if sign_pos {
                    multiplier.clone()
                } else {
                    -&multiplier
                };
                for (entry, &(c, a)) in row_coeffs.iter().enumerate() {
                    if entry & 0xff == 0 {
                        work(0x100.min(row_coeffs.len().saturating_sub(entry)))?;
                    }
                    if c as usize >= model.num_cols() {
                        return Err(CertificateError::MalformedModel {
                            index,
                            msg: format!("row {} references missing column {c}", row.index()),
                        });
                    }
                    if !a.is_finite() {
                        return Err(CertificateError::MalformedModel {
                            index,
                            msg: format!(
                                "row {} has a non-finite coefficient at column {c}",
                                row.index()
                            ),
                        });
                    }
                    let a = model.row_coeff_exact_small(row.index(), c, a);
                    coeffs[c as usize].mul_add_assign(&oriented, &a);
                }
                constant.mul_add_assign(&(-&oriented), &bound);
            }
            FactRef::ColBound { col, side } => {
                if col.index() >= model.num_cols() {
                    return Err(CertificateError::MissingFact { index });
                }
                let bound = match col_bounds {
                    Some((lbs, ubs)) => {
                        let slot = match side {
                            BoundSide::Lower => lbs.get(col.index()),
                            BoundSide::Upper => ubs.get(col.index()),
                        }
                        .ok_or(CertificateError::MissingFact { index })?;
                        slot.as_ref()
                            .map(Rational::from)
                            .ok_or(CertificateError::InfiniteBound { index })
                    }
                    None => {
                        let (lb, ub) = model.col_bounds(col);
                        match side {
                            BoundSide::Lower => {
                                bound_exact_small(lb, side, index, "column lower bound")
                            }
                            BoundSide::Upper => {
                                bound_exact_small(ub, side, index, "column upper bound")
                            }
                        }
                    }
                }?;
                // Lower: +x − lb ; Upper: −x + ub.
                let oriented = match side {
                    BoundSide::Lower => multiplier,
                    BoundSide::Upper => -multiplier,
                };
                coeffs[col.index()] += &oriented;
                constant.mul_add_assign(&(-&oriented), &bound);
            }
        }
    }
    Ok(Combination { coeffs, constant })
}

/// `BigRational` row-bound extraction, reached only from
/// [`combine_bounded_big_reference`]. Production uses
/// [`row_bound_exact_small`]; the two are deliberately separate code so the
/// differential check has an independent oracle.
fn row_bound_exact(
    model: &Model,
    row: usize,
    bound: f64,
    side: BoundSide,
    index: usize,
) -> Result<BigRational, CertificateError> {
    if bound.is_nan() {
        return Err(CertificateError::MalformedModel {
            index,
            msg: format!("row {row} has a NaN bound"),
        });
    }
    if !bound.is_finite() {
        return match (side, bound.is_sign_negative()) {
            (BoundSide::Lower, true) | (BoundSide::Upper, false) => {
                Err(CertificateError::InfiniteBound { index })
            }
            (BoundSide::Lower, false) => Err(CertificateError::MalformedModel {
                index,
                msg: format!("row {row} has +inf lower bound"),
            }),
            (BoundSide::Upper, true) => Err(CertificateError::MalformedModel {
                index,
                msg: format!("row {row} has -inf upper bound"),
            }),
        };
    }
    match side {
        BoundSide::Lower => model.row_lb_exact(row, bound),
        BoundSide::Upper => model.row_ub_exact(row, bound),
    }
    .ok_or(CertificateError::InfiniteBound { index })
}

fn row_bound_exact_small(
    model: &Model,
    row: usize,
    bound: f64,
    side: BoundSide,
    index: usize,
) -> Result<Rational, CertificateError> {
    if bound.is_nan() {
        return Err(CertificateError::MalformedModel {
            index,
            msg: format!("row {row} has a NaN bound"),
        });
    }
    if !bound.is_finite() {
        return match (side, bound.is_sign_negative()) {
            (BoundSide::Lower, true) | (BoundSide::Upper, false) => {
                Err(CertificateError::InfiniteBound { index })
            }
            (BoundSide::Lower, false) => Err(CertificateError::MalformedModel {
                index,
                msg: format!("row {row} has +inf lower bound"),
            }),
            (BoundSide::Upper, true) => Err(CertificateError::MalformedModel {
                index,
                msg: format!("row {row} has -inf upper bound"),
            }),
        };
    }
    match side {
        BoundSide::Lower => model.row_lb_exact_small(row, bound),
        BoundSide::Upper => model.row_ub_exact_small(row, bound),
    }
    .ok_or(CertificateError::InfiniteBound { index })
}

/// `BigRational` column-bound extraction, reached only from
/// [`combine_bounded_big_reference`]. Production uses [`bound_exact_small`].
fn bound_exact(
    bound: f64,
    side: BoundSide,
    index: usize,
    what: &'static str,
) -> Result<BigRational, CertificateError> {
    if bound.is_nan() {
        return Err(CertificateError::MalformedModel {
            index,
            msg: format!("{what} is NaN"),
        });
    }
    if !bound.is_finite() {
        return match (side, bound.is_sign_negative()) {
            (BoundSide::Lower, true) | (BoundSide::Upper, false) => {
                Err(CertificateError::InfiniteBound { index })
            }
            _ => Err(CertificateError::MalformedModel {
                index,
                msg: format!("{what} has the wrong infinite sign"),
            }),
        };
    }
    exact(bound).ok_or(CertificateError::InfiniteBound { index })
}

fn bound_exact_small(
    bound: f64,
    side: BoundSide,
    index: usize,
    what: &'static str,
) -> Result<Rational, CertificateError> {
    if bound.is_nan() {
        return Err(CertificateError::MalformedModel {
            index,
            msg: format!("{what} is NaN"),
        });
    }
    if !bound.is_finite() {
        return match (side, bound.is_sign_negative()) {
            (BoundSide::Lower, true) | (BoundSide::Upper, false) => {
                Err(CertificateError::InfiniteBound { index })
            }
            _ => Err(CertificateError::MalformedModel {
                index,
                msg: format!("{what} has the wrong infinite sign"),
            }),
        };
    }
    crate::model::exact_small(bound).ok_or(CertificateError::InfiniteBound { index })
}

/// Pre-fast-path `BigRational` combination, retained only as a differential
/// oracle: [`combine_bounded`] must reproduce it in every rational slot, or
/// decline for the same reason.
///
/// Kept `pub(crate)` and unexported. Its callers are the `#[cfg(test)]`
/// agreement check below and the [`crate::certify::sealed_scale`]
/// characterization.
pub(crate) fn combine_bounded_big_reference(
    multipliers: &[Multiplier],
    model: &Model,
    col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
) -> Result<(Vec<BigRational>, BigRational), CertificateError> {
    if let Some((lbs, ubs)) = col_bounds {
        let expected = model.num_cols();
        if lbs.len() != expected || ubs.len() != expected {
            return Err(CertificateError::MalformedBoundOverride {
                expected,
                lower: lbs.len(),
                upper: ubs.len(),
            });
        }
    }

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
                let bound = match side {
                    BoundSide::Lower => row_bound_exact(model, row.index(), lb, side, index)?,
                    BoundSide::Upper => row_bound_exact(model, row.index(), ub, side, index)?,
                };
                let sign_pos = matches!(side, BoundSide::Lower);
                for &(c, a) in row_coeffs {
                    if c as usize >= model.num_cols() {
                        return Err(CertificateError::MalformedModel {
                            index,
                            msg: format!("row {} references missing column {c}", row.index()),
                        });
                    }
                    if !a.is_finite() {
                        return Err(CertificateError::MalformedModel {
                            index,
                            msg: format!(
                                "row {} has a non-finite coefficient at column {c}",
                                row.index()
                            ),
                        });
                    }
                    let term = &m.coeff * model.row_coeff_exact(row.index(), c, a);
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
                    Some((lbs, ubs)) => {
                        let slot = match side {
                            BoundSide::Lower => lbs.get(col.index()),
                            BoundSide::Upper => ubs.get(col.index()),
                        }
                        .ok_or(CertificateError::MissingFact { index })?;
                        slot.clone()
                            .ok_or(CertificateError::InfiniteBound { index })
                    }
                    None => {
                        let (lb, ub) = model.col_bounds(col);
                        match side {
                            BoundSide::Lower => bound_exact(lb, side, index, "column lower bound"),
                            BoundSide::Upper => bound_exact(ub, side, index, "column upper bound"),
                        }
                    }
                }?;
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
    Ok((coeffs, constant))
}

/// Run the production inline accumulator while preserving its `Rational`
/// outputs. The [`crate::certify::sealed_scale`] characterization converts them
/// to `BigRational` only after stopping its Combination timer.
pub(crate) fn combine_bounded_fast_for_benchmark(
    multipliers: &[Multiplier],
    model: &Model,
    col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
) -> Result<(Vec<Rational>, Rational), CertificateError> {
    let combination = combine_bounded(multipliers, model, col_bounds)?;
    Ok((combination.coeffs, combination.constant))
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    use super::*;

    fn row_multiplier(row: Row) -> Multiplier {
        Multiplier {
            fact: FactRef::RowBound {
                row,
                side: BoundSide::Upper,
            },
            coeff: BigRational::one(),
        }
    }

    fn col_multiplier(col: Col, side: BoundSide) -> Multiplier {
        Multiplier {
            fact: FactRef::ColBound { col, side },
            coeff: BigRational::one(),
        }
    }

    /// The forgery from the design review, built as a MUST-REJECT.
    ///
    /// `x in [0,10]` integer, `y` continuous in `[0,10]`, row `y - x <= 0`,
    /// minimise `-y`. The true optimum is `-10` at `x = y = 10`. On the SHRUNKEN
    /// box `x in [0,0]` the row forces `y <= 0`, so `-y >= 0` really is provable
    /// — and a certificate that RECORDED that box would verify while the model's
    /// optimum is `-10`.
    ///
    /// `verify_bound_leaf` takes the box as a PARAMETER precisely so this cannot
    /// happen: the same multipliers must be rejected when priced at the model's
    /// own bounds. If this test ever passes on the true box, the design is
    /// forgeable.
    fn forgery_model() -> (Model, Vec<Multiplier>) {
        let mut model = Model::new();
        let x = model.add_col(0.0, 10.0);
        let y = model.add_col(0.0, 10.0);
        model.cols[x.index()].obj = 0.0;
        model.cols[y.index()].obj = -1.0;
        // y - x <= 0
        let row = model.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (x, -1.0)]);
        // -y >= 0  follows from  (y - x <= 0)  plus  (x <= 0):
        //   1*(y - x <= 0) + 1*(x <= 0)  =>  y <= 0  =>  -y >= 0
        let mult = vec![row_multiplier(row), col_multiplier(x, BoundSide::Upper)];
        (model, mult)
    }

    #[test]
    fn a_bound_leaf_cannot_forge_optimality_by_shrinking_the_box() {
        let (model, mult) = forgery_model();
        let n = model.num_cols();
        let zero = BigRational::zero();

        // The forger's box: x pinned to 0. Here the multipliers DO prove
        // `objective >= 0`, which is the whole danger.
        let mut lb = vec![Some(BigRational::zero()); n];
        let mut ub = vec![Some(BigRational::from_integer(BigInt::from(10))); n];
        ub[0] = Some(BigRational::zero());
        assert!(
            OptimalityCertificate::verify_bound_leaf(&mult, &model, &lb, &ub, &zero).is_ok(),
            "the shrunken box must really admit the proof -- otherwise this test \
             is not exercising the forgery it claims to"
        );

        // The model's OWN box, which is what a verifier reconstructs. The same
        // multipliers must now fail: `x <= 10` cannot force `y <= 0`.
        lb[0] = Some(BigRational::zero());
        ub[0] = Some(BigRational::from_integer(BigInt::from(10)));
        let priced_at_truth =
            OptimalityCertificate::verify_bound_leaf(&mult, &model, &lb, &ub, &zero);
        assert!(
            priced_at_truth.is_err(),
            "FORGEABLE: multipliers valid only on a shrunken box were accepted at \
             the model's true bounds -- the box must never come from the certificate"
        );
    }

    #[test]
    fn a_bound_leaf_applies_the_objective_offset() {
        // Offset is the difference between the multiplier algebra's frame and
        // `Outcome::Optimal.value`. With offset -100, a linear bound of 0 means
        // the region's true objective is bounded by -100, which does NOT dominate
        // z* = 0.
        let (mut model, mult) = forgery_model();
        let n = model.num_cols();
        let lb = vec![Some(BigRational::zero()); n];
        let mut ub = vec![Some(BigRational::from_integer(BigInt::from(10))); n];
        ub[0] = Some(BigRational::zero());
        let zero = BigRational::zero();
        assert!(OptimalityCertificate::verify_bound_leaf(&mult, &model, &lb, &ub, &zero).is_ok());

        model.set_objective_offset(-100.0);
        assert!(
            OptimalityCertificate::verify_bound_leaf(&mult, &model, &lb, &ub, &zero).is_err(),
            "an offset of -100 drops the region's objective to -100 and must no \
             longer dominate z* = 0"
        );
    }

    #[test]
    fn a_bound_leaf_accepts_a_bound_strictly_STRONGER_than_z_star() {
        // A standalone OptimalityCertificate checks its bound for EQUALITY. A
        // leaf only has to DOMINATE z*, so proving more than required must pass.
        let (model, mult) = forgery_model();
        let n = model.num_cols();
        let lb = vec![Some(BigRational::zero()); n];
        let mut ub = vec![Some(BigRational::from_integer(BigInt::from(10))); n];
        ub[0] = Some(BigRational::zero());
        let weaker = BigRational::from_integer(BigInt::from(-5));
        assert!(
            OptimalityCertificate::verify_bound_leaf(&mult, &model, &lb, &ub, &weaker).is_ok(),
            "a leaf proving objective >= 0 must dominate z* = -5"
        );
        let stronger = BigRational::one();
        assert!(
            OptimalityCertificate::verify_bound_leaf(&mult, &model, &lb, &ub, &stronger).is_err(),
            "a leaf proving only objective >= 0 must NOT dominate z* = 1"
        );
    }

    fn model_with_malformed_row_column() -> (Model, Row) {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let row = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        model.rows[row.index()].coeffs[0].0 = 1;
        (model, row)
    }

    fn assert_combination_matches_big_reference(
        multipliers: &[Multiplier],
        model: &Model,
        col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
    ) {
        let fast = combine_bounded(multipliers, model, col_bounds);
        let reference = combine_bounded_big_reference(multipliers, model, col_bounds);
        match (fast, reference) {
            (Ok(fast), Ok((coeffs, constant))) => {
                assert_eq!(
                    fast.coeffs.iter().map(Rational::to_big).collect::<Vec<_>>(),
                    coeffs
                );
                assert_eq!(fast.constant.to_big(), constant);
            }
            (Err(fast), Err(reference)) => assert_eq!(fast, reference),
            _ => panic!("inline and BigRational combination paths diverged"),
        }
    }

    #[test]
    fn inline_combination_matches_big_reference_across_promotion_and_overrides() {
        let mut state = 0x243f_6a88_85a3_08d3_u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };

        for case in 0..100 {
            let mut model = Model::new();
            let cols: Vec<Col> = (0..5).map(|_| model.add_col(-7.0, 11.0)).collect();
            let mut rows = Vec::new();
            for r in 0..7 {
                let coeffs: Vec<(Col, f64)> = cols
                    .iter()
                    .enumerate()
                    .map(|(j, &col)| {
                        let sign = if next() & 1 == 0 { 1.0 } else { -1.0 };
                        let mantissa = ((next() % 31) + 1) as f64;
                        let exponent = -i32::try_from((next() % 100) + 1).unwrap();
                        let a = sign * mantissa * 2.0_f64.powi(exponent);
                        (
                            col,
                            if r == 0 && j == 0 && case % 5 == 0 {
                                f64::from_bits(1)
                            } else {
                                a
                            },
                        )
                    })
                    .collect();
                rows.push(model.add_row(-3.0, 4.0, &coeffs));
            }

            if case % 4 == 0 {
                let numerator = (BigInt::one() << (130 + case % 17)) + BigInt::from(5_u8);
                let denominator = (BigInt::one() << (70 + case % 11)) + BigInt::from(3_u8);
                let exact_coeff = BigRational::new(numerator, denominator);
                model.record_inexact_row_coeff(rows[0], cols[0].0, exact_coeff);
                model.record_inexact_row_bound(rows[0], true, BigRational::new(1.into(), 3.into()));
            }

            let mut multipliers = Vec::new();
            for (r, &row) in rows.iter().enumerate() {
                let coeff = if (case + r) % 3 == 0 {
                    BigRational::new(
                        (BigInt::one() << (90 + r)) + BigInt::from(1_u8),
                        (BigInt::one() << (65 + r)) + BigInt::from(3_u8),
                    )
                } else {
                    BigRational::new(((next() % 17) + 1).into(), ((next() % 13) + 1).into())
                };
                multipliers.push(Multiplier {
                    fact: FactRef::RowBound {
                        row,
                        side: if next() & 1 == 0 {
                            BoundSide::Lower
                        } else {
                            BoundSide::Upper
                        },
                    },
                    coeff,
                });
            }
            for (j, &col) in cols.iter().enumerate() {
                multipliers.push(Multiplier {
                    fact: FactRef::ColBound {
                        col,
                        side: if (case + j) % 2 == 0 {
                            BoundSide::Lower
                        } else {
                            BoundSide::Upper
                        },
                    },
                    coeff: BigRational::new(((next() % 29) + 1).into(), 1.into()),
                });
            }

            assert_combination_matches_big_reference(&multipliers, &model, None);
            let lbs: Vec<Option<BigRational>> = (0..cols.len())
                .map(|j| Some(BigRational::new((-14 + j as i64).into(), 2.into())))
                .collect();
            let ubs: Vec<Option<BigRational>> = (0..cols.len())
                .map(|j| Some(BigRational::new((22 - j as i64).into(), 2.into())))
                .collect();
            assert_combination_matches_big_reference(&multipliers, &model, Some((&lbs, &ubs)));
        }
    }

    #[test]
    fn branch_bound_override_length_mismatch_fails_closed() {
        let mut model = Model::new();
        let x = model.add_col(1.0, f64::INFINITY);
        let row = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        let cert = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::ColBound {
                        col: x,
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row,
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };

        assert_eq!(
            cert.verify_with_col_bounds(&model, &[], &[]),
            Err(CertificateError::MalformedBoundOverride {
                expected: 1,
                lower: 0,
                upper: 0
            })
        );
    }

    #[test]
    fn branch_bound_empty_box_certificate_verifies_with_overrides() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let cert = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::ColBound {
                        col: x,
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: x,
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };

        assert_eq!(
            cert.verify_with_col_bounds(
                &model,
                &[Some(BigRational::one())],
                &[Some(BigRational::zero())],
            ),
            Ok(())
        );
    }

    #[test]
    fn farkas_rejects_malformed_row_column_without_panicking() {
        let (model, row) = model_with_malformed_row_column();
        let cert = FarkasCertificate {
            multipliers: vec![row_multiplier(row)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn optimality_rejects_malformed_row_column_without_panicking() {
        let (model, row) = model_with_malformed_row_column();
        let cert = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, BigRational::zero())],
            bound: BigRational::zero(),
            multipliers: vec![row_multiplier(row)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn certified_row_rejects_malformed_row_column_without_panicking() {
        let (model, row) = model_with_malformed_row_column();
        let cert = CertifiedRow {
            coeffs: Vec::new(),
            lb: BigRational::zero(),
            multipliers: vec![row_multiplier(row)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn farkas_rejects_malformed_nonfinite_row_coefficient_without_panicking() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let row = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        model.rows[row.index()].coeffs[0].1 = f64::NAN;
        let cert = FarkasCertificate {
            multipliers: vec![row_multiplier(row)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn farkas_rejects_malformed_nan_row_bound_as_model_error() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let row = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        model.rows[row.index()].ub = f64::NAN;
        let cert = FarkasCertificate {
            multipliers: vec![row_multiplier(row)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn farkas_rejects_malformed_nan_column_bound_as_model_error() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.cols[x.index()].lb = f64::NAN;
        let cert = FarkasCertificate {
            multipliers: vec![col_multiplier(x, BoundSide::Lower)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn farkas_rejects_wrong_sign_infinite_row_bound_as_model_error() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let row = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        model.rows[row.index()].ub = f64::NEG_INFINITY;
        let cert = FarkasCertificate {
            multipliers: vec![row_multiplier(row)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn farkas_rejects_wrong_sign_infinite_column_bound_as_model_error() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.cols[x.index()].lb = f64::INFINITY;
        let cert = FarkasCertificate {
            multipliers: vec![col_multiplier(x, BoundSide::Lower)],
        };

        assert!(matches!(
            cert.verify(&model),
            Err(CertificateError::MalformedModel { .. })
        ));
    }

    #[test]
    fn valid_infinite_bound_side_still_reports_infinite_fact() {
        let mut model = Model::new();
        let x = model.add_col(f64::NEG_INFINITY, 1.0);
        let cert = FarkasCertificate {
            multipliers: vec![col_multiplier(x, BoundSide::Lower)],
        };

        assert_eq!(
            cert.verify(&model),
            Err(CertificateError::InfiniteBound { index: 0 })
        );
    }
}
