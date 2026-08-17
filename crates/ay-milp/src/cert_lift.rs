// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CERTIFICATE LIFTING: translating evidence proved against a REDUCED model
//! back into the caller's frame.
//!
//! # Why this module exists
//!
//! `ay` has three root model reductions — duplicate-column dedup, free /
//! implied-free singleton-column substitution, and the Aardal–Hurkens–Lenstra
//! kernel reformulation ([`crate::lattice::reformulate_kernel`]). All three
//! produce a model whose rows and columns are NOT the caller's, so a
//! certificate proved against the reduced model names facts the caller's model
//! does not have. The `expand_*` functions in `bab.rs` therefore either LIFT the
//! certificate through this module or STRIP it — stripping is safe (a verdict
//! without evidence is still a verdict) but it is a loss.
//!
//! HOW EACH REDUCTION RELATES TO THE CERTIFICATE LANE, exactly (the call site is
//! `bab::solve_milp`, and this list has been wrong in comments before — read the
//! gates, they are three consecutive `if`s):
//!
//! * NONE OF THE THREE is gated on `tree_cert_leaves` any more. KERNEL and DEDUP
//!   used to be (`if opts.tree_cert_leaves == 0` and `if opts.tree_cert_leaves == 0
//!   && dedup_enabled()`), and since that field defaults to 256 both were off on
//!   default options — two reductions surrendered for an artifact only an
//!   `Outcome::Infeasible` can carry. They now run unconditionally and the artifact
//!   is bought where it is possible: `bab::harvest_tree_cert_by_resolve` re-solves
//!   the CALLER's model once, with capture armed, on Infeasible + a declined lift.
//! * The TREE still does not survive the round trip for either of them — the
//!   kernel's splits are on `z` columns, which `TreeNode` cannot express at all
//!   (there is deliberately no `KernelPostsolve::lift_tree_cert`), and a dedup tree
//!   splits only KEPT columns, so [`DedupLift::lift_tree_cert`] closes a leaf only
//!   in the rare case it leans on lower bounds. What changed is the response to
//!   that: a re-solve instead of a forfeited reduction.
//! * SINGLETON substitution never was gated on `tree_cert_leaves`. Its only gate is
//!   `if singleton_sub_enabled()` (`the singleton-sub knob`, default OFF for a
//!   measured search regression that has nothing to do with certificates). It runs
//!   under ARMED capture and `expand_singleton_outcome` lifts the tree leaf by leaf,
//!   stripping only on a decline — so it needs no re-solve.
//!
//! Translating the certificate is still the FIRST answer, and it is what lets a
//! reduction and a certificate coexist with no second solve at all: every ROOT
//! certificate lifts here. This module is the shared frame for doing that, plus
//! the kernel reformulation's own lift. It is written so the singleton and
//! dedup lifts can reuse every piece.
//!
//! # The shape of every lift
//!
//! A certificate is a POSITIVE combination of oriented model facts
//! ([`crate::cert`]). A lift therefore has exactly three jobs:
//!
//! 1. **Re-name** each reduced fact as the original fact it IS. This is
//!    reduction-specific and it is the only step that needs the reduction's own
//!    bookkeeping.
//! 2. **Repair** whatever the reduced model dropped. A deleted row is a fact
//!    the reduced certificate could not cite and may still need; the repair is
//!    an exact rational solve for the missing multipliers
//!    ([`solve_row_combination`]).
//! 3. **Seal.** Re-verify the produced certificate against the ORIGINAL model
//!    with the real [`FarkasCertificate::verify`] /
//!    [`OptimalityCertificate::verify`] and return `None` if it does not pass
//!    ([`seal_farkas`], [`seal_optimality`]).
//!
//! Step 3 is the load-bearing one. Every lift here returns `Option`, every
//! `None` degrades to exactly today's behaviour (no certificate), and NO path
//! in this module constructs a returned certificate except through a `seal_*`
//! function. So a wrong lift cannot ship a wrong certificate; it can only fail
//! to ship one. That is the property to preserve when adding the next lift:
//! **never return a certificate you did not seal.**
//!
//! The seals are not a substitute for getting the algebra right — a lift that
//! declines every time is worthless — but they are what makes the algebra's
//! correctness a PERFORMANCE property rather than a soundness property.

use std::collections::BTreeMap;

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::cert::{BoundSide, FactRef, FarkasCertificate, Multiplier, OptimalityCertificate};
use crate::lattice::{KernelPostsolve, KernelRowOrigin};
use crate::model::{exact, Col, Model, Row, Sense};
use crate::presolve::{
    BinaryComplementPostsolve, BinaryComplementRowOrigin, BinaryComplementSide,
    ObjectiveSingletonPostsolve, ObjectiveSingletonRecovery, ObjectiveSingletonSide,
    SingletonPostsolve, SingletonRowOrigin,
};
use crate::tree_cert::{MilpInfeasibilityCertificate, TreeNode};

/// Solve `Σ_i mu_i · rows[i] = rhs` EXACTLY over ℚ, or return `None`.
///
/// `rows` is a list of `m` coefficient vectors, each of length `n = rhs.len()`;
/// the returned `mu` has length `m`. The system is `n` equations in `m`
/// unknowns and is usually both over- and under-determined: over-determined
/// because `n` is the whole column block and under-determined because the
/// deleted rows may be linearly dependent. Free unknowns are set to zero, which
/// is legitimate — ANY solution is a valid certificate, and the seal checks the
/// one we picked.
///
/// Inconsistency is a `None`, never a panic and never an approximate answer:
/// the caller's reduced identity is what implies solvability, and if that
/// implication is wrong (a corrupted reduced certificate, a reduction whose
/// algebra does not hold) then declining is the whole point.
///
/// The elimination is followed by an INDEPENDENT re-multiplication check, so a
/// bug in the elimination cannot propagate into a certificate: it can only turn
/// a lift into a decline.
pub(crate) fn solve_row_combination(
    rows: &[Vec<BigRational>],
    rhs: &[BigRational],
) -> Option<Vec<BigRational>> {
    let n = rhs.len();
    let m = rows.len();
    if rows.iter().any(|r| r.len() != n) {
        return None;
    }
    if m == 0 {
        return rhs.iter().all(Zero::is_zero).then(Vec::new);
    }

    // Augmented system, transposed: one equation per COLUMN of the block.
    let mut aug: Vec<Vec<BigRational>> = (0..n)
        .map(|j| {
            let mut eq: Vec<BigRational> = (0..m).map(|i| rows[i][j].clone()).collect();
            eq.push(rhs[j].clone());
            eq
        })
        .collect();

    let mut pivot_row_of: Vec<Option<usize>> = vec![None; m];
    let mut pivot = 0usize;
    for col in 0..m {
        if pivot == n {
            break;
        }
        let Some(found) = (pivot..n).find(|&r| !aug[r][col].is_zero()) else {
            continue;
        };
        aug.swap(pivot, found);
        let inverse_of = aug[pivot][col].clone();
        for k in col..=m {
            aug[pivot][k] = &aug[pivot][k] / &inverse_of;
        }
        for r in 0..n {
            if r == pivot || aug[r][col].is_zero() {
                continue;
            }
            let factor = aug[r][col].clone();
            for k in col..=m {
                let term = &aug[pivot][k] * &factor;
                aug[r][k] -= term;
            }
        }
        pivot_row_of[col] = Some(pivot);
        pivot += 1;
    }

    // Consistency: `0 = nonzero` anywhere means `rhs` is not in the row space.
    for eq in &aug {
        if eq[..m].iter().all(Zero::is_zero) && !eq[m].is_zero() {
            return None;
        }
    }

    let mu: Vec<BigRational> = (0..m)
        .map(|col| pivot_row_of[col].map_or_else(BigRational::zero, |r| aug[r][m].clone()))
        .collect();

    // Independent re-check of the solve, in the direction the caller needs it.
    for (j, want) in rhs.iter().enumerate() {
        let mut acc = BigRational::zero();
        for (i, mu_i) in mu.iter().enumerate() {
            if !mu_i.is_zero() && !rows[i][j].is_zero() {
                acc += mu_i * &rows[i][j];
            }
        }
        if acc != *want {
            return None;
        }
    }
    Some(mu)
}

/// SIGNED contributions to a lifted combination, on their way to becoming
/// contract-legal [`Multiplier`]s.
///
/// The certificate contract requires STRICTLY POSITIVE multipliers, but a
/// repair solve ([`solve_row_combination`]) returns signed rationals. A
/// negative contribution is representable exactly when the fact's OPPOSITE side
/// names the same linear form, i.e. when the row/column is an equality
/// (`lb == ub`): then `−c · (a·x − lb) = c · (ub − a·x)`. That is precisely the
/// case the deleted-equality repair lands in, and it is checked against the
/// MODEL rather than assumed — a negative contribution on a genuine range
/// bound declines.
#[derive(Debug, Default)]
pub(crate) struct SignedFacts {
    terms: Vec<(FactRef, BigRational)>,
}

impl SignedFacts {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record `coeff · fact`, with `coeff` of either sign.
    pub(crate) fn push(&mut self, fact: FactRef, coeff: BigRational) {
        self.terms.push((fact, coeff));
    }

    /// Emit contract-legal multipliers, or `None` if some sign cannot be
    /// represented. Exact zeros are DROPPED: a zero multiplier is rejected by
    /// `verify` as non-positive, and it contributes nothing, so carrying it
    /// would turn a correct lift into a rejected certificate.
    pub(crate) fn into_multipliers(self, model: &Model) -> Option<Vec<Multiplier>> {
        let mut out = Vec::with_capacity(self.terms.len());
        for (fact, coeff) in self.terms {
            if coeff.is_zero() {
                continue;
            }
            if coeff.is_positive() {
                out.push(Multiplier { fact, coeff });
                continue;
            }
            if !opposite_side_names_the_same_form(model, fact) {
                return None;
            }
            out.push(Multiplier {
                fact: flip_side(fact),
                coeff: -coeff,
            });
        }
        Some(out)
    }
}

/// True when the fact's two sides differ only in orientation, i.e. the bound is
/// an equality in EXACT arithmetic. Reads the exact side-store, so a model whose
/// `f64` bounds coincide only after rounding is refused.
fn opposite_side_names_the_same_form(model: &Model, fact: FactRef) -> bool {
    match fact {
        FactRef::RowBound { row, .. } => {
            if row.index() >= model.num_rows() {
                return false;
            }
            let (_, lb, ub) = model.row(row);
            if !lb.is_finite() || !ub.is_finite() {
                return false;
            }
            match (
                model.row_lb_exact(row.index(), lb),
                model.row_ub_exact(row.index(), ub),
            ) {
                (Some(l), Some(u)) => l == u,
                _ => false,
            }
        }
        FactRef::ColBound { col, .. } => {
            if col.index() >= model.num_cols() {
                return false;
            }
            let (lb, ub) = model.col_bounds(col);
            match (exact(lb), exact(ub)) {
                (Some(l), Some(u)) => l == u,
                _ => false,
            }
        }
    }
}

/// The same fact, other side.
fn flip_side(fact: FactRef) -> FactRef {
    let other = |side| match side {
        BoundSide::Lower => BoundSide::Upper,
        BoundSide::Upper => BoundSide::Lower,
    };
    match fact {
        FactRef::RowBound { row, side } => FactRef::RowBound {
            row,
            side: other(side),
        },
        FactRef::ColBound { col, side } => FactRef::ColBound {
            col,
            side: other(side),
        },
    }
}

/// The exact combined linear form `coeffs·x + constant` of `multipliers` over
/// `model`, so a lift can check its own work before returning. `None` for any
/// reason `verify` itself would reject the combination (non-positive
/// multiplier, infinite bound, missing fact, malformed model).
pub(crate) fn combination_over(
    multipliers: &[Multiplier],
    model: &Model,
) -> Option<(Vec<BigRational>, BigRational)> {
    combination_over_bounded(multipliers, model, None)
}

/// [`combination_over`] with the model's COLUMN bounds replaced by an exact
/// effective box (`None` entry = that side is infinite), i.e. priced exactly the
/// way [`FarkasCertificate::verify_with_col_bounds`] prices a TREE-certificate
/// leaf. A leaf lift must check its own work against the same box the leaf
/// verifier will use, or its residual is computed against bounds nobody applies.
pub(crate) fn combination_over_bounded(
    multipliers: &[Multiplier],
    model: &Model,
    col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
) -> Option<(Vec<BigRational>, BigRational)> {
    crate::cert::combine_bounded_big_reference(multipliers, model, col_bounds).ok()
}

/// Reduced column -> original column, inverted from a reduction's forward map
/// (`original -> Option<reduced>`).
///
/// Declines rather than guesses on anything that is not a clean injection: two
/// originals claiming one reduced column, or a reduced column index no original
/// maps to. Both mean the map is not the map this lift was written for.
pub(crate) fn reverse_column_map(map: &[Option<Col>]) -> Option<Vec<usize>> {
    let mut out: Vec<Option<usize>> = Vec::new();
    for (orig, slot) in map.iter().enumerate() {
        let Some(reduced) = slot else { continue };
        let index = reduced.index();
        if out.len() <= index {
            out.resize(index + 1, None);
        }
        if out[index].replace(orig).is_some() {
            return None;
        }
    }
    out.into_iter().collect()
}

/// The certificate objective naming the CALLER's model objective: sorted,
/// duplicate-free, exact, zeros omitted — the shape
/// [`OptimalityCertificate::verify`] accumulates against.
pub(crate) fn model_objective(model: &Model) -> Vec<(u32, BigRational)> {
    (0..model.num_cols())
        .filter_map(|j| {
            let a = model.obj_coeff(Col(j as u32));
            (a != 0.0).then(|| (j as u32, model.obj_coeff_exact_at(j as u32, a)))
        })
        .collect()
}

/// The coefficient vector `verify` requires of an optimality combination over
/// the CALLER's columns: `+objective` for Minimize, `−objective` for Maximize.
pub(crate) fn optimality_target(model: &Model, sense: Sense) -> Vec<BigRational> {
    let sigma_positive = matches!(sense, Sense::Minimize);
    (0..model.num_cols())
        .map(|j| {
            let a = model.obj_coeff(Col(j as u32));
            let c = if a == 0.0 {
                BigRational::zero()
            } else {
                model.obj_coeff_exact_at(j as u32, a)
            };
            if sigma_positive {
                c
            } else {
                -c
            }
        })
        .collect()
}

/// True when a certificate's claimed objective is, as an ACCUMULATED vector,
/// the one a reduction induces. The certificate contract only requires the list
/// to be sorted and duplicate-free, and `verify` itself accumulates, so the
/// comparison has to accumulate too.
fn claims_the_objective(
    claimed: &[(u32, BigRational)],
    induced: &BTreeMap<u32, BigRational>,
) -> bool {
    let mut acc: BTreeMap<u32, BigRational> = BTreeMap::new();
    for (c, a) in claimed {
        *acc.entry(*c).or_insert_with(BigRational::zero) += a;
    }
    acc.retain(|_, v| !v.is_zero());
    let mut want = induced.clone();
    want.retain(|_, v| !v.is_zero());
    acc == want
}

/// THE SEAL for an infeasibility lift: build the certificate and re-verify it
/// against the caller's own model with the real verifier. The only way this
/// module returns a [`FarkasCertificate`].
pub(crate) fn seal_farkas(
    multipliers: Vec<Multiplier>,
    original: &Model,
) -> Option<FarkasCertificate> {
    let cert = FarkasCertificate { multipliers };
    cert.verify(original).ok()?;
    Some(cert)
}

/// THE SEAL for a dual-bound lift. The only way this module returns an
/// [`OptimalityCertificate`].
pub(crate) fn seal_optimality(
    sense: Sense,
    objective: Vec<(u32, BigRational)>,
    bound: BigRational,
    multipliers: Vec<Multiplier>,
    original: &Model,
) -> Option<OptimalityCertificate> {
    let cert = OptimalityCertificate {
        sense,
        objective,
        bound,
        multipliers,
    };
    cert.verify(original).ok()?;
    Some(cert)
}

/// THE SEAL for a whole-tree infeasibility lift: build the certificate and
/// re-verify it against the caller's own model with the real
/// [`MilpInfeasibilityCertificate::verify`], which re-walks the split tree,
/// re-checks integrality and integer cuts at every split, and re-prices every
/// leaf's Farkas combination at that leaf's accumulated exact box. The only way
/// this module returns a [`MilpInfeasibilityCertificate`].
pub(crate) fn seal_tree(root: TreeNode, original: &Model) -> Option<MilpInfeasibilityCertificate> {
    let cert = MilpInfeasibilityCertificate { root };
    cert.verify(original).ok()?;
    Some(cert)
}

/// Depth beyond which a tree lift declines rather than recurses further.
///
/// The trees this walks are the engine's own (bounded by
/// `SolveOpts::tree_cert_leaves`, 256 by default), not attacker data, so this
/// never binds in practice — but a lift must not be the thing that turns a
/// pathological capture into a stack overflow, and declining costs only
/// evidence.
const MAX_TREE_LIFT_DEPTH: usize = 4096;

/// A reduction whose reduced COLUMNS are a renaming of a subset of the
/// caller's, so a branch-and-bound TREE proved against it transfers: every
/// split names a column the caller also has, at the same integer cut, and the
/// two branches still cover the caller's integer domain.
///
/// This is exactly the property the kernel reformulation does NOT have — its
/// splits are on `z` columns, and `z_t <= k` pulled back through `x_C = x_p +
/// B z` is a general lattice disjunction that [`TreeNode`] cannot express — so
/// [`KernelPostsolve`] deliberately does not implement it.
pub(crate) trait ReducedFrame {
    /// The caller-frame column a reduced column names, or `None` to decline the
    /// whole lift.
    fn original_col(&self, reduced: Col) -> Option<Col>;

    /// Lift ONE leaf's Farkas certificate, priced at the caller-frame effective
    /// column box `lb`/`ub` (`None` entry = that side is infinite) that the leaf
    /// sits under. Must itself be sealed with
    /// [`FarkasCertificate::verify_with_col_bounds`] against `original`.
    fn lift_leaf(
        &self,
        leaf: &FarkasCertificate,
        original: &Model,
        lb: &[Option<BigRational>],
        ub: &[Option<BigRational>],
    ) -> Option<FarkasCertificate>;
}

/// Lift a whole-tree infeasibility certificate proved against a REDUCED model
/// into the caller's frame, or `None`.
///
/// The skeleton is re-named split by split while the caller-frame effective box
/// is carried down exactly as [`MilpInfeasibilityCertificate::verify`] carries
/// it — model bounds intersected with the accumulated tightenings — so each
/// leaf is lifted against the same box its verifier will use. The seal is the
/// real whole-tree verifier.
pub(crate) fn lift_tree(
    reduced: &MilpInfeasibilityCertificate,
    original: &Model,
    frame: &impl ReducedFrame,
) -> Option<MilpInfeasibilityCertificate> {
    let n = original.num_cols();
    let mut lb: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(original.col_bounds(Col(j as u32)).0))
        .collect();
    let mut ub: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(original.col_bounds(Col(j as u32)).1))
        .collect();
    let root = lift_tree_node(&reduced.root, original, frame, &mut lb, &mut ub, 0)?;
    seal_tree(root, original)
}

/// One node of [`lift_tree`]'s walk. `lb`/`ub` are mutated in place for the
/// subtree and restored before returning, INCLUDING on the decline paths — a
/// leaked tightening would price a sibling's leaf at a box it does not live
/// under.
fn lift_tree_node(
    node: &TreeNode,
    original: &Model,
    frame: &impl ReducedFrame,
    lb: &mut [Option<BigRational>],
    ub: &mut [Option<BigRational>],
    depth: usize,
) -> Option<TreeNode> {
    if depth > MAX_TREE_LIFT_DEPTH {
        return None;
    }
    match node {
        TreeNode::Leaf { farkas } => Some(TreeNode::Leaf {
            farkas: frame.lift_leaf(farkas, original, lb, ub)?,
        }),
        TreeNode::Split { col, cut, lo, hi } => {
            let col = frame.original_col(*col)?;
            let j = col.index();
            if j >= lb.len() {
                return None;
            }

            let saved_ub = ub[j].clone();
            ub[j] = Some(match &saved_ub {
                Some(u) => u.clone().min(cut.clone()),
                None => cut.clone(),
            });
            let lo_lifted = lift_tree_node(lo, original, frame, lb, ub, depth + 1);
            ub[j] = saved_ub;
            let lo_lifted = lo_lifted?;

            let hi_cut = cut + BigRational::one();
            let saved_lb = lb[j].clone();
            lb[j] = Some(match &saved_lb {
                Some(l) => l.clone().max(hi_cut),
                None => hi_cut,
            });
            let hi_lifted = lift_tree_node(hi, original, frame, lb, ub, depth + 1);
            lb[j] = saved_lb;
            let hi_lifted = hi_lifted?;

            Some(TreeNode::Split {
                col,
                cut: cut.clone(),
                lo: Box::new(lo_lifted),
                hi: Box::new(hi_lifted),
            })
        }
    }
}

// ---------------------------------------------------------------------------
// The kernel reformulation's lift.
// ---------------------------------------------------------------------------

impl KernelPostsolve {
    /// Lift a Farkas certificate proved against the KERNEL-REFORMULATED model
    /// into the caller's frame, or `None`.
    ///
    /// See [`Self::lift_multipliers`] for the algebra; the Farkas target is
    /// simply "every original coefficient over `C` is zero", which together
    /// with the reduced certificate's own zero coefficients is the whole
    /// contradiction.
    pub(crate) fn lift_farkas(
        &self,
        reduced: &FarkasCertificate,
        original: &Model,
    ) -> Option<FarkasCertificate> {
        let want_c = vec![BigRational::zero(); self.cols_c.len()];
        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want_c)?;
        seal_farkas(multipliers, original)
    }

    /// Lift an optimality certificate proved against the KERNEL-REFORMULATED
    /// model into the caller's frame, or `None`.
    ///
    /// # What the bound means on each side
    ///
    /// The reduced objective is `c_C·x_C + c_R·x_R = const_delta + (c_C·B)·z +
    /// c_R·x_R`, so a reduced dual bound `beta` on the reduced LINEAR FORM
    /// bounds the caller's linear form at `beta + const_delta`. Certificates
    /// exclude the model's objective OFFSET on both sides (the reduced model
    /// carries the caller's offset verbatim), so the offset does not appear
    /// here at all — only `const_delta`, which is the part the SUBSTITUTION
    /// folded out.
    ///
    /// # Why the objective must match
    ///
    /// An [`OptimalityCertificate`] names its own objective, and nothing forces
    /// that to be the reduced MODEL's objective — `tighten_col_bounds` proves
    /// per-column objectives with the same type. A reduced objective with an
    /// arbitrary `z` part corresponds to many different caller-frame
    /// objectives (any `w` with `B^T w = g`), each with its own bound, so
    /// lifting it would be inventing a claim the caller did not ask for. This
    /// lift therefore handles the case that actually arises — the reduced
    /// model's own objective, induced by the reformulation from the caller's —
    /// and DECLINES anything else.
    pub(crate) fn lift_optimality(
        &self,
        reduced: &OptimalityCertificate,
        original: &Model,
    ) -> Option<OptimalityCertificate> {
        if original.num_cols() != self.n_orig || reduced.sense != original.sense() {
            return None;
        }
        if !self.objective_is_the_induced_one(&reduced.objective, original) {
            return None;
        }

        // `verify` checks `Σ multipliers == sigma·objective − ...`, so the
        // coefficient target over `C` carries the sense's sign.
        let sigma_positive = matches!(reduced.sense, Sense::Minimize);
        let objective: Vec<(u32, BigRational)> = (0..self.n_orig)
            .filter_map(|j| {
                let a = original.obj_coeff(Col(j as u32));
                (a != 0.0).then(|| (j as u32, original.obj_coeff_exact_at(j as u32, a)))
            })
            .collect();
        let want_c: Vec<BigRational> = self
            .cols_c
            .iter()
            .map(|&j| {
                let a = original.obj_coeff(Col(j as u32));
                let c = if a == 0.0 {
                    BigRational::zero()
                } else {
                    original.obj_coeff_exact_at(j as u32, a)
                };
                if sigma_positive {
                    c
                } else {
                    -c
                }
            })
            .collect();

        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want_c)?;
        let bound = &reduced.bound + &self.const_delta;
        seal_optimality(reduced.sense, objective, bound, multipliers, original)
    }

    /// THE ALGEBRA. Translate `reduced` multipliers into caller-frame
    /// multipliers whose combination has coefficient `want_c[p]` on
    /// `cols_c[p]`, or `None`.
    ///
    /// # (1) A folded row lifts 1:1
    ///
    /// A surviving reduced row is the original row with `x_C = x_p + B z`
    /// substituted. Evaluated at a feasible point it IS the original row's
    /// fact, on the same side, so its multiplier moves across unchanged.
    ///
    /// # (2) A bound row lifts to the column bound it encodes
    ///
    /// The reduced row for `j ∈ C` is `lo_j − x_p[p] ≤ B_p·z ≤ up_j − x_p[p]`.
    /// Its lower side is `B_p·z − lo_j + x_p[p] = x_j − lo_j`, its upper side
    /// `up_j − x_j`. So it lifts to the ORIGINAL column bound, same side, same
    /// coefficient. (A side that was infinite produced no row bound, so it
    /// cannot be cited.)
    ///
    /// # (3) A `z` column bound cannot occur
    ///
    /// The `z` columns are FREE on both sides by construction — that is the
    /// property the whole reformulation rests on — so no such fact exists.
    /// This is ASSERTED, not assumed: one appearing means the reduced model is
    /// not the model this postsolve describes, and the lift declines.
    ///
    /// # (4) The deleted equalities are RECOVERABLE
    ///
    /// The reduced certificate carries no multiplier for the rows `E` that were
    /// folded away, and in general it needs them. They are not lost. Write `L`
    /// for the combination of (1)+(2) as a form over the ORIGINAL columns. The
    /// reduced identity says the reduced combination is a CONSTANT in `z`; since
    /// `L(x_p + B z) ` is that combination, `L`'s coefficient vector `r` over
    /// `C` satisfies `r·B = 0`, i.e. `r ⊥ ker(A_E)`, i.e. `r ∈ rowspace(A_E)`.
    /// So `A_E^T mu = want_c − r` is SOLVABLE, exactly, over the rationals
    /// ([`solve_row_combination`]).
    ///
    /// A negative `mu_i` is representable because an equality row has BOTH
    /// oriented sides: take the opposite side with `|mu_i|`
    /// ([`SignedFacts`]). Every emitted multiplier is therefore strictly
    /// positive, as the contract demands.
    ///
    /// # (5) The constant follows
    ///
    /// The reduced right-hand sides were shifted by `−R_C x_p` (rows) and
    /// `−x_p` (bound rows), and `mu·b = mu^T A x_p = (want_c − r)·x_p` restores
    /// exactly that much. Nothing here relies on that being re-derived
    /// correctly: the seal re-checks the constant with the real verifier.
    fn lift_multipliers(
        &self,
        reduced: &[Multiplier],
        original: &Model,
        want_c: &[BigRational],
    ) -> Option<Vec<Multiplier>> {
        if original.num_cols() != self.n_orig || want_c.len() != self.cols_c.len() {
            return None;
        }

        // Reduced column -> original column, for the columns that survived.
        let mut original_of_reduced: BTreeMap<usize, usize> = BTreeMap::new();
        for (orig, slot) in self.map.iter().enumerate() {
            if let Some(reduced_col) = slot {
                if original_of_reduced
                    .insert(reduced_col.index(), orig)
                    .is_some()
                {
                    return None; // two originals on one reduced column: not this map
                }
            }
        }

        let mut base: Vec<Multiplier> = Vec::with_capacity(reduced.len());
        for m in reduced {
            if !m.coeff.is_positive() {
                return None;
            }
            let fact = match m.fact {
                FactRef::RowBound { row, side } => match *self.reduced_rows.get(row.index())? {
                    // (1)
                    KernelRowOrigin::Folded(orig) => {
                        if orig >= original.num_rows() {
                            return None;
                        }
                        FactRef::RowBound {
                            row: Row(u32::try_from(orig).ok()?),
                            side,
                        }
                    }
                    // (2)
                    KernelRowOrigin::ColumnBound(col) => {
                        if col >= self.n_orig {
                            return None;
                        }
                        FactRef::ColBound {
                            col: Col(u32::try_from(col).ok()?),
                            side,
                        }
                    }
                },
                FactRef::ColBound { col, side } => {
                    // (3)
                    if self.z.contains(&col) {
                        return None;
                    }
                    let orig = *original_of_reduced.get(&col.index())?;
                    FactRef::ColBound {
                        col: Col(u32::try_from(orig).ok()?),
                        side,
                    }
                }
            };
            base.push(Multiplier {
                fact,
                coeff: m.coeff.clone(),
            });
        }

        // (4): the residual over `C`, and the equality multipliers that clear it.
        let (coeffs, _constant) = combination_over(&base, original)?;
        let mut need = Vec::with_capacity(self.cols_c.len());
        for (p, &j) in self.cols_c.iter().enumerate() {
            need.push(&want_c[p] - coeffs.get(j)?);
        }
        let a_e = self.equality_matrix(original)?;
        let mu = solve_row_combination(&a_e, &need)?;

        let mut signed = SignedFacts::new();
        for (i, &row) in self.e_rows.iter().enumerate() {
            signed.push(
                FactRef::RowBound {
                    row: Row(u32::try_from(row).ok()?),
                    side: BoundSide::Lower,
                },
                mu[i].clone(),
            );
        }
        let mut out = base;
        out.extend(signed.into_multipliers(original)?);
        Some(out)
    }

    /// The deleted equality system `A_E` restricted to `C`, read back out of
    /// the ORIGINAL model in exact rationals — deliberately re-read rather than
    /// cached, so the multipliers this produces are multipliers of the rows the
    /// VERIFIER will price, not of a remembered copy of them.
    ///
    /// Declines if a row of `E` is missing, is not an exact equality, or
    /// touches a column outside `C` (none of which the reformulation's gate
    /// admits — this is a fail-closed re-check of that gate, not a new claim).
    fn equality_matrix(&self, original: &Model) -> Option<Vec<Vec<BigRational>>> {
        let mut position = vec![usize::MAX; self.n_orig];
        for (p, &j) in self.cols_c.iter().enumerate() {
            *position.get_mut(j)? = p;
        }
        let mut out = Vec::with_capacity(self.e_rows.len());
        for &i in &self.e_rows {
            if i >= original.num_rows() {
                return None;
            }
            let row = Row(u32::try_from(i).ok()?);
            let (coeffs, lb, ub) = original.row(row);
            if !lb.is_finite() || !ub.is_finite() {
                return None;
            }
            let (lo, up) = (original.row_lb_exact(i, lb)?, original.row_ub_exact(i, ub)?);
            if lo != up {
                return None;
            }
            let mut dense = vec![BigRational::zero(); self.cols_c.len()];
            for &(c, a) in coeffs {
                let p = *position.get(c as usize)?;
                if p == usize::MAX {
                    return None;
                }
                dense[p] += original.row_coeff_exact(i, c, a);
            }
            out.push(dense);
        }
        Some(out)
    }

    /// True when `objective` is exactly the reduced objective this
    /// reformulation induces from `original`'s: the caller's coefficients on
    /// the surviving columns, and `c_C·B_t` on each `z_t`.
    ///
    /// Compared as accumulated dense vectors, because the certificate's list is
    /// only required to be sorted and duplicate-free by its own contract and
    /// `verify` itself accumulates.
    fn objective_is_the_induced_one(
        &self,
        objective: &[(u32, BigRational)],
        original: &Model,
    ) -> bool {
        let mut induced: BTreeMap<u32, BigRational> = BTreeMap::new();
        for j in 0..self.n_orig {
            let a = original.obj_coeff(Col(j as u32));
            if a == 0.0 {
                continue;
            }
            let c = original.obj_coeff_exact_at(j as u32, a);
            match self.map.get(j).copied().flatten() {
                Some(reduced_col) => {
                    *induced
                        .entry(reduced_col.0)
                        .or_insert_with(BigRational::zero) += c;
                }
                None => {
                    let Some(p) = self.cols_c.iter().position(|&cj| cj == j) else {
                        return false;
                    };
                    for (t, bt) in self.basis.iter().enumerate() {
                        let Some(b) = bt.get(p) else {
                            return false;
                        };
                        if b.is_zero() {
                            continue;
                        }
                        let Some(z) = self.z.get(t) else {
                            return false;
                        };
                        *induced.entry(z.0).or_insert_with(BigRational::zero) += &c * b;
                    }
                }
            }
        }
        induced.retain(|_, v| !v.is_zero());

        let mut claimed: BTreeMap<u32, BigRational> = BTreeMap::new();
        for (c, a) in objective {
            *claimed.entry(*c).or_insert_with(BigRational::zero) += a;
        }
        claimed.retain(|_, v| !v.is_zero());

        induced == claimed
    }
}

// ---------------------------------------------------------------------------
// The singleton-column substitution's lift.
// ---------------------------------------------------------------------------

impl SingletonPostsolve {
    /// Lift a Farkas certificate proved against the SINGLETON-REDUCED model
    /// into the caller's frame, or `None`.
    ///
    /// The Farkas target is "every original coefficient is zero"; see
    /// [`Self::lift_multipliers`] for why the base translation already achieves
    /// that and the repair contributes nothing here.
    pub(crate) fn lift_farkas(
        &self,
        reduced: &FarkasCertificate,
        original: &Model,
    ) -> Option<FarkasCertificate> {
        let want = vec![BigRational::zero(); self.n_orig];
        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want, None)?;
        seal_farkas(multipliers, original)
    }

    /// Lift an optimality certificate proved against the SINGLETON-REDUCED
    /// model into the caller's frame, or `None`.
    ///
    /// # The bound
    ///
    /// The substitution folds `c_x·x = (c_x/a)·b − Σ_k (c_x·a_k/a)·z_k`, so the
    /// reduced linear form is the caller's MINUS the constant `const_delta =
    /// Σ_x c_x·b_x/a_x`. A reduced dual bound `beta` therefore bounds the
    /// caller's form at `beta + const_delta` — the same constant
    /// `expand_singleton_outcome` adds to the reported value, and, exactly as
    /// there, the model's objective OFFSET is not involved: certificates bound
    /// the pure linear form and the reduced model carries the caller's offset
    /// verbatim.
    ///
    /// # Why the objective must be the induced one
    ///
    /// A certificate names its own objective and nothing forces it to be the
    /// reduced MODEL's (`tighten_col_bounds` proves per-column objectives with
    /// the same type). A reduced objective that is not the fold of the caller's
    /// bounds a form over the survivors that corresponds to no single
    /// caller-frame objective — the eliminated columns' coefficients are free —
    /// so lifting it would be inventing a claim. This lift REPLAYS the fold
    /// from `recover` and declines anything else; the replay also has to
    /// reproduce `const_delta`, which is an independent check that the replay is
    /// the fold the reduction actually performed.
    pub(crate) fn lift_optimality(
        &self,
        reduced: &OptimalityCertificate,
        original: &Model,
    ) -> Option<OptimalityCertificate> {
        if original.num_cols() != self.n_orig || reduced.sense != original.sense() {
            return None;
        }
        let (induced, replayed_delta) = self.induced_objective(original)?;
        if replayed_delta != self.const_delta {
            return None;
        }
        if !claims_the_objective(&reduced.objective, &induced) {
            return None;
        }

        let want = optimality_target(original, reduced.sense);
        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want, None)?;
        let bound = &reduced.bound + &self.const_delta;
        seal_optimality(
            reduced.sense,
            model_objective(original),
            bound,
            multipliers,
            original,
        )
    }

    /// Lift a whole-tree infeasibility certificate proved against the
    /// SINGLETON-REDUCED model into the caller's frame, or `None`.
    ///
    /// The tree transfers because the reduction only ever eliminates
    /// CONTINUOUS columns: every splittable (integral) column survives, with
    /// its handle renamed and its box copied verbatim, so a split on a reduced
    /// column is literally a split on the caller's column at the same integer
    /// cut. The eliminated columns are never split on and keep their model
    /// bounds at every leaf — which is also the box the reduced model's forcing
    /// ranges were built from, so the two frames price the same facts the same
    /// way.
    pub(crate) fn lift_tree_cert(
        &self,
        reduced: &MilpInfeasibilityCertificate,
        original: &Model,
    ) -> Option<MilpInfeasibilityCertificate> {
        if original.num_cols() != self.n_orig {
            return None;
        }
        lift_tree(reduced, original, self)
    }

    /// THE ALGEBRA. Translate `reduced` multipliers into caller-frame
    /// multipliers whose combination has coefficient `want[j]` on original
    /// column `j`, priced at `col_bounds` when a leaf supplies one.
    ///
    /// # (1) A kept row lifts 1:1
    ///
    /// An eliminated column has degree 1, so it appears in NO row but its own
    /// defining equality. A [`SingletonRowOrigin::Kept`] reduced row therefore
    /// has the original row's coefficients over every column it mentions, and
    /// the reduction copies its two bounds verbatim: same fact, same side, same
    /// multiplier.
    ///
    /// # (2) A rebounded row lifts to the original equality PLUS a box fact
    ///
    /// When `x` was not implied-free its defining equality `a·x + Σ a_k z_k = b`
    /// became the forcing range that enforces `x ∈ [lo, up]` on the survivors.
    /// Writing the range's own two oriented facts out and substituting the
    /// equality gives, for `a > 0`,
    ///
    /// ```text
    ///   lower: Σ a_k z_k − (b − a·up) = a·(up − x) + (a·x + Σ a_k z_k − b)
    ///   upper: (b − a·lo) − Σ a_k z_k = a·(x − lo) + (b − a·x − Σ a_k z_k)
    /// ```
    ///
    /// i.e. `|a|` times ONE side of `x`'s original column bound plus the SAME
    /// side of the original equality row. For `a < 0` the two column sides
    /// swap. Both pieces are ordinary caller-frame facts with positive
    /// multipliers, and the side of `x`'s box that appears is exactly the side
    /// that made the range bound finite, so it exists whenever the reduced fact
    /// did.
    ///
    /// # (3) A surviving column bound lifts 1:1
    ///
    /// The reduction copies each survivor's box, so the fact is the same fact.
    ///
    /// # (4) The repair is the OBJECTIVE's, not the geometry's
    ///
    /// (1)-(3) reproduce the reduced combination exactly as a form over the
    /// original columns — zero on every eliminated column. For a FARKAS lift
    /// that is already the target (`want = 0`) and the repair is empty. For an
    /// OPTIMALITY lift the target is the caller's objective, which the fold
    /// moved off the eliminated columns, and the difference is recovered by
    /// solving `A_E^T mu = want − base` over the defining equalities
    /// ([`solve_row_combination`]). That system is solvable and in fact
    /// triangular on the eliminated coordinates: `mu_x = σ·c_x/a_x` is forced,
    /// because row `E_x` is the only one with a coefficient on `x`. A negative
    /// `mu` is representable on an equality by taking its opposite side
    /// ([`SignedFacts`]) — which is why the reduction's equality-only gate
    /// matters here and is re-checked against the MODEL in
    /// [`Self::equality_matrix`].
    fn lift_multipliers(
        &self,
        reduced: &[Multiplier],
        original: &Model,
        want: &[BigRational],
        col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
    ) -> Option<Vec<Multiplier>> {
        if original.num_cols() != self.n_orig
            || want.len() != self.n_orig
            || self.map.len() != self.n_orig
        {
            return None;
        }
        let reverse = reverse_column_map(&self.map)?;

        let mut base: Vec<Multiplier> = Vec::with_capacity(reduced.len() + 1);
        for m in reduced {
            if !m.coeff.is_positive() {
                return None;
            }
            match m.fact {
                FactRef::RowBound { row, side } => match *self.row_origin.get(row.index())? {
                    // (1)
                    SingletonRowOrigin::Kept(orig) => {
                        if orig >= original.num_rows() {
                            return None;
                        }
                        base.push(Multiplier {
                            fact: FactRef::RowBound {
                                row: Row(u32::try_from(orig).ok()?),
                                side,
                            },
                            coeff: m.coeff.clone(),
                        });
                    }
                    // (2)
                    SingletonRowOrigin::Rebound { orig, recover } => {
                        if orig >= original.num_rows() {
                            return None;
                        }
                        let rec = self.recover.get(recover)?;
                        // The two handles must agree, or `recover` indexes some
                        // other elimination and the coefficient below is not
                        // this row's.
                        if rec.row != orig || rec.a.is_zero() || rec.col >= self.n_orig {
                            return None;
                        }
                        let col_side = if matches!(side, BoundSide::Lower) == rec.a.is_positive() {
                            BoundSide::Upper
                        } else {
                            BoundSide::Lower
                        };
                        base.push(Multiplier {
                            fact: FactRef::RowBound {
                                row: Row(u32::try_from(orig).ok()?),
                                side,
                            },
                            coeff: m.coeff.clone(),
                        });
                        base.push(Multiplier {
                            fact: FactRef::ColBound {
                                col: Col(u32::try_from(rec.col).ok()?),
                                side: col_side,
                            },
                            coeff: &m.coeff * rec.a.abs(),
                        });
                    }
                },
                // (3)
                FactRef::ColBound { col, side } => {
                    let orig = *reverse.get(col.index())?;
                    base.push(Multiplier {
                        fact: FactRef::ColBound {
                            col: Col(u32::try_from(orig).ok()?),
                            side,
                        },
                        coeff: m.coeff.clone(),
                    });
                }
            }
        }

        // (4)
        let (coeffs, _constant) = combination_over_bounded(&base, original, col_bounds)?;
        let mut need = Vec::with_capacity(self.n_orig);
        for (j, target) in want.iter().enumerate() {
            need.push(target - coeffs.get(j)?);
        }
        if need.iter().all(Zero::is_zero) {
            return Some(base);
        }
        let a_e = self.equality_matrix(original)?;
        let mu = solve_row_combination(&a_e, &need)?;

        let mut signed = SignedFacts::new();
        for (i, rec) in self.recover.iter().enumerate() {
            signed.push(
                FactRef::RowBound {
                    row: Row(u32::try_from(rec.row).ok()?),
                    side: BoundSide::Lower,
                },
                mu.get(i)?.clone(),
            );
        }
        let mut out = base;
        out.extend(signed.into_multipliers(original)?);
        Some(out)
    }

    /// The defining equalities, dense over ALL original columns, read back out
    /// of the ORIGINAL model in exact rationals — deliberately re-read rather
    /// than reconstructed from `recover`, so the multipliers this produces are
    /// multipliers of the rows the VERIFIER will price.
    ///
    /// Declines if a defining row is missing or is not an exact equality. The
    /// reduction only ever selects equality rows, so this is a fail-closed
    /// re-check of its gate rather than a new claim — but it is the check that
    /// licenses [`SignedFacts`] to flip a negative multiplier onto the opposite
    /// side, so it is re-made against the model here.
    fn equality_matrix(&self, original: &Model) -> Option<Vec<Vec<BigRational>>> {
        let mut out = Vec::with_capacity(self.recover.len());
        for rec in &self.recover {
            if rec.row >= original.num_rows() {
                return None;
            }
            let row = Row(u32::try_from(rec.row).ok()?);
            let (coeffs, lb, ub) = original.row(row);
            if !lb.is_finite() || !ub.is_finite() {
                return None;
            }
            let (lo, up) = (
                original.row_lb_exact(rec.row, lb)?,
                original.row_ub_exact(rec.row, ub)?,
            );
            if lo != up {
                return None;
            }
            let mut dense = vec![BigRational::zero(); self.n_orig];
            for &(c, a) in coeffs {
                let slot = dense.get_mut(c as usize)?;
                *slot += original.row_coeff_exact(rec.row, c, a);
            }
            out.push(dense);
        }
        Some(out)
    }

    /// Replay the objective fold the reduction performed, returning the reduced
    /// model's induced objective (keyed by REDUCED column) and the constant it
    /// folded out.
    ///
    /// The replay is a literal re-run of `substitute_singletons`'s fold in
    /// `recover` order. It is well defined because an eliminated column has
    /// degree 1: it is never in another elimination's `rest`, so its cost is
    /// still the caller's when its own turn comes, and no fold ever writes a
    /// coefficient onto a column that later disappears. A leftover cost on an
    /// eliminated column would mean exactly that assumption failed, and
    /// declines.
    fn induced_objective(
        &self,
        original: &Model,
    ) -> Option<(BTreeMap<u32, BigRational>, BigRational)> {
        if original.num_cols() != self.n_orig {
            return None;
        }
        let mut obj: Vec<BigRational> = (0..self.n_orig)
            .map(|j| {
                let a = original.obj_coeff(Col(j as u32));
                original.obj_coeff_exact_at(j as u32, a)
            })
            .collect();
        let mut delta = BigRational::zero();
        for rec in &self.recover {
            if rec.a.is_zero() {
                return None;
            }
            let cx = obj.get(rec.col)?.clone();
            if cx.is_zero() {
                continue;
            }
            for (k, ak) in &rec.rest {
                let slot = obj.get_mut(*k)?;
                *slot -= &(&cx * ak) / &rec.a;
            }
            delta += &(&cx * &rec.b) / &rec.a;
            *obj.get_mut(rec.col)? = BigRational::zero();
        }

        let mut induced: BTreeMap<u32, BigRational> = BTreeMap::new();
        for (j, c) in obj.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let reduced = self.map.get(j).copied().flatten()?;
            *induced.entry(reduced.0).or_insert_with(BigRational::zero) += c;
        }
        Some((induced, delta))
    }
}

impl ReducedFrame for SingletonPostsolve {
    fn original_col(&self, reduced: Col) -> Option<Col> {
        let orig = *reverse_column_map(&self.map)?.get(reduced.index())?;
        Some(Col(u32::try_from(orig).ok()?))
    }

    fn lift_leaf(
        &self,
        leaf: &FarkasCertificate,
        original: &Model,
        lb: &[Option<BigRational>],
        ub: &[Option<BigRational>],
    ) -> Option<FarkasCertificate> {
        let want = vec![BigRational::zero(); self.n_orig];
        let multipliers =
            self.lift_multipliers(&leaf.multipliers, original, &want, Some((lb, ub)))?;
        // The leaf's own seal: the real verifier, at the real box. The whole
        // tree is sealed again in `seal_tree`.
        let cert = FarkasCertificate { multipliers };
        cert.verify_with_col_bounds(original, lb, ub).ok()?;
        Some(cert)
    }
}

// ---------------------------------------------------------------------------
// Binary equivalence/complement substitution's lift.
// ---------------------------------------------------------------------------

impl BinaryComplementPostsolve {
    /// Lift a reduced-frame contradiction through the exact affine binary map.
    pub(crate) fn lift_farkas(
        &self,
        reduced: &FarkasCertificate,
        original: &Model,
    ) -> Option<FarkasCertificate> {
        let want = vec![BigRational::zero(); self.n_orig];
        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want, None)?;
        seal_farkas(multipliers, original)
    }

    /// Lift a bound on the reduced objective to the caller's objective.
    ///
    /// Each complement substitution contributes `c_j` to `const_delta` and
    /// `-c_j` to its representative's coefficient, so the caller's linear form
    /// is the reduced one plus that exact constant.  The model objective offset
    /// remains present on both models and is deliberately not added here.
    pub(crate) fn lift_optimality(
        &self,
        reduced: &OptimalityCertificate,
        original: &Model,
    ) -> Option<OptimalityCertificate> {
        if original.num_cols() != self.n_orig || reduced.sense != original.sense() {
            return None;
        }
        let (induced, replayed_delta) = self.induced_objective(original)?;
        if replayed_delta != self.const_delta || !claims_the_objective(&reduced.objective, &induced)
        {
            return None;
        }
        let want = optimality_target(original, reduced.sense);
        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want, None)?;
        seal_optimality(
            reduced.sense,
            model_objective(original),
            &reduced.bound + &self.const_delta,
            multipliers,
            original,
        )
    }

    /// Lift a whole branch-and-bound refutation.
    ///
    /// Every reduced integral column is a literal surviving caller column.  A
    /// component representative remains binary with the same `[0,1]` box, so a
    /// split on it is the same split in both frames.  Eliminated component
    /// members are determined by equality rows and need no independent split.
    pub(crate) fn lift_tree_cert(
        &self,
        reduced: &MilpInfeasibilityCertificate,
        original: &Model,
    ) -> Option<MilpInfeasibilityCertificate> {
        if original.num_cols() != self.n_orig {
            return None;
        }
        lift_tree(reduced, original, self)
    }

    /// Translate reduced facts back to their original row/column facts, then
    /// repair the coefficient residual with the defining binary equalities.
    ///
    /// A folded row is not literally the original linear form: eliminated
    /// columns have been replaced by `x` or `1-x`, and its bound has moved by
    /// the same constant.  On the equality manifold the two facts are equal.
    /// Consequently their coefficient difference lies in the row space of the
    /// spanning forest of defining equalities.  [`solve_row_combination`] finds
    /// those multipliers exactly, and the final verifier seal checks both the
    /// coefficients and the constant against the caller's actual model.
    fn lift_multipliers(
        &self,
        reduced: &[Multiplier],
        original: &Model,
        want: &[BigRational],
        col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
    ) -> Option<Vec<Multiplier>> {
        if original.num_cols() != self.n_orig
            || want.len() != self.n_orig
            || self.map.len() != self.n_orig
        {
            return None;
        }
        let reverse = reverse_column_map(&self.map)?;
        let mut base = Vec::with_capacity(reduced.len() + self.defining_rows.len());
        for multiplier in reduced {
            if !multiplier.coeff.is_positive() {
                return None;
            }
            let fact = match multiplier.fact {
                FactRef::RowBound { row, side } => {
                    let BinaryComplementRowOrigin { lower, upper } =
                        *self.row_origin.get(row.index())?;
                    let origin = match side {
                        BoundSide::Lower => lower?,
                        BoundSide::Upper => upper?,
                    };
                    if origin.row >= original.num_rows() {
                        return None;
                    }
                    FactRef::RowBound {
                        row: Row(u32::try_from(origin.row).ok()?),
                        side: match origin.side {
                            BinaryComplementSide::Lower => BoundSide::Lower,
                            BinaryComplementSide::Upper => BoundSide::Upper,
                        },
                    }
                }
                FactRef::ColBound { col, side } => {
                    let original_col = *reverse.get(col.index())?;
                    FactRef::ColBound {
                        col: Col(u32::try_from(original_col).ok()?),
                        side,
                    }
                }
            };
            base.push(Multiplier {
                fact,
                coeff: multiplier.coeff.clone(),
            });
        }

        let (coefficients, _constant) = combination_over_bounded(&base, original, col_bounds)?;
        let need = want
            .iter()
            .enumerate()
            .map(|(j, target)| Some(target - coefficients.get(j)?))
            .collect::<Option<Vec<_>>>()?;
        if need.iter().all(Zero::is_zero) {
            return Some(base);
        }
        let equalities = self.equality_matrix(original)?;
        let repair = solve_row_combination(&equalities, &need)?;
        let mut signed = SignedFacts::new();
        for (&row, coefficient) in self.defining_rows.iter().zip(repair) {
            signed.push(
                FactRef::RowBound {
                    row: Row(u32::try_from(row).ok()?),
                    side: BoundSide::Lower,
                },
                coefficient,
            );
        }
        base.extend(signed.into_multipliers(original)?);
        Some(base)
    }

    /// Re-read the independent defining equations from the caller's model.
    fn equality_matrix(&self, original: &Model) -> Option<Vec<Vec<BigRational>>> {
        if self.defining_rows.len() != self.recover.len() {
            return None;
        }
        let mut out = Vec::with_capacity(self.defining_rows.len());
        for &row_index in &self.defining_rows {
            if row_index >= original.num_rows() {
                return None;
            }
            let row = Row(u32::try_from(row_index).ok()?);
            let (coeffs, lb, ub) = original.row(row);
            if !lb.is_finite() || !ub.is_finite() {
                return None;
            }
            if original.row_lb_exact(row_index, lb)? != original.row_ub_exact(row_index, ub)? {
                return None;
            }
            let mut dense = vec![BigRational::zero(); self.n_orig];
            for &(column, coefficient) in coeffs {
                *dense.get_mut(column as usize)? +=
                    original.row_coeff_exact(row_index, column, coefficient);
            }
            out.push(dense);
        }
        Some(out)
    }

    /// Replay the objective fold independently of the reduced model builder.
    fn induced_objective(
        &self,
        original: &Model,
    ) -> Option<(BTreeMap<u32, BigRational>, BigRational)> {
        if original.num_cols() != self.n_orig {
            return None;
        }
        let recovery: BTreeMap<usize, _> = self
            .recover
            .iter()
            .map(|entry| (entry.col, entry))
            .collect();
        if recovery.len() != self.recover.len() {
            return None;
        }
        let mut induced = BTreeMap::<u32, BigRational>::new();
        let mut delta = BigRational::zero();
        for j in 0..self.n_orig {
            let coefficient = original.obj_coeff(Col(j as u32));
            let coefficient = original.obj_coeff_exact_at(j as u32, coefficient);
            if coefficient.is_zero() {
                continue;
            }
            if let Some(reduced_col) = self.map.get(j).copied().flatten() {
                *induced
                    .entry(reduced_col.0)
                    .or_insert_with(BigRational::zero) += coefficient;
                continue;
            }
            let entry = *recovery.get(&j)?;
            let representative = self.map.get(entry.representative).copied().flatten()?;
            if entry.complement {
                delta += &coefficient;
                *induced
                    .entry(representative.0)
                    .or_insert_with(BigRational::zero) -= coefficient;
            } else {
                *induced
                    .entry(representative.0)
                    .or_insert_with(BigRational::zero) += coefficient;
            }
        }
        induced.retain(|_, coefficient| !coefficient.is_zero());
        Some((induced, delta))
    }
}

impl ReducedFrame for BinaryComplementPostsolve {
    fn original_col(&self, reduced: Col) -> Option<Col> {
        let original = *reverse_column_map(&self.map)?.get(reduced.index())?;
        Some(Col(u32::try_from(original).ok()?))
    }

    fn lift_leaf(
        &self,
        leaf: &FarkasCertificate,
        original: &Model,
        lb: &[Option<BigRational>],
        ub: &[Option<BigRational>],
    ) -> Option<FarkasCertificate> {
        let want = vec![BigRational::zero(); self.n_orig];
        let multipliers =
            self.lift_multipliers(&leaf.multipliers, original, &want, Some((lb, ub)))?;
        let certificate = FarkasCertificate { multipliers };
        certificate.verify_with_col_bounds(original, lb, ub).ok()?;
        Some(certificate)
    }
}

// ---------------------------------------------------------------------------
// Objective-driven continuous singleton substitution's lift.
// ---------------------------------------------------------------------------

impl ObjectiveSingletonPostsolve {
    pub(crate) fn lift_farkas(
        &self,
        reduced: &FarkasCertificate,
        original: &Model,
    ) -> Option<FarkasCertificate> {
        seal_farkas(
            self.map_multipliers(&reduced.multipliers, original)?,
            original,
        )
    }

    pub(crate) fn lift_optimality(
        &self,
        reduced: &OptimalityCertificate,
        original: &Model,
    ) -> Option<OptimalityCertificate> {
        if original.num_cols() != self.n_orig || reduced.sense != original.sense() {
            return None;
        }
        let (induced, replayed_delta) = self.induced_objective(original)?;
        if replayed_delta != self.const_delta || !claims_the_objective(&reduced.objective, &induced)
        {
            return None;
        }
        let mut multipliers = self.map_multipliers(&reduced.multipliers, original)?;
        for recovery in &self.recover {
            self.recovery_matches_original(recovery, original)?;
            let signed_coefficient = match reduced.sense {
                Sense::Minimize => recovery.objective_coeff.clone(),
                Sense::Maximize => -&recovery.objective_coeff,
            };
            let oriented_a = match recovery.side {
                ObjectiveSingletonSide::Lower => recovery.a.clone(),
                ObjectiveSingletonSide::Upper => -&recovery.a,
            };
            let coefficient = signed_coefficient / oriented_a;
            if !coefficient.is_positive() {
                return None;
            }
            multipliers.push(Multiplier {
                fact: FactRef::RowBound {
                    row: Row(u32::try_from(recovery.row).ok()?),
                    side: match recovery.side {
                        ObjectiveSingletonSide::Lower => BoundSide::Lower,
                        ObjectiveSingletonSide::Upper => BoundSide::Upper,
                    },
                },
                coeff: coefficient,
            });
        }
        seal_optimality(
            reduced.sense,
            model_objective(original),
            &reduced.bound + &self.const_delta,
            multipliers,
            original,
        )
    }

    pub(crate) fn lift_tree_cert(
        &self,
        reduced: &MilpInfeasibilityCertificate,
        original: &Model,
    ) -> Option<MilpInfeasibilityCertificate> {
        if original.num_cols() != self.n_orig {
            return None;
        }
        lift_tree(reduced, original, self)
    }

    fn map_multipliers(&self, reduced: &[Multiplier], original: &Model) -> Option<Vec<Multiplier>> {
        if original.num_cols() != self.n_orig || self.map.len() != self.n_orig {
            return None;
        }
        let reverse = reverse_column_map(&self.map)?;
        reduced
            .iter()
            .map(|multiplier| {
                if !multiplier.coeff.is_positive() {
                    return None;
                }
                let fact = match multiplier.fact {
                    FactRef::RowBound { row, side } => {
                        let original_row = *self.row_origin.get(row.index())?;
                        if original_row >= original.num_rows() {
                            return None;
                        }
                        FactRef::RowBound {
                            row: Row(u32::try_from(original_row).ok()?),
                            side,
                        }
                    }
                    FactRef::ColBound { col, side } => {
                        let original_col = *reverse.get(col.index())?;
                        FactRef::ColBound {
                            col: Col(u32::try_from(original_col).ok()?),
                            side,
                        }
                    }
                };
                Some(Multiplier {
                    fact,
                    coeff: multiplier.coeff.clone(),
                })
            })
            .collect()
    }

    fn recovery_matches_original(
        &self,
        recovery: &ObjectiveSingletonRecovery,
        original: &Model,
    ) -> Option<()> {
        if recovery.col >= self.n_orig || recovery.row >= original.num_rows() {
            return None;
        }
        let row = Row(u32::try_from(recovery.row).ok()?);
        let (coeffs, lower, upper) = original.row(row);
        let bound = match recovery.side {
            ObjectiveSingletonSide::Lower => original.row_lb_exact(recovery.row, lower),
            ObjectiveSingletonSide::Upper => original.row_ub_exact(recovery.row, upper),
        }?;
        if bound != recovery.b {
            return None;
        }
        let mut found = false;
        let mut rest = Vec::with_capacity(coeffs.len().saturating_sub(1));
        for &(column, coefficient) in coeffs {
            let coefficient = original.row_coeff_exact(recovery.row, column, coefficient);
            if column as usize == recovery.col {
                if found || coefficient != recovery.a {
                    return None;
                }
                found = true;
            } else {
                rest.push((column as usize, coefficient));
            }
        }
        (found && rest == recovery.rest).then_some(())
    }

    fn induced_objective(
        &self,
        original: &Model,
    ) -> Option<(BTreeMap<u32, BigRational>, BigRational)> {
        if original.num_cols() != self.n_orig {
            return None;
        }
        let mut objective = (0..self.n_orig)
            .map(|j| {
                let coefficient = original.obj_coeff(Col(j as u32));
                original.obj_coeff_exact_at(j as u32, coefficient)
            })
            .collect::<Vec<_>>();
        let mut delta = BigRational::zero();
        for recovery in &self.recover {
            self.recovery_matches_original(recovery, original)?;
            let coefficient = objective.get(recovery.col)?.clone();
            if coefficient != recovery.objective_coeff || recovery.a.is_zero() {
                return None;
            }
            for (column, row_coefficient) in &recovery.rest {
                *objective.get_mut(*column)? -= &(&coefficient * row_coefficient) / &recovery.a;
            }
            delta += &(&coefficient * &recovery.b) / &recovery.a;
            *objective.get_mut(recovery.col)? = BigRational::zero();
        }
        let mut induced = BTreeMap::new();
        for (original_col, coefficient) in objective.into_iter().enumerate() {
            if coefficient.is_zero() {
                continue;
            }
            let reduced_col = self.map.get(original_col).copied().flatten()?;
            *induced
                .entry(reduced_col.0)
                .or_insert_with(BigRational::zero) += coefficient;
        }
        induced.retain(|_, coefficient| !coefficient.is_zero());
        Some((induced, delta))
    }
}

impl ReducedFrame for ObjectiveSingletonPostsolve {
    fn original_col(&self, reduced: Col) -> Option<Col> {
        let original = *reverse_column_map(&self.map)?.get(reduced.index())?;
        Some(Col(u32::try_from(original).ok()?))
    }

    fn lift_leaf(
        &self,
        leaf: &FarkasCertificate,
        original: &Model,
        lb: &[Option<BigRational>],
        ub: &[Option<BigRational>],
    ) -> Option<FarkasCertificate> {
        let multipliers = self.map_multipliers(&leaf.multipliers, original)?;
        let certificate = FarkasCertificate { multipliers };
        certificate.verify_with_col_bounds(original, lb, ub).ok()?;
        Some(certificate)
    }
}

// ---------------------------------------------------------------------------
// The duplicate-column dedup's lift.
// ---------------------------------------------------------------------------

/// The lift for `bab::dedup_columns`, which keeps ONE column of each group of
/// interchangeable duplicates and drops the rest.
///
/// # What the reduced model is
///
/// Every row is copied, in order, with the same bounds and the same
/// coefficients on the kept columns — so a reduced ROW handle is already an
/// original row handle. Kept columns keep their own box and cost. The removed
/// columns simply vanish, which makes the reduced model the FACE `x_removed =
/// 0` of the caller's, and the merge's licence is combinatorial (each group's
/// shared support holds a partition row, so at most one member can be at 1),
/// not linear-algebraic.
///
/// # So what does a reduced certificate need?
///
/// The face is not the caller's polytope, and a combination that is a
/// contradiction (or a tight dual bound) on the face has, in the caller's
/// frame, a LEFTOVER coefficient on each removed column: the rows cannot tell
/// a removed column from its kept twin, so whatever the rows contribute to the
/// twin they contribute to it as well. The lift's whole job is to cancel that
/// leftover with the removed column's OWN box facts — which is what "distribute
/// the merged column's bound back over the originals it represents" comes to
/// once the reduction is read.
///
/// The distribution is not a choice: the residual is computed against the
/// model, one column at a time, and there is exactly one multiplier per column
/// that clears it. A POSITIVE residual is cleared by the removed column's lower
/// bound and (because that bound is 0 for every merged group) costs the
/// combination's constant nothing, so the lifted certificate keeps the reduced
/// one's bound exactly. A NEGATIVE residual needs the upper bound, which moves
/// the constant the wrong way; that lift is attempted anyway and the seal is
/// the judge, so it survives only where the slack it spends is slack the
/// combination had.
pub(crate) struct DedupLift<'a> {
    /// Original column -> kept reduced column, or `None` if the column was
    /// merged away. This is `dedup_columns`'s own map, borrowed.
    map: &'a [Option<Col>],
    /// Reduced column -> original column.
    reverse: Vec<usize>,
}

impl<'a> DedupLift<'a> {
    /// Build a lift over `dedup_columns`'s map, or `None` if the map is not a
    /// clean injection (see [`reverse_column_map`]).
    pub(crate) fn new(map: &'a [Option<Col>]) -> Option<Self> {
        let reverse = reverse_column_map(map)?;
        Some(Self { map, reverse })
    }

    /// Lift a Farkas certificate proved against the DEDUP-REDUCED model into
    /// the caller's frame, or `None`.
    pub(crate) fn lift_farkas(
        &self,
        reduced: &FarkasCertificate,
        original: &Model,
    ) -> Option<FarkasCertificate> {
        let want = vec![BigRational::zero(); self.map.len()];
        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want, None)?;
        seal_farkas(multipliers, original)
    }

    /// Lift an optimality certificate proved against the DEDUP-REDUCED model
    /// into the caller's frame, or `None`.
    ///
    /// The reduction folds no constant, so the claimed bound is carried across
    /// UNCHANGED and the seal decides. That is deliberate: if clearing a
    /// removed column's residual needed its upper bound, the combination's
    /// constant moves and the identity for THIS bound fails — declining is
    /// right, because the alternative is quietly reporting a weaker bound than
    /// the `Optimal` verdict it is attached to.
    pub(crate) fn lift_optimality(
        &self,
        reduced: &OptimalityCertificate,
        original: &Model,
    ) -> Option<OptimalityCertificate> {
        if original.num_cols() != self.map.len() || reduced.sense != original.sense() {
            return None;
        }
        if !claims_the_objective(&reduced.objective, &self.induced_objective(original)?) {
            return None;
        }
        let want = optimality_target(original, reduced.sense);
        let multipliers = self.lift_multipliers(&reduced.multipliers, original, &want, None)?;
        seal_optimality(
            reduced.sense,
            model_objective(original),
            reduced.bound.clone(),
            multipliers,
            original,
        )
    }

    /// Lift a whole-tree infeasibility certificate, or `None`.
    ///
    /// ⚠ This is the case where a lift is EXPECTED to decline most of the time,
    /// and the reason is structural rather than arithmetic. The reduced tree
    /// splits only on KEPT columns; in the caller's frame the removed twins are
    /// still free in `[0, 1]`, so the split skeleton does not by itself cover
    /// the caller's domain. Each leaf can only close if its own Farkas
    /// combination already excludes the twins — which the per-column
    /// distribution below achieves exactly when every residual is nonnegative,
    /// i.e. when the leaf leans on the kept columns' LOWER bounds. A leaf that
    /// leans on an upper bound (the `x_k <= 0` side of a branch, the common
    /// case) spends constant it does not have and the seal rejects it.
    ///
    /// It is offered rather than hard-wired to `None` because it is fully
    /// sealed — the whole-tree verifier re-walks and re-prices everything — so
    /// the cases that do transfer are free. Callers must treat `None` as the
    /// expected answer.
    pub(crate) fn lift_tree_cert(
        &self,
        reduced: &MilpInfeasibilityCertificate,
        original: &Model,
    ) -> Option<MilpInfeasibilityCertificate> {
        if original.num_cols() != self.map.len() {
            return None;
        }
        lift_tree(reduced, original, self)
    }

    /// Rows and kept columns 1:1, then one box multiplier per column whose
    /// combined coefficient is not yet `want[j]`.
    fn lift_multipliers(
        &self,
        reduced: &[Multiplier],
        original: &Model,
        want: &[BigRational],
        col_bounds: Option<(&[Option<BigRational>], &[Option<BigRational>])>,
    ) -> Option<Vec<Multiplier>> {
        if original.num_cols() != self.map.len() || want.len() != self.map.len() {
            return None;
        }
        let mut base: Vec<Multiplier> = Vec::with_capacity(reduced.len());
        for m in reduced {
            if !m.coeff.is_positive() {
                return None;
            }
            let fact = match m.fact {
                // `dedup_columns` emits every row, in order: reduced row `i` IS
                // original row `i`, same bounds, same coefficients on the kept
                // columns. Re-checked against the model's arity rather than
                // assumed.
                FactRef::RowBound { row, side } => {
                    if row.index() >= original.num_rows() {
                        return None;
                    }
                    FactRef::RowBound { row, side }
                }
                FactRef::ColBound { col, side } => FactRef::ColBound {
                    col: Col(u32::try_from(*self.reverse.get(col.index())?).ok()?),
                    side,
                },
            };
            base.push(Multiplier {
                fact,
                coeff: m.coeff.clone(),
            });
        }

        let (coeffs, _constant) = combination_over_bounded(&base, original, col_bounds)?;
        let mut out = base;
        for (j, target) in want.iter().enumerate() {
            let delta = target - coeffs.get(j)?;
            if delta.is_zero() {
                continue;
            }
            out.push(column_correction(Col(u32::try_from(j).ok()?), delta));
        }
        Some(out)
    }

    /// The reduced model's objective: the caller's coefficients, on the kept
    /// columns, keyed by reduced column. A cost on a merged-away column belongs
    /// to no reduced column, and the reduction leaves it behind — which is
    /// sound for the VALUE (the widened point sets that column to 0) but means
    /// a reduced certificate's objective is not the caller's, so the lift must
    /// re-attach it rather than pass the certificate through.
    fn induced_objective(&self, original: &Model) -> Option<BTreeMap<u32, BigRational>> {
        let mut induced: BTreeMap<u32, BigRational> = BTreeMap::new();
        for (j, slot) in self.map.iter().enumerate() {
            let Some(reduced) = slot else { continue };
            let a = original.obj_coeff(Col(u32::try_from(j).ok()?));
            if a == 0.0 {
                continue;
            }
            *induced.entry(reduced.0).or_insert_with(BigRational::zero) +=
                original.obj_coeff_exact_at(u32::try_from(j).ok()?, a);
        }
        Some(induced)
    }
}

impl ReducedFrame for DedupLift<'_> {
    fn original_col(&self, reduced: Col) -> Option<Col> {
        Some(Col(u32::try_from(*self.reverse.get(reduced.index())?).ok()?))
    }

    fn lift_leaf(
        &self,
        leaf: &FarkasCertificate,
        original: &Model,
        lb: &[Option<BigRational>],
        ub: &[Option<BigRational>],
    ) -> Option<FarkasCertificate> {
        let want = vec![BigRational::zero(); self.map.len()];
        let multipliers =
            self.lift_multipliers(&leaf.multipliers, original, &want, Some((lb, ub)))?;
        let cert = FarkasCertificate { multipliers };
        cert.verify_with_col_bounds(original, lb, ub).ok()?;
        Some(cert)
    }
}

/// The ONE multiplier that adds `delta` to a column's combined coefficient.
///
/// A positive `delta` is the column's LOWER fact (`x − lb`, coefficient `+1`),
/// a negative one its UPPER fact (`ub − x`, coefficient `−1`) with `|delta|`.
/// There is no choice here and no sign that cannot be represented — but each
/// also moves the combination's CONSTANT (by `−delta·lb` and `−delta·ub`
/// respectively), which is why this is never the last word: the seal re-checks
/// the constant against the identity the certificate claims.
fn column_correction(col: Col, delta: BigRational) -> Multiplier {
    if delta.is_positive() {
        Multiplier {
            fact: FactRef::ColBound {
                col,
                side: BoundSide::Lower,
            },
            coeff: delta,
        }
    } else {
        Multiplier {
            fact: FactRef::ColBound {
                col,
                side: BoundSide::Upper,
            },
            coeff: -delta,
        }
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use num_traits::One;

    use super::*;
    use crate::lattice::reformulate_kernel;

    /// THE ENVIRONMENT LOCK, TAKEN BY READERS. Every test below that runs a real
    /// solve takes it, and none of them mutates the environment: `lock_env`
    /// serialises WRITERS, and a solve is a READER of a couple of dozen `AY_*`
    /// names — it samples them once, at `solve_milp_in` entry. Sibling tests in
    /// this binary set knobs around their own solves and hold them for the
    /// duration (`bab::tests::solve_node_capped` installs `with_max_nodes`,
    /// exactly as its doc says), so a solve that STARTS inside that window
    /// inherits the cap and reports `Feasible { incumbent_only: true }` where the
    /// test demanded `Optimal`. Observed live: seven tests in this module at
    /// `--test-threads=4`, all with an intact fixture and a capped tree. Joining
    /// the same lock puts readers and writers in one order.
    fn solve_lock() -> std::sync::MutexGuard<'static, ()> {
        ay_test_support::env::lock_env()
    }

    fn int(v: i64) -> BigRational {
        BigRational::from(BigInt::from(v))
    }

    /// An INFEASIBLE model the kernel reformulation fires on, with a second,
    /// independent contradiction outside the reformulated block so that a
    /// single certificate exercises all three lift rules at once:
    ///
    /// * `3·x₀ + 5·x₁ = −1`, `x₀,x₁ ≥ 0` integer and unbounded above — the
    ///   reformulated block (rule 2 on the bound rows, rule 4 on the deleted
    ///   equality);
    /// * `y ≥ 2` with a row `y ≤ 1` — a surviving column and a surviving row
    ///   (rules 1 and the surviving-column case).
    fn infeasible_model() -> Model {
        let mut m = Model::new();
        let x0 = m.add_int_col(0.0, f64::INFINITY);
        let x1 = m.add_int_col(0.0, f64::INFINITY);
        let y = m.add_col(2.0, f64::INFINITY);
        m.add_row(-1.0, -1.0, &[(x0, 3.0), (x1, 5.0)]);
        m.add_row(f64::NEG_INFINITY, 1.0, &[(y, 1.0)]);
        m.set_objective(&[(x0, 1.0)], Sense::Minimize);
        m
    }

    /// The reduced-frame Farkas certificate for [`infeasible_model`], built
    /// from the reduced model's ACTUAL coefficients (never from an assumed
    /// basis) and asserted to verify there before anything is lifted.
    fn reduced_farkas(reduced: &Model) -> FarkasCertificate {
        // The two bound rows carry one `z` term each, with opposite signs (if
        // they agreed the block would be feasible); cross-multiplying their
        // lower sides cancels `z`.
        let mut bound_rows: Vec<(Row, BigRational)> = Vec::new();
        let mut folded: Option<Row> = None;
        for i in 0..reduced.num_rows() {
            let row = Row(i as u32);
            let (coeffs, lb, _) = reduced.row(row);
            if lb.is_finite()
                && coeffs.len() == 1
                && reduced.col_bounds(Col(coeffs[0].0)).0.is_infinite()
            {
                bound_rows.push((row, exact(coeffs[0].1).expect("finite")));
            } else {
                folded = Some(row);
            }
        }
        assert_eq!(bound_rows.len(), 2, "two finite lower bounds in C");
        let folded = folded.expect("the y row survives");
        let (r0, a0) = bound_rows[0].clone();
        let (r1, a1) = bound_rows[1].clone();
        assert!(
            (a0.is_positive() && a1.is_negative()) || (a0.is_negative() && a1.is_positive()),
            "an infeasible 1-D block has opposite-signed bound rows: {a0} {a1}"
        );
        let surviving_col = (0..reduced.num_cols())
            .map(|j| Col(j as u32))
            .find(|&c| reduced.col_bounds(c).0.is_finite())
            .expect("y survives with a finite lower bound");

        FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: r0,
                        side: BoundSide::Lower,
                    },
                    coeff: a1.abs(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: r1,
                        side: BoundSide::Lower,
                    },
                    coeff: a0.abs(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: surviving_col,
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: folded,
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
            ],
        }
    }

    /// An OPTIMAL model the reformulation fires on, whose LP optimum over the
    /// equality is attained at an INTEGER point, so the dual bound the
    /// certificate carries is the true MILP optimum: `min x₀ + x₁` subject to
    /// `3·x₀ − 5·x₁ = 15`, `x₀,x₁ ≥ 0` integer, unbounded above. Optimum 5 at
    /// `(5, 0)`.
    ///
    /// `x_p` cannot make `const_delta = c·x_p = x_p[0] + x_p[1]` vanish here:
    /// `x_p[0] = −x_p[1]` would need `−8·x_p[1] = 15`. So the
    /// objective-constant bookkeeping is genuinely exercised whatever
    /// particular solution the HNF returns.
    fn optimal_model() -> Model {
        let mut m = Model::new();
        let x0 = m.add_int_col(0.0, f64::INFINITY);
        let x1 = m.add_int_col(0.0, f64::INFINITY);
        m.add_row(15.0, 15.0, &[(x0, 3.0), (x1, -5.0)]);
        m.set_objective(&[(x0, 1.0), (x1, 1.0)], Sense::Minimize);
        m
    }

    /// The reduced-frame optimality certificate for [`optimal_model`]: the
    /// reduced model is one free `z` column under two lower-bound rows, so its
    /// dual is the single tightest of them. Built from the reduced model's own
    /// numbers and asserted to verify there first.
    fn reduced_optimality(reduced: &Model) -> OptimalityCertificate {
        let z = Col(0);
        assert_eq!(reduced.num_cols(), 1, "one kernel direction");
        let g = exact(reduced.obj_coeff(z)).expect("finite");
        assert!(!g.is_zero());

        let mut best: Option<(Row, BigRational, BigRational)> = None;
        for i in 0..reduced.num_rows() {
            let row = Row(i as u32);
            let (coeffs, lb, _) = reduced.row(row);
            if !lb.is_finite() || coeffs.len() != 1 {
                continue;
            }
            let beta = exact(coeffs[0].1).expect("finite");
            let y = &g / &beta;
            if !y.is_positive() {
                continue;
            }
            let bound = &y * exact(lb).expect("finite");
            if best.as_ref().is_none_or(|(_, _, b)| &bound > b) {
                best = Some((row, y, bound));
            }
        }
        let (row, y, bound) = best.expect("a bounded 1-D LP has a binding row");
        OptimalityCertificate {
            sense: reduced.sense(),
            objective: vec![(z.0, g)],
            bound,
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row,
                    side: BoundSide::Lower,
                },
                coeff: y,
            }],
        }
    }

    #[test]
    fn farkas_round_trips_from_the_reformulated_frame() {
        let original = infeasible_model();
        let (reduced, post) = reformulate_kernel(&original).expect("the model is this shape");
        let cert = reduced_farkas(&reduced);
        assert_eq!(
            cert.verify(&reduced),
            Ok(()),
            "the fixture's reduced certificate must be valid THERE first"
        );

        let lifted = post
            .lift_farkas(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(
            lifted.verify(&original),
            Ok(()),
            "the lifted certificate must verify in the CALLER's frame"
        );
        // The recovered equality multiplier is what makes it verify: without a
        // fact for the deleted row the `C` coefficients cannot cancel.
        assert!(
            lifted.multipliers.iter().any(|m| matches!(
                m.fact,
                FactRef::RowBound { row, .. } if row.index() == 0
            )),
            "the deleted equality row must appear in the lifted certificate"
        );
        // And every lifted fact is a fact of the ORIGINAL model.
        for m in &lifted.multipliers {
            assert!(m.coeff.is_positive(), "contract: strictly positive");
            match m.fact {
                FactRef::RowBound { row, .. } => assert!(row.index() < original.num_rows()),
                FactRef::ColBound { col, .. } => assert!(col.index() < original.num_cols()),
            }
        }
    }

    #[test]
    fn optimality_round_trips_and_its_bound_is_the_caller_frame_optimum() {
        let _env = solve_lock();
        let original = optimal_model();
        let (reduced, post) = reformulate_kernel(&original).expect("the model is this shape");
        let cert = reduced_optimality(&reduced);
        assert_eq!(
            cert.verify(&reduced),
            Ok(()),
            "the fixture's reduced certificate must be valid THERE first"
        );
        assert!(
            !post.const_delta.is_zero(),
            "this fixture exists to exercise a NONZERO objective constant"
        );

        let lifted = post
            .lift_optimality(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(
            lifted.verify(&original),
            Ok(()),
            "the lifted certificate must verify in the CALLER's frame"
        );
        assert_eq!(lifted.bound, int(5), "the true optimum of the fixture");
        assert_eq!(
            lifted.objective,
            vec![(0, BigRational::one()), (1, BigRational::one())],
            "the lifted certificate names the CALLER's objective"
        );
        assert_eq!(&lifted.bound - &post.const_delta, cert.bound);

        // Independently: the solver's own answer for the original model.
        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(0)
            .with_time_limit(std::time::Duration::from_secs(30));
        match crate::bab::solve_milp(&original, &opts) {
            crate::Outcome::Optimal { value, .. } => {
                assert_eq!(value, lifted.bound, "the dual bound must MEET the optimum");
            }
            other => panic!("expected Optimal, got {other:?}"),
        }
    }

    /// The certificate bounds the PURE LINEAR FORM, so the model's objective
    /// OFFSET must not appear in the lifted bound — only `const_delta`, which
    /// is what the SUBSTITUTION folded out. The two constants are easy to
    /// confuse (both are added to a reported value on the way out of
    /// `expand_kernel_outcome`), and confusing them yields a certificate that
    /// verifies nowhere or, worse, a bound off by the offset.
    #[test]
    fn the_objective_offset_stays_out_of_the_lifted_bound() {
        let _env = solve_lock();
        let mut original = optimal_model();
        original.set_objective_offset(7.0);
        let (reduced, post) = reformulate_kernel(&original).expect("the model is this shape");
        assert_eq!(reduced.objective_offset(), 7.0, "the offset rides along");

        let cert = reduced_optimality(&reduced);
        assert_eq!(cert.verify(&reduced), Ok(()));
        let lifted = post
            .lift_optimality(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert_eq!(lifted.bound, int(5), "the LINEAR FORM's bound, offset-free");

        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(0)
            .with_time_limit(std::time::Duration::from_secs(30));
        match crate::bab::solve_milp(&original, &opts) {
            crate::Outcome::Optimal { value, .. } => {
                assert_eq!(value, int(12), "the reported value DOES include the offset");
                assert_eq!(value, &lifted.bound + int(7));
            }
            other => panic!("expected Optimal, got {other:?}"),
        }
    }

    #[test]
    fn a_corrupted_lifted_multiplier_is_rejected_by_verify_and_by_the_seal() {
        let original = infeasible_model();
        let (reduced, post) = reformulate_kernel(&original).expect("the model is this shape");
        let cert = reduced_farkas(&reduced);
        let lifted = post
            .lift_farkas(&cert, &original)
            .expect("control: the honest lift succeeds");
        assert_eq!(lifted.verify(&original), Ok(()));

        // (a) Perturbing ONE lifted coefficient must be caught by the public
        //     verifier — the certificate no longer combines to a contradiction.
        for index in 0..lifted.multipliers.len() {
            let mut corrupt = lifted.clone();
            corrupt.multipliers[index].coeff += BigRational::one();
            assert!(
                corrupt.verify(&original).is_err(),
                "verify accepted a certificate with multiplier {index} perturbed"
            );
        }

        // (b) The SEAL is the same check, so the same corruption cannot escape
        //     through it either.
        for index in 0..lifted.multipliers.len() {
            let mut multipliers = lifted.multipliers.clone();
            multipliers[index].coeff += BigRational::one();
            assert!(
                seal_farkas(multipliers, &original).is_none(),
                "the seal passed a certificate with multiplier {index} perturbed"
            );
        }

        // (c) And corrupting the REDUCED certificate before the lift makes the
        //     lift decline rather than emit anything: the recovery solve for the
        //     deleted equality becomes inconsistent.
        let mut corrupt_reduced = cert.clone();
        corrupt_reduced.multipliers[0].coeff += BigRational::one();
        assert!(
            corrupt_reduced.verify(&reduced).is_err(),
            "control: the corrupted reduced certificate is not valid either"
        );
        assert!(
            post.lift_farkas(&corrupt_reduced, &original).is_none(),
            "a corrupted reduced certificate must not lift to anything"
        );
    }

    #[test]
    fn the_lift_declines_what_it_cannot_translate() {
        let original = infeasible_model();
        let (reduced, post) = reformulate_kernel(&original).expect("the model is this shape");

        // (1) A bound fact on a FREE `z` column cannot occur (rule 3). Assert
        //     the decline rather than trusting that it never happens.
        let z = *post.z.first().expect("one kernel direction");
        let on_z = FarkasCertificate {
            multipliers: vec![Multiplier {
                fact: FactRef::ColBound {
                    col: z,
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            }],
        };
        assert!(post.lift_farkas(&on_z, &original).is_none());

        // (2) A reduced row index that does not exist.
        let missing = FarkasCertificate {
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(reduced.num_rows() as u32),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            }],
        };
        assert!(post.lift_farkas(&missing, &original).is_none());

        // (3) An optimality certificate for an objective that is NOT the one
        //     the reformulation induced — the caller-frame objective it bounds
        //     is not determined, so the lift must refuse to invent one.
        let opt = optimal_model();
        let (opt_reduced, opt_post) = reformulate_kernel(&opt).expect("fires");
        let mut foreign = reduced_optimality(&opt_reduced);
        assert!(
            opt_post.lift_optimality(&foreign, &opt).is_some(),
            "control: the induced objective does lift"
        );
        foreign.objective = vec![(0, int(1))];
        assert!(
            opt_post.lift_optimality(&foreign, &opt).is_none(),
            "a foreign reduced objective must decline"
        );

        // (4) The wrong model entirely.
        let cert = reduced_farkas(&reduced);
        assert!(post.lift_farkas(&cert, &opt).is_none());
    }

    #[test]
    fn the_repair_solve_is_exact_and_declines_inconsistent_systems() {
        let rows = vec![vec![int(3), int(5)], vec![int(1), int(1)]];
        // 3a + b = 1, 5a + b = 3  =>  a = 1, b = -2.
        let mu = solve_row_combination(&rows, &[int(1), int(3)]).expect("consistent");
        assert_eq!(mu, vec![int(1), int(-2)]);

        // A single row cannot produce a vector off its own line.
        assert!(solve_row_combination(&rows[..1], &[int(1), int(3)]).is_none());
        // The zero system solves only the zero right-hand side.
        assert!(solve_row_combination(&[], &[BigRational::zero()]).is_some());
        assert!(solve_row_combination(&[], &[int(1)]).is_none());
        // Ragged input is refused rather than indexed into.
        assert!(solve_row_combination(&[vec![int(1)]], &[int(1), int(1)]).is_none());
    }

    #[test]
    fn signed_facts_only_flip_sides_that_name_the_same_form() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 4.0);
        let equality = m.add_row(2.0, 2.0, &[(x, 1.0)]);
        let range = m.add_row(0.0, 7.0, &[(x, 1.0)]);

        let mut facts = SignedFacts::new();
        facts.push(
            FactRef::RowBound {
                row: equality,
                side: BoundSide::Lower,
            },
            int(-3),
        );
        facts.push(
            FactRef::ColBound {
                col: x,
                side: BoundSide::Lower,
            },
            BigRational::zero(),
        );
        let out = facts.into_multipliers(&m).expect("an equality flips");
        assert_eq!(
            out,
            vec![Multiplier {
                fact: FactRef::RowBound {
                    row: equality,
                    side: BoundSide::Upper
                },
                coeff: int(3),
            }],
            "the negative flips side and the exact zero is dropped"
        );

        let mut facts = SignedFacts::new();
        facts.push(
            FactRef::RowBound {
                row: range,
                side: BoundSide::Lower,
            },
            int(-3),
        );
        assert!(
            facts.into_multipliers(&m).is_none(),
            "a range row's two sides are DIFFERENT forms and must not be flipped"
        );
    }

    // -----------------------------------------------------------------------
    // Binary equivalence/complement substitution's lift.
    // -----------------------------------------------------------------------

    #[test]
    fn binary_complement_farkas_round_trips_to_the_caller_frame() {
        let mut original = Model::new();
        let x = original.add_binary_col();
        let y = original.add_binary_col();
        original.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        original.add_row(2.0, f64::INFINITY, &[(y, 1.0)]);

        let (reduced, post) = crate::presolve::substitute_binary_complements(&original)
            .expect("the complement equation fires");
        assert_eq!(reduced.num_cols(), 1);
        assert_eq!(reduced.num_rows(), 1);
        // y >= 2 becomes x <= -1 after canonical sign normalization.  Its
        // upper side plus x's lower bound
        // combines to the constant -1.
        let certificate = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(0),
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: Col(0),
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };
        assert_eq!(certificate.verify(&reduced), Ok(()));
        assert!(certificate.verify(&original).is_err());

        let lifted = post
            .lift_farkas(&certificate, &original)
            .expect("the exact equality repair must lift");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert!(lifted.multipliers.iter().any(|multiplier| matches!(
            multiplier.fact,
            FactRef::RowBound {
                row: Row(0),
                side: BoundSide::Upper
            }
        )));
    }

    #[test]
    fn binary_complement_optimality_lifts_the_folded_constant() {
        let mut original = Model::new();
        let x = original.add_binary_col();
        let y = original.add_binary_col();
        original.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        original.set_objective(&[(x, 3.0), (y, 5.0)], Sense::Minimize);

        let (reduced, post) = crate::presolve::substitute_binary_complements(&original)
            .expect("the complement equation fires");
        assert_eq!(*post.const_delta(), int(5));
        assert_eq!(reduced.obj_coeff(Col(0)), -2.0);
        let certificate = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, int(-2))],
            bound: int(-2),
            multipliers: vec![Multiplier {
                fact: FactRef::ColBound {
                    col: Col(0),
                    side: BoundSide::Upper,
                },
                coeff: int(2),
            }],
        };
        assert_eq!(certificate.verify(&reduced), Ok(()));

        let lifted = post
            .lift_optimality(&certificate, &original)
            .expect("objective and equality repair must lift");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert_eq!(lifted.bound, int(3));
        assert_eq!(lifted.objective, vec![(0, int(3)), (1, int(5))]);
    }

    #[test]
    fn binary_complement_tree_lifts_every_leaf_and_preserves_the_split() {
        let mut original = Model::new();
        let x = original.add_binary_col();
        let y = original.add_binary_col();
        original.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        original.add_row(0.5, 0.5, &[(y, 1.0)]);

        let (reduced, post) = crate::presolve::substitute_binary_complements(&original)
            .expect("the complement equation fires");
        // y = 1-x and y = 1/2 become x = 1/2 after canonical sign
        // normalization.  At x<=0 the row's lower side contradicts the branch
        // upper bound; at x>=1 its upper side contradicts the branch lower.
        let leaf = |row_side, col_side| TreeNode::Leaf {
            farkas: FarkasCertificate {
                multipliers: vec![
                    Multiplier {
                        fact: FactRef::RowBound {
                            row: Row(0),
                            side: row_side,
                        },
                        coeff: BigRational::one(),
                    },
                    Multiplier {
                        fact: FactRef::ColBound {
                            col: Col(0),
                            side: col_side,
                        },
                        coeff: BigRational::one(),
                    },
                ],
            },
        };
        let certificate = MilpInfeasibilityCertificate {
            root: TreeNode::Split {
                col: Col(0),
                cut: BigRational::zero(),
                lo: Box::new(leaf(BoundSide::Lower, BoundSide::Upper)),
                hi: Box::new(leaf(BoundSide::Upper, BoundSide::Lower)),
            },
        };
        assert_eq!(certificate.verify(&reduced), Ok(()));

        let lifted = post
            .lift_tree_cert(&certificate, &original)
            .expect("both leaves must lift and seal");
        assert_eq!(lifted.verify(&original), Ok(()));
        let TreeNode::Split { col, cut, .. } = lifted.root else {
            panic!("the split skeleton survives");
        };
        assert_eq!(col, x);
        assert_eq!(cut, BigRational::zero());
    }

    // -----------------------------------------------------------------------
    // Objective-driven continuous singleton substitution's lift.
    // -----------------------------------------------------------------------

    /// `aggregate` is removed first, exposing `slack` as the next objective
    /// singleton.  The reduced proof `min t >= 5` must become the caller-frame
    /// proof `min aggregate >= 2`, including both defining rows and the folded
    /// constant `-3`.
    #[test]
    fn objective_singleton_optimality_lifts_defining_rows_and_constant() {
        let mut original = Model::new();
        let slack = original.add_col(0.0, f64::INFINITY);
        let t = original.add_int_col(5.0, 10.0);
        let aggregate = original.add_col(0.0, f64::INFINITY);
        original.add_row(f64::NEG_INFINITY, 3.0, &[(t, 1.0), (slack, -1.0)]);
        original.add_row(f64::NEG_INFINITY, 0.0, &[(slack, 1.0), (aggregate, -1.0)]);
        original.set_objective(&[(aggregate, 1.0)], Sense::Minimize);

        let (reduced, post) = crate::presolve::substitute_objective_singletons(&original)
            .expect("both objective singletons eliminate");
        assert_eq!((reduced.num_rows(), reduced.num_cols()), (0, 1));
        assert_eq!(*post.const_delta(), int(-3));
        let certificate = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, int(1))],
            bound: int(5),
            multipliers: vec![Multiplier {
                fact: FactRef::ColBound {
                    col: Col(0),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            }],
        };
        assert_eq!(certificate.verify(&reduced), Ok(()));
        assert!(certificate.verify(&original).is_err());

        let lifted = post
            .lift_optimality(&certificate, &original)
            .expect("both defining row facts reattach exactly");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert_eq!(lifted.bound, int(2));
        assert_eq!(lifted.objective, vec![(aggregate.0, int(1))]);
        for row in [Row(0), Row(1)] {
            assert!(lifted.multipliers.iter().any(|multiplier| matches!(
                multiplier.fact,
                FactRef::RowBound {
                    row: cited,
                    side: BoundSide::Upper
                } if cited == row
            )));
        }
    }

    #[test]
    fn objective_singleton_farkas_maps_surviving_facts() {
        let mut original = Model::new();
        let slack = original.add_col(0.0, f64::INFINITY);
        let t = original.add_int_col(5.0, 10.0);
        let aggregate = original.add_col(0.0, f64::INFINITY);
        original.add_row(f64::NEG_INFINITY, 3.0, &[(t, 1.0), (slack, -1.0)]);
        original.add_row(f64::NEG_INFINITY, 0.0, &[(slack, 1.0), (aggregate, -1.0)]);
        original.add_row(f64::NEG_INFINITY, 4.0, &[(t, 1.0)]);
        original.set_objective(&[(aggregate, 1.0)], Sense::Minimize);

        let (reduced, post) = crate::presolve::substitute_objective_singletons(&original)
            .expect("objective singleton reduction fires");
        let certificate = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(0),
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: Col(0),
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };
        assert_eq!(certificate.verify(&reduced), Ok(()));
        let lifted = post
            .lift_farkas(&certificate, &original)
            .expect("surviving facts map back to the caller");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert!(lifted.multipliers.iter().any(|multiplier| matches!(
            multiplier.fact,
            FactRef::RowBound {
                row: Row(2),
                side: BoundSide::Upper
            }
        )));
    }

    #[test]
    fn objective_singleton_tree_lifts_leaves_and_split() {
        let mut original = Model::new();
        let slack = original.add_col(0.0, f64::INFINITY);
        let t = original.add_int_col(5.0, 10.0);
        let aggregate = original.add_col(0.0, f64::INFINITY);
        original.add_row(f64::NEG_INFINITY, 3.0, &[(t, 1.0), (slack, -1.0)]);
        original.add_row(f64::NEG_INFINITY, 0.0, &[(slack, 1.0), (aggregate, -1.0)]);
        original.add_row(5.5, 5.5, &[(t, 1.0)]);
        original.set_objective(&[(aggregate, 1.0)], Sense::Minimize);

        let (reduced, post) = crate::presolve::substitute_objective_singletons(&original)
            .expect("objective singleton reduction fires");
        let leaf = |row_side, col_side| TreeNode::Leaf {
            farkas: FarkasCertificate {
                multipliers: vec![
                    Multiplier {
                        fact: FactRef::RowBound {
                            row: Row(0),
                            side: row_side,
                        },
                        coeff: BigRational::one(),
                    },
                    Multiplier {
                        fact: FactRef::ColBound {
                            col: Col(0),
                            side: col_side,
                        },
                        coeff: BigRational::one(),
                    },
                ],
            },
        };
        let certificate = MilpInfeasibilityCertificate {
            root: TreeNode::Split {
                col: Col(0),
                cut: int(5),
                lo: Box::new(leaf(BoundSide::Lower, BoundSide::Upper)),
                hi: Box::new(leaf(BoundSide::Upper, BoundSide::Lower)),
            },
        };
        assert_eq!(certificate.verify(&reduced), Ok(()));
        let lifted = post
            .lift_tree_cert(&certificate, &original)
            .expect("both leaves map and seal in the caller frame");
        assert_eq!(lifted.verify(&original), Ok(()));
        let TreeNode::Split { col, cut, .. } = lifted.root else {
            panic!("the split skeleton survives");
        };
        assert_eq!(col, t);
        assert_eq!(cut, int(5));
    }

    // -----------------------------------------------------------------------
    // The singleton-column substitution's lift.
    // -----------------------------------------------------------------------

    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    /// An INFEASIBLE model the singleton substitution fires on, in the shape
    /// that exercises the interesting rule: `x` is NOT implied-free, so its
    /// defining equality is REBOUNDED rather than dropped and the reduced row
    /// is a forcing range whose two sides are `x`'s box, not the row's.
    ///
    /// * `x ∈ [0, 1]` continuous, degree 1, defined by `x + y = 5`;
    /// * `y ∈ [0, 10]` continuous, degree 2 (so not itself eligible);
    /// * `y <= 1`, which contradicts the `y >= 4` the forcing range imposes.
    fn singleton_infeasible_model() -> Model {
        let mut m = Model::new();
        let x = m.add_col(0.0, 1.0);
        let y = m.add_col(0.0, 10.0);
        m.add_row(5.0, 5.0, &[(x, 1.0), (y, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 1.0, &[(y, 1.0)]);
        m.set_objective(&[(y, 1.0)], Sense::Minimize);
        m
    }

    /// A model with a KNOWN optimum whose singleton fold moves cost off the
    /// eliminated column (`const_delta = 6`, and the surviving objective flips
    /// sign), so the lift's constant bookkeeping is genuinely exercised:
    /// `min x + y` subject to `x + 2y = 6`, `y >= 1`, `x ∈ [0, 10]`,
    /// `y ∈ [0, 10]` integer. Optimum 3 at `(0, 3)`.
    fn singleton_optimal_model() -> Model {
        let mut m = Model::new();
        let x = m.add_col(0.0, 10.0);
        let y = m.add_int_col(0.0, 10.0);
        m.add_row(6.0, 6.0, &[(x, 1.0), (y, 2.0)]);
        m.add_row(1.0, f64::INFINITY, &[(y, 1.0)]);
        m.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Minimize);
        m
    }

    /// The rebounded row of a singleton-reduced model: the one whose bounds are
    /// NOT its original's. Located by structure (a row over exactly one
    /// surviving column that is not a copy of an original row) rather than by
    /// an assumed index.
    fn only_rebound_row(post: &SingletonPostsolve) -> usize {
        let mut found = None;
        for (reduced, origin) in post.row_origin.iter().enumerate() {
            if matches!(origin, SingletonRowOrigin::Rebound { .. }) {
                assert!(found.is_none(), "this fixture rebounds exactly one row");
                found = Some(reduced);
            }
        }
        found.expect("the fixture must rebound a row, or it tests nothing")
    }

    #[test]
    fn singleton_farkas_round_trips_from_the_reduced_frame() {
        let original = singleton_infeasible_model();
        let (reduced, post) =
            crate::presolve::substitute_singletons(&original).expect("x is an eligible singleton");
        let rebound = only_rebound_row(&post);
        assert_eq!(
            reduced.num_cols(),
            1,
            "only y survives; x is substituted out"
        );

        // The forcing range says `y >= 4`; the surviving row says `y <= 1`.
        let kept = (0..reduced.num_rows())
            .find(|&r| r != rebound)
            .expect("the y row survives");
        let cert = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(rebound as u32),
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(kept as u32),
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };
        assert_eq!(
            cert.verify(&reduced),
            Ok(()),
            "the fixture's reduced certificate must be valid THERE first"
        );
        assert!(
            cert.verify(&original).is_err(),
            "and it must NOT be valid in the caller's frame — otherwise this \
             test would pass without a lift"
        );

        let lifted = post
            .lift_farkas(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(
            lifted.verify(&original),
            Ok(()),
            "the lifted certificate must verify in the CALLER's frame"
        );
        // The rebounded row's lower side IS `x`'s upper bound plus the original
        // equality; both must appear, or the coefficients could not cancel.
        assert!(
            lifted.multipliers.iter().any(|m| matches!(
                m.fact,
                FactRef::ColBound { col, side: BoundSide::Upper } if col.index() == 0
            )),
            "the eliminated column's box fact must appear: {:?}",
            lifted.multipliers
        );
        for m in &lifted.multipliers {
            assert!(m.coeff.is_positive(), "contract: strictly positive");
            match m.fact {
                FactRef::RowBound { row, .. } => assert!(row.index() < original.num_rows()),
                FactRef::ColBound { col, .. } => assert!(col.index() < original.num_cols()),
            }
        }
    }

    #[test]
    fn singleton_optimality_round_trips_and_carries_the_folded_constant() {
        let _env = solve_lock();
        let original = singleton_optimal_model();
        let (reduced, post) =
            crate::presolve::substitute_singletons(&original).expect("x is an eligible singleton");
        assert_eq!(
            *post.const_delta(),
            int(6),
            "this fixture exists to exercise a NONZERO folded constant"
        );
        let rebound = only_rebound_row(&post);

        // The reduced model is `min −y` over `2y <= 6`, `y >= 1`: the binding
        // dual is half the rebounded row's UPPER side.
        let cert = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, int(-1))],
            bound: int(-3),
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(rebound as u32),
                    side: BoundSide::Upper,
                },
                coeff: rat(1, 2),
            }],
        };
        assert_eq!(
            cert.verify(&reduced),
            Ok(()),
            "the fixture's reduced certificate must be valid THERE first"
        );

        let lifted = post
            .lift_optimality(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(
            lifted.verify(&original),
            Ok(()),
            "the lifted certificate must verify in the CALLER's frame"
        );
        assert_eq!(lifted.bound, int(3), "−3 + const_delta 6");
        assert_eq!(
            lifted.objective,
            vec![(0, BigRational::one()), (1, BigRational::one())],
            "the lifted certificate names the CALLER's objective"
        );
        assert_eq!(&lifted.bound - post.const_delta(), cert.bound);

        // Independently: the solver's own answer for the original model.
        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(0)
            .with_time_limit(std::time::Duration::from_secs(30));
        match crate::bab::solve_milp(&original, &opts) {
            crate::Outcome::Optimal { value, .. } => {
                assert_eq!(value, lifted.bound, "the dual bound must MEET the optimum");
            }
            other => panic!("expected Optimal, got {other:?}"),
        }
    }

    /// The model's objective OFFSET rides the reduced model verbatim and is NOT
    /// part of what a certificate bounds, so only `const_delta` may move the
    /// lifted bound. The two constants are both added to a reported value on
    /// the way out of `expand_singleton_outcome`, which is exactly what makes
    /// them easy to confuse.
    #[test]
    fn the_singleton_offset_stays_out_of_the_lifted_bound() {
        let _env = solve_lock();
        let mut original = singleton_optimal_model();
        original.set_objective_offset(7.0);
        let (reduced, post) = crate::presolve::substitute_singletons(&original).expect("eligible");
        assert_eq!(reduced.objective_offset(), 7.0, "the offset rides along");
        let rebound = only_rebound_row(&post);

        let cert = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, int(-1))],
            bound: int(-3),
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(rebound as u32),
                    side: BoundSide::Upper,
                },
                coeff: rat(1, 2),
            }],
        };
        assert_eq!(cert.verify(&reduced), Ok(()));
        let lifted = post
            .lift_optimality(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert_eq!(lifted.bound, int(3), "the LINEAR FORM's bound, offset-free");

        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(0)
            .with_time_limit(std::time::Duration::from_secs(30));
        match crate::bab::solve_milp(&original, &opts) {
            crate::Outcome::Optimal { value, .. } => {
                assert_eq!(value, int(10), "the reported value DOES include the offset");
                assert_eq!(value, &lifted.bound + int(7));
            }
            other => panic!("expected Optimal, got {other:?}"),
        }
    }

    #[test]
    fn a_corrupted_singleton_lift_is_rejected_by_verify_and_by_the_seal() {
        let original = singleton_infeasible_model();
        let (reduced, post) = crate::presolve::substitute_singletons(&original).expect("eligible");
        let rebound = only_rebound_row(&post);
        let kept = (0..reduced.num_rows())
            .find(|&r| r != rebound)
            .expect("row");
        let cert = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(rebound as u32),
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(kept as u32),
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };
        let lifted = post
            .lift_farkas(&cert, &original)
            .expect("control: the honest lift succeeds");

        for index in 0..lifted.multipliers.len() {
            let mut corrupt = lifted.clone();
            corrupt.multipliers[index].coeff += BigRational::one();
            assert!(
                corrupt.verify(&original).is_err(),
                "verify accepted a certificate with multiplier {index} perturbed"
            );
            let mut multipliers = lifted.multipliers.clone();
            multipliers[index].coeff += BigRational::one();
            assert!(
                seal_farkas(multipliers, &original).is_none(),
                "the seal passed a certificate with multiplier {index} perturbed"
            );
        }

        // A reduced certificate that is not a contradiction cannot lift to one:
        // the lift moves facts across, it never invents slack.
        let mut corrupt_reduced = cert.clone();
        corrupt_reduced.multipliers[0].coeff = rat(1, 4);
        assert!(
            corrupt_reduced.verify(&reduced).is_err(),
            "control: the corrupted reduced certificate is not valid either"
        );
        assert!(
            post.lift_farkas(&corrupt_reduced, &original).is_none(),
            "a non-contradictory reduced certificate must not lift to anything"
        );
    }

    #[test]
    fn the_singleton_lift_declines_what_it_cannot_translate() {
        let original = singleton_infeasible_model();
        let (reduced, post) = crate::presolve::substitute_singletons(&original).expect("eligible");
        let rebound = only_rebound_row(&post);

        // (1) A reduced row index that does not exist.
        let missing = FarkasCertificate {
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(reduced.num_rows() as u32),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            }],
        };
        assert!(post.lift_farkas(&missing, &original).is_none());

        // (2) A reduced column index that does not exist.
        let missing_col = FarkasCertificate {
            multipliers: vec![Multiplier {
                fact: FactRef::ColBound {
                    col: Col(reduced.num_cols() as u32),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            }],
        };
        assert!(post.lift_farkas(&missing_col, &original).is_none());

        // (3) The wrong model entirely.
        let other = singleton_optimal_model();
        let cert = FarkasCertificate {
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(rebound as u32),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            }],
        };
        assert!(post.lift_farkas(&cert, &other).is_none());

        // (4) A reduced objective that is not the fold of the caller's. The
        //     caller-frame objective such a certificate bounds is not
        //     determined — the eliminated column's cost is free — so inventing
        //     one is exactly what must not happen.
        let opt = singleton_optimal_model();
        let (_, opt_post) = crate::presolve::substitute_singletons(&opt).expect("eligible");
        let opt_rebound = only_rebound_row(&opt_post);
        let mut foreign = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, int(-1))],
            bound: int(-3),
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(opt_rebound as u32),
                    side: BoundSide::Upper,
                },
                coeff: rat(1, 2),
            }],
        };
        assert!(
            opt_post.lift_optimality(&foreign, &opt).is_some(),
            "control: the induced objective does lift"
        );
        foreign.objective = vec![(0, int(1))];
        assert!(
            opt_post.lift_optimality(&foreign, &opt).is_none(),
            "a foreign reduced objective must decline"
        );

        // (5) The wrong SENSE.
        let mut wrong_sense = OptimalityCertificate {
            sense: Sense::Maximize,
            ..foreign
        };
        wrong_sense.objective = vec![(0, int(-1))];
        assert!(opt_post.lift_optimality(&wrong_sense, &opt).is_none());
    }

    /// The whole point of the tree lift: a case split proved against the
    /// REDUCED model, re-named and re-priced into the caller's frame, checked
    /// by the real whole-tree verifier.
    ///
    /// A model the ENGINE proves infeasible by case split and the substitution
    /// fires on, used for the end-to-end tree round trips.
    ///
    /// `b0 + b1 + b2 = 3/2` over binaries is the crate's canonical
    /// case-split-only infeasibility: the relaxation is satisfiable, no bound
    /// propagates, and only enumeration closes it (`tests/tree_cert.rs` is
    /// built on the same row). Bolted on, in blocks the split does not touch,
    /// are BOTH singleton fates:
    ///
    /// * `x1 + w1 = 1` with `x1` FREE — implied-free, so the row is DROPPED,
    ///   which shifts every later row's reduced index;
    /// * `x2 + w2 = 1` with `x2 ∈ [0, 1/2]` — not implied-free, so the row is
    ///   REBOUNDED into a forcing range;
    /// * `x1` sits at column 0 and `x2` at the end, so the split block's
    ///   columns are renumbered too;
    /// * each `w` carries a second row, so its `x` is the defining row's ONLY
    ///   degree-1 continuous column (two would orphan one another and the
    ///   reduction would decline the row).
    ///
    /// The renumbering is the point: it makes the reduced tree certificate
    /// concretely INVALID in the caller's frame, so the round trip cannot pass
    /// by accident. What it does NOT cover — established by deleting the rule
    /// and watching this test stay green — is a leaf that CITES the forcing
    /// range, because this model's contradiction lives entirely in the binary
    /// block. That obligation is
    /// [`the_tree_lift_translates_a_forcing_range_at_every_leaf`]'s.
    fn singleton_case_split_model() -> Model {
        let mut m = Model::new();
        let x1 = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let w1 = m.add_col(0.0, 4.0);
        let b0 = m.add_binary_col();
        let b1 = m.add_binary_col();
        let b2 = m.add_binary_col();
        let w2 = m.add_col(0.0, 4.0);
        let x2 = m.add_col(0.0, 0.5);
        m.add_row(1.0, 1.0, &[(x1, 1.0), (w1, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 4.0, &[(w1, 1.0)]);
        m.add_row(1.5, 1.5, &[(b0, 1.0), (b1, 1.0), (b2, 1.0)]);
        m.add_row(1.0, 1.0, &[(x2, 1.0), (w2, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 4.0, &[(w2, 1.0)]);
        m
    }

    /// The leaf obligation the engine-driven round trip does not reach: a tree
    /// whose EVERY leaf cites the REBOUNDED row, one on each side.
    ///
    /// `x + 2y = 21/4` with `x ∈ [0, 1/2]` continuous and `y` integer. `x` is
    /// degree 1 and not implied-free, so its equality becomes the forcing range
    /// `19/4 <= 2y <= 21/4`, i.e. `y ∈ [2.375, 2.625]` — LP-feasible, integer-
    /// infeasible, and closed by a single split at 2. The lo leaf refutes with
    /// the range's LOWER side, the hi leaf with its UPPER side, and NEITHER
    /// fact exists in the caller's model: there the row is an equality over two
    /// columns, one of which the reduced model does not have.
    ///
    /// The tree is built here rather than solved for, because what is under
    /// test is the translation, and a hand-built tree is the only way to
    /// guarantee the leaves exercise it.
    #[test]
    fn the_tree_lift_translates_a_forcing_range_at_every_leaf() {
        let mut original = Model::new();
        let x = original.add_col(0.0, 0.5);
        let y = original.add_int_col(0.0, 10.0);
        original.add_row(5.25, 5.25, &[(x, 1.0), (y, 2.0)]);
        original.add_row(f64::NEG_INFINITY, 10.0, &[(y, 1.0)]);

        let (reduced, post) =
            crate::presolve::substitute_singletons(&original).expect("x is an eligible singleton");
        let rebound = only_rebound_row(&post);
        assert_eq!(reduced.num_cols(), 1, "only y survives");
        let y_reduced = Col(0);

        let leaf = |side: BoundSide, box_side: BoundSide, box_coeff: BigRational| TreeNode::Leaf {
            farkas: FarkasCertificate {
                multipliers: vec![
                    Multiplier {
                        fact: FactRef::RowBound {
                            row: Row(rebound as u32),
                            side,
                        },
                        coeff: BigRational::one(),
                    },
                    Multiplier {
                        fact: FactRef::ColBound {
                            col: y_reduced,
                            side: box_side,
                        },
                        coeff: box_coeff,
                    },
                ],
            },
        };
        let cert = MilpInfeasibilityCertificate {
            root: TreeNode::Split {
                col: y_reduced,
                cut: int(2),
                // y <= 2 makes 2y <= 4 < 19/4: the range's LOWER side refutes.
                lo: Box::new(leaf(BoundSide::Lower, BoundSide::Upper, int(2))),
                // y >= 3 makes 2y >= 6 > 21/4: its UPPER side refutes.
                hi: Box::new(leaf(BoundSide::Upper, BoundSide::Lower, int(2))),
            },
        };
        assert_eq!(
            cert.verify(&reduced),
            Ok(()),
            "the fixture's reduced tree must be valid THERE first"
        );
        assert!(
            cert.verify(&original).is_err(),
            "and invalid here — column 0 of the caller's model is CONTINUOUS, \
             so the split does not even type-check against it"
        );

        let lifted = post
            .lift_tree_cert(&cert, &original)
            .expect("the tree lift must succeed");
        assert_eq!(
            lifted.verify(&original),
            Ok(()),
            "the lifted tree must verify against the CALLER's model"
        );
        let TreeNode::Split { col, cut, .. } = &lifted.root else {
            panic!("the skeleton is preserved");
        };
        assert_eq!(*col, y, "the split is re-named to the caller's column");
        assert_eq!(*cut, int(2), "at the same integer cut");
    }

    #[test]
    fn singleton_tree_certificate_round_trips_from_the_reduced_frame() {
        let _env = solve_lock();
        let original = singleton_case_split_model();

        let (reduced, post) =
            crate::presolve::substitute_singletons(&original).expect("x is an eligible singleton");
        assert!(
            post.row_origin
                .iter()
                .any(|o| matches!(o, SingletonRowOrigin::Rebound { .. })),
            "the fixture must rebound, not drop, or the leaf lift is untested"
        );

        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(256)
            .with_time_limit(std::time::Duration::from_secs(30));
        let reduced_tree = match crate::bab::solve_milp(&reduced, &opts) {
            crate::Outcome::Infeasible { tree_cert, .. } => {
                tree_cert.expect("the reduced solve must capture a tree certificate")
            }
            other => panic!("the reduced model is infeasible; got {other:?}"),
        };
        assert_eq!(reduced_tree.verify(&reduced), Ok(()));
        assert!(
            reduced_tree.verify(&original).is_err(),
            "the reduced tree must NOT already verify in the caller's frame"
        );

        let lifted = post
            .lift_tree_cert(&reduced_tree, &original)
            .expect("the tree lift must succeed");
        assert_eq!(
            lifted.verify(&original),
            Ok(()),
            "the lifted tree must verify against the CALLER's model"
        );
    }

    /// The wired path, end to end: a caller who armed tree-certificate capture
    /// and enabled the substitution gets BOTH the right verdict AND evidence
    /// that verifies against the model they handed in — which before this lift
    /// was impossible, because the reduction was skipped whenever capture was
    /// armed.
    #[test]
    fn a_capturing_solve_that_fires_the_substitution_returns_liftable_evidence() {
        // Already holds the lock in its own right (it MUTATES the environment);
        // `solve_lock` is the same mutex and must not be taken twice.
        let _env_lock = ay_test_support::env::lock_env();
        let _on = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
            crate::tune::Knob::SingletonSub,
            crate::tune::Setting::Flag(true),
        ));

        let original = singleton_case_split_model();
        assert!(
            crate::presolve::substitute_singletons(&original).is_some(),
            "control: the reduction fires on this model"
        );

        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(256)
            .with_time_limit(std::time::Duration::from_secs(30));
        match crate::bab::solve_milp(&original, &opts) {
            crate::Outcome::Infeasible { tree_cert, .. } => {
                let tree_cert = tree_cert.expect("the wired lift must deliver the artifact");
                assert_eq!(
                    tree_cert.verify(&original),
                    Ok(()),
                    "the certificate must verify against the CALLER's model"
                );
            }
            other => panic!("expected Infeasible with evidence, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // The duplicate-column dedup's lift.
    // -----------------------------------------------------------------------

    /// A model `dedup_columns` merges: `b0` and `b1` are indistinguishable
    /// (identical support — the partition row alone — same kind, same box), and
    /// `b2` is not (it also appears in row 1). The group's shared support holds
    /// the partition row, which is the merge's licence.
    fn dedup_model(c0: f64, c1: f64, c2: f64, second_row: (f64, f64)) -> Model {
        let mut m = Model::new();
        let b0 = m.add_binary_col();
        let b1 = m.add_binary_col();
        let b2 = m.add_binary_col();
        m.add_row(1.0, 1.0, &[(b0, 1.0), (b1, 1.0), (b2, 1.0)]);
        m.add_row(second_row.0, second_row.1, &[(b2, 1.0)]);
        m.set_objective(&[(b0, c0), (b1, c1), (b2, c2)], Sense::Minimize);
        m
    }

    #[test]
    fn dedup_farkas_round_trips_and_distributes_over_the_merged_twin() {
        // `b2 >= 2` is unsatisfiable for a binary, so both frames are
        // infeasible — and the reduced Farkas leaves a residual on the merged
        // twin `b1` that only its own box fact can clear.
        let original = dedup_model(1.0, 3.0, 5.0, (2.0, f64::INFINITY));
        let (reduced, map) = crate::bab::dedup_columns(&original).expect("b0 and b1 merge");
        assert_eq!(reduced.num_cols(), 2, "b1 is merged away");
        assert_eq!(map[1], None, "b1 is the removed twin");
        let kept = map[0].expect("b0 is kept (cheapest of the group)");
        let b2 = map[2].expect("b2 is its own group");

        let cert = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(1),
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(0),
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: kept,
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };
        assert_eq!(cert.verify(&reduced), Ok(()));
        assert!(
            cert.verify(&original).is_err(),
            "the reduced combination leaves a −1 on b1 in the caller's frame"
        );
        let _ = b2;

        let lift = DedupLift::new(&map).expect("a clean injection");
        let lifted = lift
            .lift_farkas(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert!(
            lifted.multipliers.iter().any(|m| matches!(
                m.fact,
                FactRef::ColBound { col, side: BoundSide::Lower } if col.index() == 1
            )),
            "the removed twin's own lower bound is what clears the residual: {:?}",
            lifted.multipliers
        );
    }

    #[test]
    fn dedup_optimality_round_trips_and_reattaches_the_merged_cost() {
        let _env = solve_lock();
        let original = dedup_model(1.0, 3.0, 5.0, (f64::NEG_INFINITY, 1.0));
        let (reduced, map) = crate::bab::dedup_columns(&original).expect("b0 and b1 merge");
        let kept = map[0].expect("b0 kept");
        let b2 = map[2].expect("b2 kept");

        // `min b0 + 5·b2` over `b0 + b2 = 1`: bound 1, from the partition row
        // plus 4 units of `b2`'s lower bound.
        let cert = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(kept.0, int(1)), (b2.0, int(5))],
            bound: int(1),
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(0),
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: b2,
                        side: BoundSide::Lower,
                    },
                    coeff: int(4),
                },
            ],
        };
        assert_eq!(cert.verify(&reduced), Ok(()));

        let lift = DedupLift::new(&map).expect("a clean injection");
        let lifted = lift
            .lift_optimality(&cert, &original)
            .expect("the lift must succeed");
        assert_eq!(lifted.verify(&original), Ok(()));
        assert_eq!(lifted.bound, int(1), "dedup folds no constant");
        assert_eq!(
            lifted.objective,
            vec![(0, int(1)), (1, int(3)), (2, int(5))],
            "the merged column's own cost is back in the claim"
        );

        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(0)
            .with_time_limit(std::time::Duration::from_secs(30));
        match crate::bab::solve_milp(&original, &opts) {
            crate::Outcome::Optimal { value, .. } => assert_eq!(value, lifted.bound),
            other => panic!("expected Optimal, got {other:?}"),
        }
    }

    /// THE HAZARD the dedup lift creates, and the seal closing it.
    ///
    /// The reduction's own rule keeps the CHEAPEST member of a group, which is
    /// what makes a reduced dual bound valid for the caller. Hand the lift a map
    /// that kept the DEARER one and the reduced certificate's bound is simply
    /// false in the caller's frame (5 against a true optimum of 1). The lift
    /// must not relabel it: the residual on the cheap twin can only be cleared
    /// by its UPPER bound, which moves the combination's constant, and the
    /// identity for the claimed bound then fails.
    #[test]
    fn a_dedup_bound_that_is_false_in_the_callers_frame_cannot_be_lifted() {
        let _env = solve_lock();
        let mut original = Model::new();
        let b0 = original.add_binary_col();
        let b1 = original.add_binary_col();
        original.add_row(1.0, 1.0, &[(b0, 1.0), (b1, 1.0)]);
        original.set_objective(&[(b0, 5.0), (b1, 1.0)], Sense::Minimize);

        // Deliberately the WRONG survivor: `b0` costs 5, `b1` costs 1.
        let map = vec![Some(Col(0)), None];
        let cert = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, int(5))],
            bound: int(5),
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(0),
                    side: BoundSide::Lower,
                },
                coeff: int(5),
            }],
        };

        let opts = crate::SolveOpts::new()
            .with_tree_cert_leaves(0)
            .with_time_limit(std::time::Duration::from_secs(30));
        match crate::bab::solve_milp(&original, &opts) {
            crate::Outcome::Optimal { value, .. } => {
                assert_eq!(value, int(1), "the caller-frame optimum is 1, not 5");
            }
            other => panic!("expected Optimal, got {other:?}"),
        }

        let lift = DedupLift::new(&map).expect("a clean injection");
        assert!(
            lift.lift_optimality(&cert, &original).is_none(),
            "a bound of 5 must not escape into a frame whose optimum is 1"
        );
    }

    #[test]
    fn the_dedup_lift_declines_what_it_cannot_translate() {
        let original = dedup_model(1.0, 3.0, 5.0, (f64::NEG_INFINITY, 1.0));
        let (reduced, map) = crate::bab::dedup_columns(&original).expect("merges");
        let lift = DedupLift::new(&map).expect("a clean injection");

        // (1) A reduced row index that does not exist.
        assert!(lift
            .lift_farkas(
                &FarkasCertificate {
                    multipliers: vec![Multiplier {
                        fact: FactRef::RowBound {
                            row: Row(original.num_rows() as u32),
                            side: BoundSide::Lower,
                        },
                        coeff: BigRational::one(),
                    }],
                },
                &original,
            )
            .is_none());

        // (2) A reduced column index that does not exist.
        assert!(lift
            .lift_farkas(
                &FarkasCertificate {
                    multipliers: vec![Multiplier {
                        fact: FactRef::ColBound {
                            col: Col(reduced.num_cols() as u32),
                            side: BoundSide::Lower,
                        },
                        coeff: BigRational::one(),
                    }],
                },
                &original,
            )
            .is_none());

        // (3) A map that is not an injection: two originals on one reduced
        //     column names no unique distribution, so there is no lift to build.
        assert!(DedupLift::new(&[Some(Col(0)), Some(Col(0))]).is_none());
        // ...and one with a hole in the reduced numbering.
        assert!(DedupLift::new(&[Some(Col(1))]).is_none());

        // (4) A foreign reduced objective.
        let kept = map[0].expect("b0 kept");
        let foreign = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(kept.0, int(1))],
            bound: BigRational::zero(),
            multipliers: Vec::new(),
        };
        assert!(lift.lift_optimality(&foreign, &original).is_none());
    }

    /// The reverse map is the one piece both new lifts share, and a wrong
    /// inversion would silently retarget every column fact.
    #[test]
    fn the_reverse_column_map_only_accepts_clean_injections() {
        assert_eq!(
            reverse_column_map(&[Some(Col(0)), None, Some(Col(1))]),
            Some(vec![0, 2])
        );
        assert_eq!(reverse_column_map(&[None, None]), Some(Vec::new()));
        assert_eq!(reverse_column_map(&[Some(Col(0)), Some(Col(0))]), None);
        assert_eq!(reverse_column_map(&[Some(Col(2)), Some(Col(0))]), None);
    }
}
