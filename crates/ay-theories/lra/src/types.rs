// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions and utility functions for LRA solver.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use smallvec::SmallVec;

use crate::rational::Rational;

/// Cached `BigRational::one()` to avoid heap allocation per call.
/// Used as default Farkas scale in 11+ call sites.
#[allow(dead_code)]
pub(crate) fn big_rational_one() -> &'static BigRational {
    use std::sync::OnceLock;
    static ONE: OnceLock<BigRational> = OnceLock::new();
    ONE.get_or_init(BigRational::one)
}

/// Cached `Rational::one()` for use as default Farkas scale (#8406).
/// Returns a static reference to avoid per-call allocation.
pub(crate) fn rational_one() -> &'static Rational {
    use std::sync::OnceLock;
    static ONE: OnceLock<Rational> = OnceLock::new();
    ONE.get_or_init(|| Rational::Small(1, 1))
}

#[allow(dead_code)]
pub(crate) fn add_sparse_term(coeffs: &mut Vec<(u32, BigRational)>, var: u32, coeff: BigRational) {
    if coeff.is_zero() {
        return;
    }
    match coeffs.binary_search_by_key(&var, |(existing_var, _)| *existing_var) {
        Ok(idx) => {
            coeffs[idx].1 += coeff;
            if coeffs[idx].1.is_zero() {
                coeffs.remove(idx);
            }
        }
        Err(idx) => coeffs.insert(idx, (var, coeff)),
    }
}

/// Normalize and merge sparse coefficient list (BigRational version for tests).
#[cfg(test)]
pub(crate) fn normalize_sparse_coeffs(
    mut coeffs: Vec<(u32, BigRational)>,
) -> Vec<(u32, BigRational)> {
    coeffs.retain(|(_, coeff)| !coeff.is_zero());
    coeffs.sort_unstable_by_key(|(var, _)| *var);

    let mut merged: Vec<(u32, BigRational)> = Vec::with_capacity(coeffs.len());
    for (var, coeff) in coeffs {
        if let Some((last_var, last_coeff)) = merged.last_mut() {
            if *last_var == var {
                *last_coeff += coeff;
                if last_coeff.is_zero() {
                    merged.pop();
                }
                continue;
            }
        }
        merged.push((var, coeff));
    }
    merged
}

/// Normalize and merge sparse coefficient list using fast Rational.
pub(crate) fn normalize_sparse_coeffs_rat(
    mut coeffs: Vec<(u32, Rational)>,
) -> Vec<(u32, Rational)> {
    coeffs.retain(|(_, coeff)| !coeff.is_zero());
    coeffs.sort_unstable_by_key(|(var, _)| *var);

    let mut merged: Vec<(u32, Rational)> = Vec::with_capacity(coeffs.len());
    for (var, coeff) in coeffs {
        if let Some((last_var, last_coeff)) = merged.last_mut() {
            if *last_var == var {
                *last_coeff += coeff;
                if last_coeff.is_zero() {
                    merged.pop();
                }
                continue;
            }
        }
        merged.push((var, coeff));
    }
    merged
}

/// Add a term to sparse coefficient list using fast Rational.
pub(crate) fn add_sparse_term_rat(coeffs: &mut Vec<(u32, Rational)>, var: u32, coeff: Rational) {
    if coeff.is_zero() {
        return;
    }
    match coeffs.binary_search_by_key(&var, |(existing_var, _)| *existing_var) {
        Ok(idx) => {
            coeffs[idx].1 += coeff;
            if coeffs[idx].1.is_zero() {
                coeffs.remove(idx);
            }
        }
        Err(idx) => coeffs.insert(idx, (var, coeff)),
    }
}

/// Entry in the column index: stores the row index and the position of the
/// variable's coefficient within that row's sorted coefficient vector.
///
/// This enables O(1) coefficient access during `update_nonbasic` and pivot
/// instead of O(log w) binary search via `coeff_ref()`.
///
/// Reference: Z3 `sparse_matrix.h:76-85` stores `m_row_id` and `m_row_idx`
/// (position within the row) in each column entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ColEntry {
    /// Index into `LraSolver::rows`.
    pub(crate) row_idx: usize,
    /// Position of this variable in `rows[row_idx].coeffs`.
    /// Enables O(1) coefficient access without binary search.
    pub(crate) row_pos: usize,
}

/// #inc-dense-sets: epoch-stamped set of dense `usize` indices (rows/vars),
/// replacing `HashSet<usize>` on hot per-backtrack paths where SipHash was
/// pure overhead. `insert`/`contains` are O(1) array ops; `clear` is an O(1)
/// epoch bump (stamps re-zeroed once per 2^32 clears); iteration walks the
/// deduplicated insertion-order `entries` list (more deterministic than
/// HashSet order). API mirrors the `HashSet` subset used by callers, and
/// `Default` starts at epoch 1 so `std::mem::take` leaves a valid empty set.
#[derive(Debug, Clone)]
pub(crate) struct DenseIdxSet {
    stamps: Vec<u32>,
    epoch: u32,
    entries: Vec<usize>,
}

impl Default for DenseIdxSet {
    fn default() -> Self {
        Self {
            stamps: Vec::new(),
            epoch: 1,
            entries: Vec::new(),
        }
    }
}

impl DenseIdxSet {
    #[inline]
    pub(crate) fn insert(&mut self, idx: usize) -> bool {
        if idx >= self.stamps.len() {
            self.stamps.resize(idx + 1, 0);
        }
        if self.stamps[idx] == self.epoch {
            return false;
        }
        self.stamps[idx] = self.epoch;
        self.entries.push(idx);
        true
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            // Wrap once per 2^32 clears: re-zero so no stale stamp matches.
            for s in self.stamps.iter_mut() {
                *s = 0;
            }
            self.epoch = 1;
        }
    }

    #[inline]
    pub(crate) fn iter(&self) -> std::slice::Iter<'_, usize> {
        self.entries.iter()
    }

    #[inline]
    pub(crate) fn extend<I>(&mut self, it: I)
    where
        I: IntoIterator,
        I::Item: std::borrow::Borrow<usize>,
    {
        use std::borrow::Borrow;
        for i in it {
            self.insert(*i.borrow());
        }
    }
}

impl<'a> IntoIterator for &'a DenseIdxSet {
    type Item = &'a usize;
    type IntoIter = std::slice::Iter<'a, usize>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

/// #inc-dense-sets: `u32`-keyed twin of [`DenseIdxSet`] for dense variable
/// ids (`propagation_dirty_vars` etc.). Same epoch-stamp design; see above.
#[derive(Debug, Clone)]
pub(crate) struct DenseU32Set {
    stamps: Vec<u32>,
    epoch: u32,
    entries: Vec<u32>,
}

impl Default for DenseU32Set {
    fn default() -> Self {
        Self {
            stamps: Vec::new(),
            epoch: 1,
            entries: Vec::new(),
        }
    }
}

impl DenseU32Set {
    /// Test-only membership probe (production paths never query membership;
    /// they rely on `insert`'s return value).
    #[cfg(test)]
    #[inline]
    pub(crate) fn contains(&self, v: &u32) -> bool {
        let i = *v as usize;
        i < self.stamps.len() && self.stamps[i] == self.epoch
    }

    #[inline]
    pub(crate) fn insert(&mut self, v: u32) -> bool {
        let i = v as usize;
        if i >= self.stamps.len() {
            self.stamps.resize(i + 1, 0);
        }
        if self.stamps[i] == self.epoch {
            return false;
        }
        self.stamps[i] = self.epoch;
        self.entries.push(v);
        true
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            for s in self.stamps.iter_mut() {
                *s = 0;
            }
            self.epoch = 1;
        }
    }

    #[inline]
    pub(crate) fn iter(&self) -> std::slice::Iter<'_, u32> {
        self.entries.iter()
    }

    #[inline]
    pub(crate) fn extend<I>(&mut self, it: I)
    where
        I: IntoIterator,
        I::Item: std::borrow::Borrow<u32>,
    {
        use std::borrow::Borrow;
        for v in it {
            self.insert(*v.borrow());
        }
    }
}

impl<'a> IntoIterator for &'a DenseU32Set {
    type Item = &'a u32;
    type IntoIter = std::slice::Iter<'a, u32>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

impl ColEntry {
    #[inline]
    pub(crate) fn new(row_idx: usize, row_pos: usize) -> Self {
        Self { row_idx, row_pos }
    }
}

mod bound_state;
pub use bound_state::{Bound, BoundProvenance, VarStatus};
pub(crate) use bound_state::{
    BoundExplanation, BoundType, ErrorKey, ExprInterval, ImpliedBound, InfRational,
    IntervalEndpoint, RowPrecision, TableauRow, VarInfo,
};
// Re-exported here so existing `use types::LinearExpr` imports continue to work.
pub use crate::linear_expr::LinearExpr;

/// Model extracted from LRA solver with variable assignments
#[derive(Debug, Clone)]
pub struct LraModel {
    /// Variable assignments: term_id -> rational value
    pub values: HashMap<TermId, BigRational>,
}

/// Optimization direction for linear objective optimization
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationSense {
    /// Minimize the objective
    Minimize,
    /// Maximize the objective
    Maximize,
}

/// Result of an optimization query
#[derive(Debug, Clone)]
pub enum OptimizationResult {
    /// Optimal value found (the constraints are satisfiable and the objective has a finite optimum)
    Optimal(BigRational),
    /// The objective has a finite SUPREMUM `value` that is NOT attained: the
    /// delta-rational simplex terminated at `value + eps_coeff * epsilon` with
    /// `eps_coeff != 0` (Dutertre–de Moura delta-rationals; strict bounds are
    /// open faces, so the optimum is approached but never reached).
    ///
    /// Sign convention: minimize ⇒ `eps_coeff > 0` (infimum approached from
    /// above), maximize ⇒ `eps_coeff < 0` (supremum approached from below).
    /// `eps_coeff == 0` is never used here — that is exactly [`Self::Optimal`].
    /// No dual certificate is extracted for unattained optima (Phase A).
    OptimalInf {
        /// The finite part of the delta-optimum: the unattained sup/inf.
        value: BigRational,
        /// The (signed, nonzero) epsilon coefficient of the delta-optimum.
        eps_coeff: BigRational,
    },
    /// The objective is unbounded in the requested direction
    Unbounded,
    /// The constraints are infeasible
    Infeasible,
    /// Optimization could not be completed (e.g., iteration limit reached)
    Unknown,
}

/// Cached information about a parsed atom
#[derive(Clone)]
pub(crate) struct ParsedAtomInfo {
    /// The normalized linear expression (expr such that "expr op 0" is the constraint)
    pub(crate) expr: LinearExpr,
    /// Is this a <= constraint (vs >=)?
    pub(crate) is_le: bool,
    /// Is this a strict comparison (< or >)?
    pub(crate) strict: bool,
    /// Is this an equality atom (= symbol)?
    pub(crate) is_eq: bool,
    /// Is this a distinct atom (distinct symbol)?
    /// When true, semantics are inverted: value=true means disequality, value=false means equality
    pub(crate) is_distinct: bool,
    /// Whether parsing this atom triggered unsupported sub-expressions (#6167).
    /// Cached alongside the parse result so register_atom() → check() cache hits
    /// preserve the unsupported status.
    pub(crate) has_unsupported: bool,
    /// Precomputed slack variable for compound atoms (coeffs.len() > 1).
    /// Set during register_atom to avoid per-assertion Vec alloc + sort in assert_literal.
    pub(crate) compound_slack: Option<u32>,
}

/// A reference to a registered theory atom for bound propagation.
///
/// Stores the information needed to check if a variable's current bounds
/// imply the truth value of this atom. Used by same-variable chain
/// propagation (Z3 Component 3).
///
/// Reference: Z3 `theory_lra.cpp:2924-2984`
#[derive(Debug, Clone)]
pub(crate) struct AtomRef {
    /// The original theory atom term
    pub(crate) term: TermId,
    /// The bound value `k` where the atom is `var <= k` or `var >= k`.
    /// #8406: Changed from BigRational to Rational to eliminate heap allocation
    /// in `cmp_big` during bound propagation. All comparisons in `bound_is_interesting`,
    /// `compute_bound_propagations_for_vars`, and `compute_direct_bound_propagations_for_var`
    /// now use pure i128 arithmetic for the common Small/Small case.
    pub(crate) bound_value: Rational,
    /// true for `var <= k` (upper bound atom), false for `var >= k` (lower bound atom)
    pub(crate) is_upper: bool,
    /// true for strict comparisons (< or >)
    pub(crate) strict: bool,
}

/// A Gomory cutting plane
#[derive(Debug, Clone)]
pub struct GomoryCut {
    /// Coefficients: (internal_var_id, coefficient)
    pub coeffs: Vec<(u32, BigRational)>,
    /// The bound value (RHS of the inequality)
    pub bound: BigRational,
    /// True for >= constraint (lower bound), false for <= (upper bound)
    pub is_lower: bool,
    /// Active bound literals that justify the cut (keeps branch-local cuts scoped).
    pub reasons: Vec<(TermId, bool)>,
    /// Basic variable whose tableau row generated this cut (LIA safety check).
    pub source_term: Option<TermId>,
}

impl GomoryCut {
    /// Returns true if all coefficients and the bound fit in machine integers.
    ///
    /// Small cuts are numerically stable and can be added permanently.
    /// Big cuts should be tested tentatively via push/pop before committing.
    /// Reference: Z3 gomory.cpp:489-491 `is_small_cut`
    pub fn is_small(&self) -> bool {
        use num_traits::ToPrimitive;
        let fits = |r: &BigRational| r.numer().to_i64().is_some() && r.denom().to_i64().is_some();
        self.coeffs.iter().all(|(_, c)| fits(c)) && fits(&self.bound)
    }
}

/// Row information for GCD test
///
/// Contains the coefficients and constant of a tableau row:
/// basic_var = Σ(coeff * var) + constant
///
/// Used by LIA to perform GCD tests on rows where the basic variable
/// has a non-integer value.
#[derive(Debug, Clone)]
pub struct GcdRowInfo {
    /// The basic variable for this row (internal var ID)
    pub basic_var: u32,
    /// The corresponding term ID (if mapped)
    pub basic_term: Option<TermId>,
    /// Sparse coefficients: (internal_var_id, coefficient)
    pub coeffs: Vec<(u32, BigRational)>,
    /// Constant term
    pub constant: BigRational,
    /// Lower bound on basic_var (if any)
    pub lower_bound: Option<BigRational>,
    /// Upper bound on basic_var (if any)
    pub upper_bound: Option<BigRational>,
    /// Whether variable is fixed (lower == upper)
    pub is_fixed: bool,
    /// Whether variable is bounded on both sides
    pub is_bounded: bool,
}

/// Compute the fractional part of a rational number
/// frac(x) = x - floor(x), always in [0, 1)
pub(crate) fn fractional_part(val: &BigRational) -> BigRational {
    let numer = val.numer();
    let denom = val.denom();

    // floor(n/d) for positive d
    let floor_val = if numer.is_negative() {
        // For negative numbers: floor(n/d) = (n - d + 1) / d for d > 0
        (numer - denom + BigInt::one()) / denom
    } else {
        numer / denom
    };

    val - BigRational::from(floor_val)
}
