// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Dense, var-indexed cutting-planes accumulator (`DenseCp`).
//!
//! This is a reusable scratch buffer mirroring [`CpConstraint`] semantics
//! exactly, but designed to avoid per-operation allocation during conflict
//! analysis. It follows RoundingSat's `ConstrExp` design: a single growable
//! `Vec<i128>` indexed by literal, an epoch/stamp scheme for O(1) membership,
//! and a `touched` list so `clear()` is O(touched) without reallocating the
//! coefficient backing store.
//!
//! Literal index encoding: for `PbLit { var (1-indexed), negated }`,
//! `index = 2 * (var - 1) + (negated as usize)`. Complementary literals (`l`
//! and `~l`) therefore differ by `XOR 1`.
//!
//! Every operation reproduces [`CpConstraint`]'s arithmetic faithfully,
//! including the order of normalization steps, complementary cancellation,
//! checked overflow handling, and the round-to-one overflow fallback. The
//! correctness oracle is the differential test module against the trusted
//! [`CpConstraint`] implementation.
//
// NOTE: This module is intentionally not yet wired into the solver (the
// conflict-analysis integration is a later step). Its full surface is
// exercised only by the differential test module below, so the entire API
// is dead code in non-test builds until integration lands.
#![allow(dead_code)]

use crate::cutting_planes::{
    div_ceil_i64, gcd_i64, lcm_i64, CpConstraint, CpError, RoundToOneResult,
};
use crate::types::{PbConstraint, PbLit, PbRel, PbTerm};

/// Encodes a literal as a dense index: `2 * (var - 1) + negated`.
#[inline]
fn lit_index(lit: PbLit) -> usize {
    debug_assert!(lit.var >= 1, "PbLit var must be 1-indexed");
    2 * (lit.var as usize - 1) + usize::from(lit.negated)
}

/// Decodes a dense index back into a [`PbLit`].
#[inline]
fn index_lit(index: usize) -> PbLit {
    PbLit {
        var: (index / 2) as u32 + 1,
        negated: (index & 1) == 1,
    }
}

/// Capture of one PROVEN round-to-one resolution step for the proof tap
/// (proof-tap spec, record kind PROVEN_RESOLVE). Filled by
/// [`DenseCp::resolve_proven_round_to_one_captured`]; all values are
/// post-orientation (relative to the conflict/reason roles actually resolved).
#[derive(Debug, Clone, Default)]
pub(crate) struct ProvenResolveCapture {
    /// Reason coefficient of the asserted pivot (the round-to-one divisor).
    pub(crate) c: i128,
    /// Conflict coefficient of the falsified pivot (the reason multiplier).
    pub(crate) w: i128,
    /// Exactly the `(reason literal, remainder)` pairs partially weakened
    /// before division, in application order (`rem == coeff` full-zeroing
    /// uses the same pair encoding).
    pub(crate) weakened: Vec<(PbLit, i128)>,
}

/// Capture of one heuristic (add-then-divide) resolution step for the proof
/// tap (record kind HEURISTIC_RESOLVE). `conflict_factor` multiplies the
/// RUNNING CONFLICT side, `reason_factor` the reason — normalized to that
/// convention regardless of the internal pivot orientation.
#[derive(Debug, Clone, Default)]
pub(crate) struct HeuristicResolveCapture {
    pub(crate) conflict_factor: i128,
    pub(crate) reason_factor: i128,
    /// Round-to-one divisor applied to the (saturated) resolvent, if any.
    pub(crate) div: Option<i128>,
}

/// A reusable, var-indexed dense cutting-planes accumulator.
///
/// Mirrors [`CpConstraint`] semantics exactly while avoiding per-operation
/// allocation. Reuse a single instance across many conflicts: [`DenseCp::clear`]
/// resets state in O(touched) without freeing the backing buffers.
#[derive(Debug, Clone)]
pub(crate) struct DenseCp {
    /// Coefficient per literal index (`0` means absent). Length is always
    /// `>= 2 * num_vars`; entries are only meaningful when stamped to the
    /// current `epoch`.
    coeffs: Vec<i128>,
    /// Stamp per literal index. Index `i` holds a nonzero coefficient iff
    /// `stamp[i] == epoch`. Allows O(1) membership and O(touched) clears.
    stamp: Vec<u32>,
    /// Indices currently stamped to `epoch` (the active support set).
    touched: Vec<u32>,
    /// Current epoch; bumped on every [`DenseCp::clear`].
    epoch: u32,
    /// Right-hand side.
    degree: i128,
}

impl Default for DenseCp {
    /// Returns a valid empty accumulator (`epoch == 1`), identical to
    /// [`DenseCp::new`]. Used as an allocation-free placeholder when temporarily
    /// moving a reusable buffer out of its owner via [`std::mem::take`].
    fn default() -> Self {
        Self::new()
    }
}

impl DenseCp {
    /// Creates an empty accumulator with capacity for `num_vars` variables.
    pub(crate) fn with_num_vars(num_vars: usize) -> Self {
        let cap = num_vars.saturating_mul(2);
        Self {
            coeffs: vec![0; cap],
            stamp: vec![0; cap],
            touched: Vec::new(),
            epoch: 1,
            degree: 0,
        }
    }

    /// Creates an empty accumulator with no preallocated capacity.
    pub(crate) fn new() -> Self {
        Self::with_num_vars(0)
    }

    /// Ensures the backing buffers can hold `index`.
    #[inline]
    fn ensure_index(&mut self, index: usize) {
        if index >= self.coeffs.len() {
            // Grow generously to amortize. Buffers grow but are never shrunk,
            // so reuse across conflicts incurs no further allocation.
            let new_len = (index + 1).next_power_of_two();
            self.coeffs.resize(new_len, 0);
            self.stamp.resize(new_len, 0);
        }
    }

    /// Returns whether `index` currently holds a (nonzero) coefficient.
    #[inline]
    fn is_set(&self, index: usize) -> bool {
        index < self.stamp.len() && self.stamp[index] == self.epoch
    }

    /// Returns the coefficient at `index` (0 if absent).
    #[inline]
    fn get_index(&self, index: usize) -> i128 {
        if self.is_set(index) {
            self.coeffs[index]
        } else {
            0
        }
    }

    /// Sets the coefficient at `index`, maintaining the touched/stamp state.
    ///
    /// Setting to zero removes the entry from the active support (logically),
    /// but leaves it in `touched`; callers that need a clean support set must
    /// call [`DenseCp::compact`].
    #[inline]
    fn set_index(&mut self, index: usize, value: i128) {
        self.ensure_index(index);
        if self.stamp[index] != self.epoch {
            // First time this index is touched in the current epoch.
            self.stamp[index] = self.epoch;
            self.touched.push(index as u32);
        }
        self.coeffs[index] = value;
    }

    /// Adds `delta` to the coefficient at `index`, with checked arithmetic.
    #[inline]
    fn add_index(&mut self, index: usize, delta: i128) -> Result<(), CpError> {
        let current = self.get_index(index);
        let next = current
            .checked_add(delta)
            .ok_or(CpError::CoefficientOverflow)?;
        self.set_index(index, next);
        Ok(())
    }

    /// Resets the accumulator in O(touched) without freeing buffers.
    pub(crate) fn clear(&mut self) {
        // Zero the coefficients of touched indices so that, even if the epoch
        // wraps (extremely unlikely), no stale nonzero coefficient is read.
        for &idx in &self.touched {
            self.coeffs[idx as usize] = 0;
        }
        self.touched.clear();
        self.degree = 0;
        // Bump epoch; on wrap, fully reset stamps.
        match self.epoch.checked_add(1) {
            Some(next) => self.epoch = next,
            None => {
                self.stamp.fill(0);
                self.epoch = 1;
            }
        }
    }

    /// Overwrites `self` with an exact copy of `src`, in O(`src` support)
    /// WITHOUT allocating — the drop-in replacement for `clone()` on the hot
    /// conflict-analysis path.
    ///
    /// WHY THIS EXISTS. `clone()` copies the whole backing store: `coeffs` and
    /// `stamp` are `2 * num_vars` rounded up to a power of two, so once OLL has
    /// grown the variable set to ~2k the two clones in
    /// [`Self::resolve_proven_round_to_one_impl`] copied ~81 KB EACH, twice per
    /// resolution step, tens of steps per conflict — around 10 MB of memcpy per
    /// conflict, plus fresh allocations the allocator then had to `mmap`. That
    /// alone caps the solver near 1k conflicts/sec regardless of search quality.
    /// The support is typically a few dozen literals, so copying `touched`
    /// instead of the whole array is the difference between O(num_vars) and
    /// O(support).
    ///
    /// EXACTNESS. Entries that are stamped but hold a zero coefficient (i.e.
    /// `compact` has not run) are mirrored too, rather than dropped. Dropping
    /// them would be semantically equivalent today — `iter_entries` filters
    /// zeros and `coefficient` returns 0 either way — but it would change
    /// `touched` ordering after a later re-add of the same index, and the point
    /// of this routine is to be indistinguishable from `clone`.
    pub(crate) fn copy_from(&mut self, src: &Self) {
        self.clear();
        self.degree = src.degree;
        self.touched.reserve(src.touched.len());
        for &idx in &src.touched {
            let i = idx as usize;
            debug_assert_eq!(
                src.stamp[i], src.epoch,
                "`touched` must only contain indices stamped to the current epoch"
            );
            self.set_index(i, src.coeffs[i]);
        }
    }

    /// Returns the degree (right-hand side).
    pub(crate) fn degree(&self) -> i128 {
        self.degree
    }

    /// Returns the coefficient of a literal, or `0` when absent.
    pub(crate) fn coefficient(&self, lit: PbLit) -> i128 {
        self.get_index(lit_index(lit))
    }

    /// Returns the number of terms (nonzero coefficients) in the constraint.
    pub(crate) fn len(&self) -> usize {
        self.touched
            .iter()
            .filter(|&&idx| self.coeffs[idx as usize] != 0)
            .count()
    }

    /// Returns whether the constraint has no terms.
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterates over `(lit, coeff)` pairs for all active nonzero terms.
    ///
    /// Read-only accessor mirroring [`CpConstraint::coefficients`] iteration.
    /// The order matches the insertion order in `touched`; callers must not
    /// rely on ordering for canonical output (use [`DenseCp::to_cp_constraint`]
    /// or [`DenseCp::sorted_terms`] for that).
    pub(crate) fn iter_terms(&self) -> impl Iterator<Item = (PbLit, i128)> + '_ {
        self.iter_entries().map(|(idx, c)| (index_lit(idx), c))
    }

    /// Iterates over `(index, coeff)` pairs for all active nonzero entries.
    ///
    /// The order matches the insertion order in `touched`; callers must not
    /// rely on ordering for canonical output (use [`DenseCp::to_cp_constraint`]
    /// or [`DenseCp::sorted_terms`] for that).
    fn iter_entries(&self) -> impl Iterator<Item = (usize, i128)> + '_ {
        self.touched.iter().filter_map(move |&idx| {
            let i = idx as usize;
            let c = self.coeffs[i];
            if self.stamp[i] == self.epoch && c != 0 {
                Some((i, c))
            } else {
                None
            }
        })
    }

    // -- Loaders -------------------------------------------------------------

    /// Loads this accumulator from a [`CpConstraint`] (clearing first).
    ///
    /// The source is assumed already normalized, so the dense copy is exact.
    pub(crate) fn load_from_cp(&mut self, source: &CpConstraint) {
        self.clear();
        for (&lit, &coeff) in source.coefficients() {
            if coeff != 0 {
                self.set_index(lit_index(lit), coeff);
            }
        }
        self.degree = source.degree();
    }

    /// Loads this accumulator from a `>=` [`PbConstraint`] and normalizes,
    /// mirroring `CpConstraint::try_from(&PbConstraint)`.
    pub(crate) fn load_from_pb(&mut self, source: &PbConstraint) -> Result<(), CpError> {
        if source.rel != PbRel::Ge {
            return Err(CpError::UnsupportedRelation(source.rel));
        }
        self.clear();
        self.degree = source.rhs;
        for (index, term) in source.terms.iter().enumerate() {
            if term.lits.len() != 1 {
                return Err(CpError::NonLinearTerm {
                    term_index: index,
                    lit_count: term.lits.len(),
                });
            }
            self.add_index(lit_index(term.lits[0]), term.coeff)?;
        }
        self.normalize()?;
        Ok(())
    }

    // -- Core normalization --------------------------------------------------

    /// Removes entries whose coefficient is zero from the active support.
    ///
    /// Mirrors `CpConstraint::compact`. After this, `touched` contains only
    /// nonzero, currently-stamped indices.
    fn compact(&mut self) {
        let epoch = self.epoch;
        let mut write = 0;
        let mut i = 0;
        while i < self.touched.len() {
            let idx = self.touched[i] as usize;
            if self.stamp[idx] == epoch && self.coeffs[idx] != 0 {
                self.touched[write] = self.touched[i];
                write += 1;
            } else {
                // Drop: reset the slot so a future re-add re-registers it in
                // `touched`. Clearing only the coefficient (but leaving the
                // stamp at the current epoch) would make a re-added entry
                // invisible to `iter_entries`.
                self.coeffs[idx] = 0;
                self.stamp[idx] = 0;
            }
            i += 1;
        }
        self.touched.truncate(write);
    }

    /// Mirrors `CpConstraint::simplify_trivial`: when the degree is
    /// non-positive, the constraint is trivially satisfied — degree becomes 0
    /// and all terms are dropped. Otherwise just compact.
    fn simplify_trivial(&mut self) {
        if self.degree <= 0 {
            self.degree = 0;
            self.clear_terms_only();
        } else {
            self.compact();
        }
    }

    /// Drops all terms but preserves the degree.
    ///
    /// Resets both the coefficient and the stamp for every dropped index so
    /// that a subsequent `set_index`/`add_index` re-registers it in `touched`.
    /// (Leaving a stale stamp at the current epoch would make a re-added entry
    /// invisible to `iter_entries`, silently dropping it.)
    fn clear_terms_only(&mut self) {
        for &idx in &self.touched {
            let i = idx as usize;
            self.coeffs[i] = 0;
            self.stamp[i] = 0;
        }
        self.touched.clear();
    }

    /// Mirrors `CpConstraint::normalize`: flip negative coefficients to the
    /// complementary literal (subtracting the negative coeff from the degree),
    /// cancel complementary pairs, compact, and simplify trivial.
    pub(crate) fn normalize(&mut self) -> Result<(), CpError> {
        // First pass: collect current entries, then rebuild flipping negatives.
        // We snapshot indices/coeffs because we mutate during rebuild.
        let entries: Vec<(usize, i128)> = self.iter_entries().collect();

        // Clear the support but keep the degree; we will re-add normalized terms.
        self.clear_terms_only();

        for (index, coeff) in entries {
            if coeff == 0 {
                continue;
            }
            if coeff > 0 {
                self.add_index(index, coeff)?;
            } else {
                // coeff < 0: flip to complementary literal with positive coeff.
                let positive_coeff = coeff.checked_abs().ok_or(CpError::CoefficientOverflow)?;
                let comp = index ^ 1;
                self.add_index(comp, positive_coeff)?;
                // degree -= coeff (coeff is negative, so this increases degree).
                self.degree = self
                    .degree
                    .checked_sub(coeff)
                    .ok_or(CpError::CoefficientOverflow)?;
            }
        }

        self.cancel_complementary_literals()?;
        self.compact();
        self.simplify_trivial();
        Ok(())
    }

    /// Mirrors `CpConstraint::cancel_complementary_literals`.
    ///
    /// For each variable where both `x` and `~x` carry positive coefficients,
    /// subtract `shared = min(pos, neg)` from both coefficients and from the
    /// degree (the identity `x + ~x = 1` contributes `shared` unconditionally).
    fn cancel_complementary_literals(&mut self) -> Result<(), CpError> {
        // Iterate over the even (positive-literal) indices currently present;
        // pair each with its complementary odd index. We snapshot to avoid
        // mutation-during-iteration issues.
        let entries: Vec<usize> = self.iter_entries().map(|(idx, _)| idx).collect();
        // Track which variable bases we've handled to avoid double-processing
        // (each pair is reachable from both its even and odd index).
        let mut handled: Vec<usize> = Vec::new();
        for idx in entries {
            let base = idx & !1usize; // even index for this variable
            if handled.contains(&base) {
                continue;
            }
            let pos = self.get_index(base);
            let neg = self.get_index(base | 1);
            if pos <= 0 || neg <= 0 {
                continue;
            }
            handled.push(base);
            let shared = pos.min(neg);
            self.degree = self
                .degree
                .checked_sub(shared)
                .ok_or(CpError::CoefficientOverflow)?;
            self.set_index(base, pos - shared);
            self.set_index(base | 1, neg - shared);
        }
        Ok(())
    }

    // -- Arithmetic ops ------------------------------------------------------

    /// Mirrors `CpConstraint::multiply` (panics on overflow in the original;
    /// here we surface overflow via the checked variant). To match the
    /// original's `multiply` exactly (which panics), use this method on inputs
    /// known to fit; for fallible behavior use [`DenseCp::multiply_checked`].
    pub(crate) fn multiply(&mut self, factor: i128) -> Result<(), CpError> {
        // The trusted `multiply` panics on overflow; we use checked arithmetic
        // and return Err instead (strictly safer; differential tests stay in
        // the non-overflowing range for `multiply`).
        self.multiply_checked(factor)
    }

    /// Mirrors `CpConstraint::multiply_checked`: scales every coefficient and
    /// the degree by a positive `factor`, returning Err on overflow.
    pub(crate) fn multiply_checked(&mut self, factor: i128) -> Result<(), CpError> {
        if factor <= 0 {
            return Err(CpError::NonPositiveMultiplier(factor));
        }
        // Collect indices first; we only scale existing nonzero entries.
        let indices: Vec<usize> = self.iter_entries().map(|(idx, _)| idx).collect();
        for idx in indices {
            let scaled = self.coeffs[idx]
                .checked_mul(factor)
                .ok_or(CpError::CoefficientOverflow)?;
            self.coeffs[idx] = scaled;
        }
        self.degree = self
            .degree
            .checked_mul(factor)
            .ok_or(CpError::CoefficientOverflow)?;
        self.simplify_trivial();
        Ok(())
    }

    /// Mirrors `CpConstraint::divide`: ceiling-divide all coefficients and the
    /// degree by a positive `divisor`, then normalize.
    pub(crate) fn divide(&mut self, divisor: i128) -> Result<(), CpError> {
        if divisor <= 0 {
            return Err(CpError::NonPositiveDivisor(divisor));
        }
        let indices: Vec<usize> = self.iter_entries().map(|(idx, _)| idx).collect();
        for idx in indices {
            self.coeffs[idx] = div_ceil_i64(self.coeffs[idx], divisor);
        }
        self.degree = div_ceil_i64(self.degree, divisor);
        self.normalize()
    }

    /// Mirrors `CpConstraint::gcd_divide`: divide by the GCD of all coefficients
    /// when that GCD exceeds 1.
    ///
    /// Returns the computed GCD (`0` for an empty constraint, `1` when no
    /// division was applied). Callers replaying the derivation into a proof
    /// need the divisor; a returned value `> 1` means the constraint WAS
    /// divided by exactly that amount.
    pub(crate) fn gcd_divide(&mut self) -> Result<i128, CpError> {
        let gcd = self.iter_entries().map(|(_, c)| c).fold(0, gcd_i64);
        if gcd > 1 {
            self.divide(gcd)?;
        }
        Ok(gcd)
    }

    /// Mirrors `CpConstraint::saturate`: cap each coefficient at the degree.
    pub(crate) fn saturate(&mut self) {
        if self.degree == 0 {
            self.clear_terms_only();
            return;
        }
        let indices: Vec<usize> = self.iter_entries().map(|(idx, _)| idx).collect();
        for idx in indices {
            self.coeffs[idx] = self.coeffs[idx].min(self.degree);
        }
        self.compact();
    }

    /// Mirrors `CpConstraint::saturate_and_gcd`.
    pub(crate) fn saturate_and_gcd(&mut self) -> Result<(), CpError> {
        self.saturate();
        self.gcd_divide().map(|_| ())
    }

    /// Mirrors `CpConstraint::weaken`: remove a literal and reduce the degree.
    pub(crate) fn weaken(&mut self, lit: PbLit) {
        let index = lit_index(lit);
        if self.is_set(index) && self.coeffs[index] != 0 {
            let coeff = self.coeffs[index];
            self.coeffs[index] = 0;
            self.degree = self.degree.saturating_sub(coeff).max(0);
            self.simplify_trivial();
        }
    }

    /// Adds `other` into `self` coefficient-wise (mirrors
    /// `CpConstraint::add_assign`). Both operands must be normalized for the
    /// result to match the trusted `addition`.
    pub(crate) fn add_assign(&mut self, other: &Self) -> Result<(), CpError> {
        for (idx, coeff) in other.iter_entries() {
            self.add_index(idx, coeff)?;
        }
        self.degree = self
            .degree
            .checked_add(other.degree)
            .ok_or(CpError::CoefficientOverflow)?;
        self.compact();
        self.simplify_trivial();
        Ok(())
    }

    /// Adds `other` scaled by `factor` into `self`.
    ///
    /// Convenience combination of scaling + addition; `factor` must be
    /// positive. This is the dense analogue used by resolution.
    pub(crate) fn add_scaled(&mut self, other: &Self, factor: i128) -> Result<(), CpError> {
        if factor <= 0 {
            return Err(CpError::NonPositiveMultiplier(factor));
        }
        for (idx, coeff) in other.iter_entries() {
            let scaled = coeff
                .checked_mul(factor)
                .ok_or(CpError::CoefficientOverflow)?;
            self.add_index(idx, scaled)?;
        }
        let scaled_degree = other
            .degree
            .checked_mul(factor)
            .ok_or(CpError::CoefficientOverflow)?;
        self.degree = self
            .degree
            .checked_add(scaled_degree)
            .ok_or(CpError::CoefficientOverflow)?;
        self.compact();
        self.simplify_trivial();
        Ok(())
    }

    /// Mirrors `CpConstraint::weaken_conservative`.
    ///
    /// Removes non-asserting literals with the smallest coefficients while
    /// preserving the asserting property. See the trusted implementation for
    /// the exact preservation conditions.
    pub(crate) fn weaken_conservative<F>(&mut self, asserting_lit: Option<PbLit>, falsified_fn: F)
    where
        F: FnMut(PbLit) -> Option<u32>,
    {
        self.weaken_conservative_captured(asserting_lit, falsified_fn, None);
    }

    /// [`Self::weaken_conservative`] with proof-tap capture: identical
    /// weakening decisions, additionally appending each removed literal to
    /// `removed` in application order (VeriPB `w` replays are order-exact
    /// because every removal adjusts the degree).
    pub(crate) fn weaken_conservative_captured<F>(
        &mut self,
        asserting_lit: Option<PbLit>,
        mut falsified_fn: F,
        mut removed: Option<&mut Vec<PbLit>>,
    ) where
        F: FnMut(PbLit) -> Option<u32>,
    {
        let Some(asserting) = asserting_lit else {
            return;
        };
        let asserting_index = lit_index(asserting);

        // Candidates: non-asserting literals sorted by coefficient ascending.
        let mut candidates: Vec<(usize, i128)> = self
            .iter_entries()
            .filter(|&(idx, _)| idx != asserting_index)
            .collect();
        candidates.sort_by_key(|&(_, coeff)| coeff);

        for (lit_idx, coeff) in candidates {
            if coeff >= self.degree {
                continue;
            }
            let new_degree = self.degree.saturating_sub(coeff).max(0);
            if new_degree <= 0 {
                continue;
            }
            let asserting_coeff = self.get_index(asserting_index);
            if asserting_coeff <= 0 {
                break;
            }
            // Sum of remaining falsified coefficients (excluding asserting and
            // the candidate literal being weakened).
            let remaining_falsified_sum: i128 = self
                .iter_entries()
                .filter(|&(idx, _)| idx != asserting_index && idx != lit_idx)
                .filter(|&(idx, _)| falsified_fn(index_lit(idx)).is_some())
                .map(|(_, c)| c)
                .sum();
            if remaining_falsified_sum >= new_degree {
                continue;
            }
            // Apply the weakening.
            self.coeffs[lit_idx] = 0;
            self.degree = new_degree;
            if let Some(out) = removed.as_deref_mut() {
                out.push(index_lit(lit_idx));
            }
        }

        self.compact();
        self.simplify_trivial();
    }

    // -- Resolution ----------------------------------------------------------

    /// Mirrors `CpConstraint::resolve`: full PB resolution on `pivot`, used as
    /// the overflow fallback for round-to-one.
    ///
    /// `self` and `reason` are the two operands (order-independent; the side
    /// containing `pivot` and the side containing `!pivot` are detected).
    fn resolve(&self, reason: &Self, pivot: PbLit) -> Result<Self, CpError> {
        let negated_pivot = pivot_negate(pivot);
        let pivot_idx = lit_index(pivot);
        let neg_idx = lit_index(negated_pivot);

        let (left_base, right_base) = if self.is_set(pivot_idx)
            && self.coeffs[pivot_idx] != 0
            && reason.is_set(neg_idx)
            && reason.coeffs[neg_idx] != 0
        {
            (self, reason)
        } else if self.is_set(neg_idx)
            && self.coeffs[neg_idx] != 0
            && reason.is_set(pivot_idx)
            && reason.coeffs[pivot_idx] != 0
        {
            (reason, self)
        } else {
            return Err(CpError::InvalidResolvePivot { pivot });
        };

        let left_coeff = left_base.get_index(pivot_idx);
        let right_coeff = right_base.get_index(neg_idx);
        let lcm = lcm_i64(left_coeff, right_coeff);
        let left_factor = lcm / left_coeff;
        let right_factor = lcm / right_coeff;

        let mut left = left_base.clone();
        let mut right = right_base.clone();
        left.multiply(left_factor)?;
        right.multiply(right_factor)?;

        let mut result = Self::with_num_vars(0);
        // Match the original's capacity behaviour loosely; size to operands.
        result
            .coeffs
            .resize(self.coeffs.len().max(reason.coeffs.len()), 0);
        result
            .stamp
            .resize(self.coeffs.len().max(reason.coeffs.len()), 0);

        for (idx, coeff) in left.iter_entries() {
            if idx != pivot_idx {
                result.add_index(idx, coeff)?;
            }
        }
        for (idx, coeff) in right.iter_entries() {
            if idx != neg_idx {
                result.add_index(idx, coeff)?;
            }
        }

        result.degree = left
            .degree
            .checked_add(right.degree)
            .and_then(|sum| sum.checked_sub(lcm))
            .ok_or(CpError::CoefficientOverflow)?;

        result.simplify_trivial();
        result.saturate();
        result.gcd_divide()?;
        Ok(result)
    }

    /// Mirrors `CpConstraint::resolve_round_to_one`, returning the resolved
    /// dense constraint plus whether division was used.
    ///
    /// The overflow fallback semantics match the trusted implementation
    /// exactly: any checked-multiply overflow during scaling, or degree
    /// overflow during the cancel step, falls back to plain [`Self::resolve`]
    /// with `used_division = false`.
    pub(crate) fn resolve_round_to_one(
        &self,
        reason: &Self,
        pivot: PbLit,
        asserting_lit: Option<PbLit>,
    ) -> Result<DenseRoundToOneResult, CpError> {
        let negated_pivot = pivot_negate(pivot);
        let pivot_idx = lit_index(pivot);
        let neg_idx = lit_index(negated_pivot);

        let (pivot_side, negated_side) =
            if self.coefficient(pivot) > 0 && reason.coefficient(negated_pivot) > 0 {
                (self, reason)
            } else if self.coefficient(negated_pivot) > 0 && reason.coefficient(pivot) > 0 {
                (reason, self)
            } else {
                return Err(CpError::InvalidResolvePivot { pivot });
            };

        let a = pivot_side.coefficient(pivot);
        let b = negated_side.coefficient(negated_pivot);

        let g = gcd_i64(a, b);
        let left_factor = b / g;
        let right_factor = a / g;

        let mut scaled_left = pivot_side.clone();
        let mut scaled_right = negated_side.clone();

        if left_factor > 1 && scaled_left.multiply_checked(left_factor).is_err() {
            return self
                .resolve(reason, pivot)
                .map(|c| DenseRoundToOneResult::new(c, false));
        }
        if right_factor > 1 && scaled_right.multiply_checked(right_factor).is_err() {
            return self
                .resolve(reason, pivot)
                .map(|c| DenseRoundToOneResult::new(c, false));
        }

        let mut resolved = Self::with_num_vars(0);
        let cap = self.coeffs.len().max(reason.coeffs.len());
        resolved.coeffs.resize(cap, 0);
        resolved.stamp.resize(cap, 0);

        for (idx, coeff) in scaled_left.iter_entries() {
            if idx != pivot_idx {
                resolved.add_index(idx, coeff)?;
            }
        }
        for (idx, coeff) in scaled_right.iter_entries() {
            if idx != neg_idx {
                resolved.add_index(idx, coeff)?;
            }
        }

        let lcm = a / g * b;
        let degree = scaled_left
            .degree
            .checked_add(scaled_right.degree)
            .and_then(|sum| sum.checked_sub(lcm));
        let Some(degree) = degree else {
            return self
                .resolve(reason, pivot)
                .map(|c| DenseRoundToOneResult::new(c, false));
        };
        resolved.degree = degree;

        resolved.normalize()?;
        resolved.saturate();

        let mut used_division = false;
        if let Some(alit) = asserting_lit {
            let a_coeff = resolved.coefficient(alit);
            if a_coeff > 1 && resolved.divide(a_coeff).is_ok() {
                used_division = true;
            }
        }

        if !used_division {
            let _ = resolved.gcd_divide();
        }

        Ok(DenseRoundToOneResult::new(resolved, used_division))
    }

    /// PROVEN round-to-one resolution (Elffers & Nordstrom, IJCAI-18, Alg. 5/6;
    /// RoundingSat/Exact). Resolves the conflict constraint `self` with the
    /// reason `reason` on `pivot`, where:
    ///
    /// * `pivot` is the trail literal that `reason` propagated true — so
    ///   `reason` contains `pivot` with a positive coefficient and `pivot` is
    ///   true under the trail.
    /// * `self` (the running conflict) contains `~pivot` (the falsified pivot)
    ///   with a positive coefficient.
    ///
    /// Unlike [`Self::resolve_round_to_one`] (the heuristic "add-then-divide"
    /// rule), this REDUCES THE REASON before adding: it weakens the reason's
    /// non-falsified literals so the pivot coefficient divides them, divides the
    /// reason so the pivot coefficient becomes 1, then multiplies the reduced
    /// reason by the conflict's pivot coefficient and adds it into the conflict.
    /// The pivot pair cancels via the `p + ~p = 1` identity during normalize.
    ///
    /// SOUNDNESS: every step (weakening, ceiling-division, multiplication,
    /// addition, saturation) preserves logical implication, so the result is
    /// implied by `self ∧ reason`. Weakening targets ONLY non-falsified literals,
    /// which preserves the falsified-conflict (slack < 0) invariant.
    ///
    /// `falsified_fn` returns `true` iff a literal is falsified by the current
    /// trail. It is used (a) to choose which literals to weaken and (b) is the
    /// caller's contract for the slack invariant.
    ///
    /// Returns `Err(InvalidResolvePivot)` if the pivot is not present in the
    /// expected polarities, and `Err(CoefficientOverflow)` on any checked-
    /// arithmetic overflow. On either error the caller MUST fall back to the
    /// sound heuristic path (never panic, never ship a non-implied lemma).
    pub(crate) fn resolve_proven_round_to_one<F>(
        &self,
        reason: &Self,
        pivot: PbLit,
        falsified_fn: F,
    ) -> Result<Self, CpError>
    where
        F: FnMut(PbLit) -> bool,
    {
        // Allocating convenience wrapper. The hot path must use
        // [`Self::resolve_proven_round_to_one_into`] instead.
        let mut out = Self::new();
        let mut reduced = Self::new();
        self.resolve_proven_round_to_one_into(&mut out, &mut reduced, reason, pivot, falsified_fn)?;
        Ok(out)
    }

    /// [`Self::resolve_proven_round_to_one`] writing into caller-owned buffers.
    ///
    /// `out` receives the resolvent and `reduced` is working space for the
    /// round-to-one'd reason; both are fully overwritten, so their prior
    /// contents are irrelevant and their CAPACITY is reused. Passing the same
    /// buffers on every call is what keeps conflict analysis allocation-free.
    ///
    /// Aliasing is prevented by the borrow checker: `out` and `reduced` are
    /// `&mut` while `self` and `reason` are `&`, so no call site can pass the
    /// same accumulator twice.
    ///
    /// FAIL-CLOSED: on any `Err` the routine clears `out` rather than leaving a
    /// half-built resolvent in it. The caller's fallback path may write only
    /// part of the buffer, and a stale term surviving from a failed proven
    /// resolution would be a non-implied lemma — the exact bug class this path
    /// must never have, and one that nothing checks for in release builds.
    pub(crate) fn resolve_proven_round_to_one_into<F>(
        &self,
        out: &mut Self,
        reduced: &mut Self,
        reason: &Self,
        pivot: PbLit,
        falsified_fn: F,
    ) -> Result<(), CpError>
    where
        F: FnMut(PbLit) -> bool,
    {
        let result =
            self.resolve_proven_round_to_one_impl(out, reduced, reason, pivot, falsified_fn, None);
        if result.is_err() {
            out.clear();
        }
        result
    }

    /// [`Self::resolve_proven_round_to_one_captured`] writing into caller-owned
    /// buffers. See [`Self::resolve_proven_round_to_one_into`].
    pub(crate) fn resolve_proven_round_to_one_captured_into<F>(
        &self,
        out: &mut Self,
        reduced: &mut Self,
        reason: &Self,
        pivot: PbLit,
        falsified_fn: F,
        capture: &mut ProvenResolveCapture,
    ) -> Result<(), CpError>
    where
        F: FnMut(PbLit) -> bool,
    {
        capture.weakened.clear();
        let result = self.resolve_proven_round_to_one_impl(
            out,
            reduced,
            reason,
            pivot,
            falsified_fn,
            Some(capture),
        );
        if result.is_err() {
            out.clear();
        }
        result
    }

    /// [`Self::resolve_proven_round_to_one`] with proof-tap capture: identical
    /// arithmetic, additionally recording the post-orientation `c`/`w` pivot
    /// coefficients and the exact partial-weakening pairs into `capture` so the
    /// serializer can replay the step as pol RPN. `capture` is only meaningful
    /// when the call returns `Ok`.
    pub(crate) fn resolve_proven_round_to_one_captured<F>(
        &self,
        reason: &Self,
        pivot: PbLit,
        falsified_fn: F,
        capture: &mut ProvenResolveCapture,
    ) -> Result<Self, CpError>
    where
        F: FnMut(PbLit) -> bool,
    {
        capture.weakened.clear();
        let mut out = Self::new();
        let mut reduced = Self::new();
        self.resolve_proven_round_to_one_impl(
            &mut out,
            &mut reduced,
            reason,
            pivot,
            falsified_fn,
            Some(capture),
        )?;
        Ok(out)
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve_proven_round_to_one_impl<F>(
        &self,
        out: &mut Self,
        reduced: &mut Self,
        reason: &Self,
        pivot: PbLit,
        mut falsified_fn: F,
        mut capture: Option<&mut ProvenResolveCapture>,
    ) -> Result<(), CpError>
    where
        F: FnMut(PbLit) -> bool,
    {
        let negated_pivot = pivot_negate(pivot);

        // The conflict (`self`) must carry the falsified pivot `~pivot`; the
        // reason must carry the asserted pivot `pivot`. (We accept the swapped
        // labelling too — whichever side carries which polarity — so the method
        // is robust to caller orientation, exactly like the heuristic variant.)
        let (conflict, asserting_reason, pivot_lit) =
            if self.coefficient(negated_pivot) > 0 && reason.coefficient(pivot) > 0 {
                (self, reason, pivot)
            } else if self.coefficient(pivot) > 0 && reason.coefficient(negated_pivot) > 0 {
                // Caller passed the opposite orientation: the conflict holds
                // `pivot` and the reason holds `~pivot`. Resolve on `~pivot`.
                (self, reason, negated_pivot)
            } else {
                return Err(CpError::InvalidResolvePivot { pivot });
            };

        let neg_pivot_lit = pivot_negate(pivot_lit);
        let c = asserting_reason.coefficient(pivot_lit); // coeff of the asserted pivot in R
        let w = conflict.coefficient(neg_pivot_lit); // coeff of the falsified pivot in C
        debug_assert!(c > 0 && w > 0);
        if let Some(cap) = capture.as_deref_mut() {
            cap.c = c;
            cap.w = w;
        }

        // -- Step 1: roundToOne(R, pivot_lit) --------------------------------
        // Weaken every NON-falsified literal l != pivot_lit in R so its
        // coefficient becomes a multiple of c (subtract `coeff mod c` from the
        // coefficient and the degree). Weakening only ever removes strength, so
        // R stays implied; restricting it to non-falsified literals preserves
        // R's conflict/assertion power under the trail. Then ceiling-divide R by
        // c, making coeff_R(pivot_lit) == 1.
        reduced.copy_from(asserting_reason);
        let pivot_idx = lit_index(pivot_lit);

        // Snapshot entries first (we mutate during the loop).
        let entries: Vec<(usize, i128)> = reduced.iter_entries().collect();
        for (idx, coeff) in entries {
            if idx == pivot_idx {
                continue;
            }
            let lit = index_lit(idx);
            if falsified_fn(lit) {
                // Falsified literals are NOT weakened (they carry the conflict).
                continue;
            }
            let rem = coeff.rem_euclid(c);
            if rem != 0 {
                // Partial weakening: drop `rem` from this literal and the degree.
                let new_coeff = coeff.checked_sub(rem).ok_or(CpError::CoefficientOverflow)?;
                reduced.set_index(idx, new_coeff);
                reduced.degree = reduced
                    .degree
                    .checked_sub(rem)
                    .ok_or(CpError::CoefficientOverflow)?;
                if let Some(cap) = capture.as_deref_mut() {
                    cap.weakened.push((lit, rem));
                }
            }
        }
        // Drop any zeroed terms produced by full weakening (coeff -> 0).
        reduced.compact();
        // Ceiling-divide by c so the pivot coefficient becomes exactly 1.
        // `divide` ceilings every coefficient and the degree, then normalizes.
        reduced.divide(c)?;
        debug_assert_eq!(
            reduced.coefficient(pivot_lit),
            1,
            "roundToOne must leave coeff_R(pivot) == 1"
        );

        // -- Step 2: multiply reduced R by w, add into C, cancel pivot pair --
        // Multiplying the reduced reason by w gives the asserted pivot a
        // coefficient of w, matching the falsified pivot's coefficient w in C,
        // so the complementary pair cancels exactly via `p + ~p = 1` during
        // `normalize`. We accumulate into `out`, seeded from the conflict.
        out.copy_from(conflict);
        out.add_scaled(reduced, w)?;

        // `add_scaled` already compacted/simplified; `normalize` performs the
        // complementary cancellation of the pivot pair (and any other pairs
        // created by the addition), subtracting the shared amount w from the
        // degree per the `p + ~p = 1` identity.
        out.normalize()?;

        // -- Step 3: saturate -------------------------------------------------
        out.saturate();

        Ok(())
    }

    /// OVERFLOW FALLBACK: reduce this PB constraint to an IMPLIED cardinality
    /// constraint `sum l_i >= m` with unit coefficients (RoundingSat
    /// `reduceToCardinality`, Elffers & Nordstrom IJCAI-18 Alg. 6 lines 9-10).
    ///
    /// PRECONDITION: `self` must be normalized (all coefficients strictly
    /// positive — guaranteed by [`Self::normalize`]). If any coefficient is
    /// non-positive (i.e. the caller passed a non-normalized constraint) this
    /// returns `None`, failing closed.
    ///
    /// ALGORITHM. Let the (positive) coefficients, sorted DESCENDING, be
    /// `a_1 >= a_2 >= ... >= a_n`, and let `d = degree`. Define
    /// `prefix(k) = a_1 + ... + a_k` (the maximum achievable LHS when exactly
    /// `k` literals are true, since the `k` largest coefficients dominate). The
    /// reduction emits `sum l_i >= m` where
    /// `m = min { k in 0..=n : prefix(k) >= d }`,
    /// i.e. the smallest number of true literals that could possibly reach the
    /// degree. (`prefix(0) = 0`, so `m = 0` when `d <= 0`.) If even
    /// `prefix(n) < d` the original is infeasible; then `m = n + 1`, and the
    /// emitted `sum l_i >= n+1` over `n` literals is itself contradictory — a
    /// sound conflict mirroring the original's infeasibility.
    ///
    /// SOUNDNESS (the produced constraint is IMPLIED by `self`). Take any model
    /// of `self` and let `t` be its number of true literals among the `n`. The
    /// LHS of `self` under that model is at most the sum of the `t` LARGEST
    /// coefficients, i.e. `<= prefix(t)`. Since the model satisfies `self`,
    /// `prefix(t) >= LHS >= d`, so `t` belongs to the set `{ k : prefix(k) >= d }`
    /// and therefore `t >= m` (the minimum of that set). Hence every model of
    /// `self` has at least `m` true literals, i.e. satisfies `sum l_i >= m`. So
    /// `self => (sum l_i >= m)`: the reduction NEVER cuts off a feasible point.
    ///
    /// Coefficients are all 1 and the degree is `m <= n + 1`, so subsequent
    /// resolution arithmetic is bounded by the number of literals (no i128/i128
    /// overflow), which is the entire point of this fallback.
    ///
    /// The threshold computation uses exact i128 arithmetic so it cannot itself
    /// overflow regardless of how large the input coefficients are.
    ///
    /// Returns `None` (fail closed) when `self` is empty (degree already
    /// satisfied — nothing to learn) or has a non-positive coefficient.
    pub(crate) fn reduce_to_cardinality(&self) -> Option<Self> {
        // Collect the literals and their (strictly positive) coefficients.
        let mut entries: Vec<(usize, i128)> = Vec::new();
        for (idx, coeff) in self.iter_entries() {
            if coeff <= 0 {
                // Not normalized (or a stray non-positive coeff): fail closed.
                return None;
            }
            entries.push((idx, coeff));
        }
        let n = entries.len();
        if n == 0 {
            // No terms: a trivially-true (degree <= 0) constraint carries no
            // cardinality content. Fail closed; the caller keeps safe behavior.
            return None;
        }

        let d = self.degree;

        // Sort coefficients DESCENDING to form the prefix maxima.
        let mut coeffs_desc: Vec<i128> = entries.iter().map(|&(_, c)| c).collect();
        coeffs_desc.sort_unstable_by(|a, b| b.cmp(a));

        // m = min { k in 0..=n : prefix(k) >= d }, all in exact i128.
        // prefix(0) = 0 handles the d <= 0 case (m = 0). If no prefix reaches d
        // (prefix(n) < d), the original is infeasible and m = n + 1, yielding a
        // contradictory cardinality (a sound conflict).
        let mut m: i128 = (n as i128) + 1;
        let mut prefix: i128 = 0;
        if d <= 0 {
            m = 0;
        } else {
            for (k, &c) in coeffs_desc.iter().enumerate() {
                // prefix grows monotonically; i128 cannot overflow here for any
                // realistic instance (sum of i128 coeffs over n literals).
                prefix = prefix.checked_add(c)?;
                if prefix >= d {
                    m = (k as i128) + 1;
                    break;
                }
            }
        }

        // Build the cardinality constraint: every input literal with coeff 1,
        // degree m. m is at most n + 1, which fits i128 comfortably.
        let mut card = Self::with_num_vars(0);
        let cap = self.coeffs.len();
        card.coeffs.resize(cap, 0);
        card.stamp.resize(cap, 0);
        for &(idx, _) in &entries {
            card.set_index(idx, 1);
        }
        // m is in 0..=n+1, n is a Vec length, so the i128 conversion is exact.
        card.degree = m;
        // Normalize to drop the terms if the degree collapsed to <= 0 (m == 0),
        // matching the rest of the API's invariants. On any (impossible here)
        // arithmetic error, fail closed.
        card.normalize().ok()?;
        Some(card)
    }

    // -- Queries -------------------------------------------------------------

    /// Mirrors `CpConstraint::slack`: `degree - sum(true coefficients)`,
    /// saturated to i128.
    pub(crate) fn slack<F>(&self, mut is_true: F) -> i128
    where
        F: FnMut(PbLit) -> bool,
    {
        let true_sum: i128 = self
            .iter_entries()
            .filter(|&(idx, _)| is_true(index_lit(idx)))
            .map(|(_, c)| c)
            .sum();
        saturate_i128(self.degree - true_sum)
    }

    /// RoundingSat slack under a partial trail: `(sum of coeffs of NON-falsified
    /// literals) − degree`, in i128 (no saturation). The constraint is falsified
    /// (conflicting) iff this is strictly negative. `falsified_fn` returns `true`
    /// iff a literal is falsified by the current trail. This is the proven
    /// round-to-one loop invariant's slack (distinct from [`Self::slack`], which
    /// uses the codebase's `degree − sum(true)` convention).
    pub(crate) fn rs_slack<F>(&self, mut falsified_fn: F) -> i128
    where
        F: FnMut(PbLit) -> bool,
    {
        let non_falsified_sum: i128 = self
            .iter_entries()
            .filter(|&(idx, _)| !falsified_fn(index_lit(idx)))
            .map(|(_, c)| c)
            .sum();
        non_falsified_sum - self.degree
    }

    /// Mirrors `CpConstraint::is_asserting`: exactly one literal participates
    /// at the highest level reported by `trail_fn`.
    pub(crate) fn is_asserting<F>(&self, mut trail_fn: F) -> bool
    where
        F: FnMut(PbLit) -> Option<u32>,
    {
        let mut highest_level: Option<u32> = None;
        let mut highest_count = 0usize;
        for (idx, _) in self.iter_entries() {
            let Some(level) = trail_fn(index_lit(idx)) else {
                continue;
            };
            match highest_level {
                None => {
                    highest_level = Some(level);
                    highest_count = 1;
                }
                Some(current) if level > current => {
                    highest_level = Some(level);
                    highest_count = 1;
                }
                Some(current) if level == current => {
                    highest_count += 1;
                }
                Some(_) => {}
            }
        }
        highest_level.is_some() && highest_count == 1
    }

    // -- Exporters -----------------------------------------------------------

    /// Returns the canonical sorted term list `(var, negated, coeff)`.
    fn sorted_terms(&self) -> Vec<(u32, bool, i128)> {
        let mut terms: Vec<(u32, bool, i128)> = self
            .iter_entries()
            .map(|(idx, c)| {
                let lit = index_lit(idx);
                (lit.var, lit.negated, c)
            })
            .collect();
        terms.sort_by_key(|&(var, negated, _)| (var, negated));
        terms
    }

    /// Exports to a normalized [`CpConstraint`].
    pub(crate) fn to_cp_constraint(&self) -> CpConstraint {
        let coeffs: std::collections::BTreeMap<PbLit, i128> = self
            .iter_entries()
            .map(|(idx, c)| (index_lit(idx), c))
            .collect();
        CpConstraint::new(coeffs, self.degree)
    }

    /// Exports to a `>=` [`PbConstraint`] (terms sorted by `(var, negated)`).
    pub(crate) fn to_pb_constraint(&self) -> PbConstraint {
        let mut terms: Vec<PbTerm> = self
            .iter_entries()
            .map(|(idx, c)| PbTerm {
                coeff: c,
                lits: vec![index_lit(idx)],
            })
            .collect();
        terms.sort_by_key(|term| (term.lits[0].var, term.lits[0].negated));
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: self.degree,
        }
    }
}

/// Result of a dense round-to-one resolution step.
#[derive(Debug, Clone)]
pub(crate) struct DenseRoundToOneResult {
    /// The resolved dense constraint.
    pub(crate) constraint: DenseCp,
    /// Whether the division rule was used (see [`RoundToOneResult`]).
    pub(crate) used_division: bool,
}

impl DenseRoundToOneResult {
    fn new(constraint: DenseCp, used_division: bool) -> Self {
        Self {
            constraint,
            used_division,
        }
    }

    /// Converts to the trusted [`RoundToOneResult`] type.
    pub(crate) fn to_round_to_one_result(&self) -> RoundToOneResult {
        RoundToOneResult {
            constraint: self.constraint.to_cp_constraint(),
            used_division: self.used_division,
        }
    }
}

/// Negates a literal (local helper mirroring `cutting_planes::negate_lit`).
#[inline]
fn pivot_negate(lit: PbLit) -> PbLit {
    PbLit {
        var: lit.var,
        negated: !lit.negated,
    }
}

/// Inert i64-era passthrough (values are already `i128`); explicit no-op.
#[inline]
fn saturate_i128(value: i128) -> i128 {
    value
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    // -- Helpers -------------------------------------------------------------

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn not(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn cp(entries: &[(PbLit, i128)], degree: i128) -> CpConstraint {
        let coeffs: BTreeMap<PbLit, i128> = entries.iter().copied().collect();
        CpConstraint::new(coeffs, degree)
    }

    /// Canonical form for differential comparison.
    fn canon_cp(c: &CpConstraint) -> (Vec<(u32, bool, i128)>, i128) {
        let mut terms: Vec<(u32, bool, i128)> = c
            .coefficients()
            .iter()
            .map(|(lit, &coeff)| (lit.var, lit.negated, coeff))
            .collect();
        terms.sort_by_key(|&(var, negated, _)| (var, negated));
        (terms, c.degree())
    }

    fn canon_dense(d: &DenseCp) -> (Vec<(u32, bool, i128)>, i128) {
        (d.sorted_terms(), d.degree())
    }

    fn dense_from_cp(c: &CpConstraint) -> DenseCp {
        let mut d = DenseCp::with_num_vars(8);
        d.load_from_cp(c);
        d
    }

    fn assert_same(c: &CpConstraint, d: &DenseCp, ctx: &str) {
        assert_eq!(
            canon_cp(c),
            canon_dense(d),
            "mismatch in {ctx}\n  cp   = {:?}\n  dense= {:?}",
            canon_cp(c),
            canon_dense(d)
        );
    }

    // -- Deterministic xorshift PRNG (no rand crate / no entropy) -------------

    struct XorShift(u64);

    impl XorShift {
        fn new(seed: u64) -> Self {
            // Avoid zero state.
            XorShift(seed | 1)
        }
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        /// Returns an i128 in [lo, hi].
        fn range(&mut self, lo: i128, hi: i128) -> i128 {
            debug_assert!(hi >= lo);
            let span = (hi - lo + 1) as u64;
            lo + (self.next_u64() % span) as i128
        }
        fn bool(&mut self) -> bool {
            self.next_u64() & 1 == 1
        }
    }

    /// Generates a random CpConstraint over vars 1..=`max_var` with mixed-sign
    /// coefficients and a small degree.
    fn random_cp(rng: &mut XorShift, max_var: u32) -> CpConstraint {
        let n_terms = rng.range(0, max_var as i128) as usize;
        let mut entries: BTreeMap<PbLit, i128> = BTreeMap::new();
        for _ in 0..n_terms {
            let var = rng.range(1, max_var as i128) as u32;
            let negated = rng.bool();
            // Mixed positive/negative coeffs, small magnitude including some larger.
            let coeff = rng.range(-6, 6);
            if coeff == 0 {
                continue;
            }
            let l = PbLit { var, negated };
            // Last write wins (BTreeMap), mirrors a random raw input; the
            // constructor normalizes.
            entries.insert(l, coeff);
        }
        let degree = rng.range(-3, 8);
        CpConstraint::new(entries, degree)
    }

    /// Like `random_cp` but allows BOTH polarities of the same var to coexist
    /// before normalization, to stress complementary cancellation.
    fn random_cp_with_complements(rng: &mut XorShift, max_var: u32) -> CpConstraint {
        let n_terms = rng.range(0, (max_var * 2) as i128) as usize;
        let mut entries: BTreeMap<PbLit, i128> = BTreeMap::new();
        for _ in 0..n_terms {
            let var = rng.range(1, max_var as i128) as u32;
            let negated = rng.bool();
            let coeff = rng.range(-5, 5);
            if coeff == 0 {
                continue;
            }
            entries.insert(PbLit { var, negated }, coeff);
        }
        let degree = rng.range(0, 10);
        CpConstraint::new(entries, degree)
    }

    // -- Deterministic hand-written cases ------------------------------------

    #[test]
    fn dense_load_roundtrip_matches() {
        let c = cp(&[(lit(1), 2), (not(2), 3)], 4);
        let d = dense_from_cp(&c);
        assert_same(&c, &d, "load roundtrip");
        // Export to CpConstraint and PbConstraint.
        let exported = d.to_cp_constraint();
        assert_eq!(canon_cp(&c), canon_cp(&exported));
        let pb = d.to_pb_constraint();
        let cp_pb = PbConstraint::from(&c);
        assert_eq!(pb, cp_pb);
    }

    #[test]
    fn dense_load_from_pb_matches_tryfrom() {
        let pb = PbConstraint {
            terms: vec![
                PbTerm {
                    coeff: -3,
                    lits: vec![lit(1)],
                },
                PbTerm {
                    coeff: 2,
                    lits: vec![not(2)],
                },
            ],
            rel: PbRel::Ge,
            rhs: 4,
        };
        let c = CpConstraint::try_from(&pb).unwrap();
        let mut d = DenseCp::new();
        d.load_from_pb(&pb).unwrap();
        assert_same(&c, &d, "load_from_pb vs try_from");
    }

    #[test]
    fn dense_divide_ceiling() {
        let c = cp(&[(lit(1), 5), (lit(2), 6)], 7);
        let mut cm = c.clone();
        cm.divide(4).unwrap();
        let mut d = dense_from_cp(&c);
        d.divide(4).unwrap();
        assert_same(&cm, &d, "divide");
    }

    #[test]
    fn dense_saturate() {
        let c = cp(&[(lit(1), 5), (lit(2), 2)], 3);
        let mut cm = c.clone();
        cm.saturate();
        let mut d = dense_from_cp(&c);
        d.saturate();
        assert_same(&cm, &d, "saturate");
    }

    #[test]
    fn dense_gcd_divide() {
        let c = cp(&[(lit(1), 6), (not(2), 12)], 9);
        let mut cm = c.clone();
        cm.gcd_divide().unwrap();
        let mut d = dense_from_cp(&c);
        d.gcd_divide().unwrap();
        assert_same(&cm, &d, "gcd_divide");
    }

    #[test]
    fn dense_normalize_flips_negative_via_raw() {
        // Build via load_from_pb to feed raw negative coeffs through normalize.
        let pb = PbConstraint {
            terms: vec![
                PbTerm {
                    coeff: -3,
                    lits: vec![lit(1)],
                },
                PbTerm {
                    coeff: 2,
                    lits: vec![not(2)],
                },
            ],
            rel: PbRel::Ge,
            rhs: 4,
        };
        let c = CpConstraint::try_from(&pb).unwrap();
        let mut d = DenseCp::new();
        d.load_from_pb(&pb).unwrap();
        assert_same(&c, &d, "normalize flips negatives");
        assert_eq!(d.coefficient(not(1)), 3);
        assert_eq!(d.degree(), 7);
    }

    #[test]
    fn dense_complementary_cancellation() {
        // x1 and ~x1 both positive in raw input -> cancellation.
        let pb = PbConstraint {
            terms: vec![
                PbTerm {
                    coeff: 5,
                    lits: vec![lit(1)],
                },
                PbTerm {
                    coeff: 3,
                    lits: vec![not(1)],
                },
                PbTerm {
                    coeff: 2,
                    lits: vec![lit(2)],
                },
            ],
            rel: PbRel::Ge,
            rhs: 6,
        };
        let c = CpConstraint::try_from(&pb).unwrap();
        let mut d = DenseCp::new();
        d.load_from_pb(&pb).unwrap();
        assert_same(&c, &d, "complementary cancellation");
        // shared = 3, degree 6 - 3 = 3, x1 -> 2, ~x1 -> 0.
        assert_eq!(d.coefficient(lit(1)), 2);
        assert_eq!(d.coefficient(not(1)), 0);
        assert_eq!(d.degree(), 3);
    }

    #[test]
    fn dense_weaken() {
        let c = cp(&[(lit(1), 4), (lit(2), 2)], 5);
        let mut cm = c.clone();
        cm.weaken(lit(1));
        let mut d = dense_from_cp(&c);
        d.weaken(lit(1));
        assert_same(&cm, &d, "weaken");
    }

    #[test]
    fn dense_add_assign() {
        let lhs = cp(&[(lit(1), 2), (not(2), 1)], 2);
        let rhs = cp(&[(lit(1), 3), (lit(3), 4)], 5);
        let sum = lhs.addition(&rhs);
        let mut d = dense_from_cp(&lhs);
        let dr = dense_from_cp(&rhs);
        d.add_assign(&dr).unwrap();
        assert_same(&sum, &d, "add_assign");
    }

    #[test]
    fn dense_multiply() {
        let c = cp(&[(lit(1), 2), (lit(2), 1)], 3);
        let mut cm = c.clone();
        cm.multiply(4).unwrap();
        let mut d = dense_from_cp(&c);
        d.multiply(4).unwrap();
        assert_same(&cm, &d, "multiply");
    }

    #[test]
    fn dense_clear_reuse() {
        let mut d = DenseCp::with_num_vars(4);
        let c1 = cp(&[(lit(1), 2), (lit(2), 3)], 4);
        d.load_from_cp(&c1);
        assert_same(&c1, &d, "first load");
        // Reuse: load a different constraint without reallocating.
        let c2 = cp(&[(not(3), 5)], 5);
        d.load_from_cp(&c2);
        assert_same(&c2, &d, "second load after reuse");
        assert_eq!(d.coefficient(lit(1)), 0, "stale entry must be gone");
        assert_eq!(d.coefficient(lit(2)), 0, "stale entry must be gone");
    }

    // -- Round-to-one hand-written cases (mirror cutting_planes.rs) ----------

    fn r2o_cp(
        conflict: &CpConstraint,
        reason: &CpConstraint,
        pivot: PbLit,
        asserting: Option<PbLit>,
    ) -> RoundToOneResult {
        conflict
            .resolve_round_to_one(reason, pivot, asserting)
            .unwrap()
    }

    fn r2o_dense(
        conflict: &CpConstraint,
        reason: &CpConstraint,
        pivot: PbLit,
        asserting: Option<PbLit>,
    ) -> DenseRoundToOneResult {
        let dc = dense_from_cp(conflict);
        let dr = dense_from_cp(reason);
        dc.resolve_round_to_one(&dr, pivot, asserting).unwrap()
    }

    fn assert_r2o_same(
        conflict: &CpConstraint,
        reason: &CpConstraint,
        pivot: PbLit,
        asserting: Option<PbLit>,
        ctx: &str,
    ) {
        let cp_res = r2o_cp(conflict, reason, pivot, asserting);
        let d_res = r2o_dense(conflict, reason, pivot, asserting);
        assert_eq!(
            cp_res.used_division, d_res.used_division,
            "used_division mismatch in {ctx}"
        );
        assert_same(&cp_res.constraint, &d_res.constraint, ctx);
    }

    #[test]
    fn dense_r2o_basic_division() {
        let conflict = cp(&[(lit(1), 3), (lit(2), 2), (lit(3), 4)], 5);
        let reason = cp(&[(not(1), 2), (lit(4), 1)], 1);
        assert_r2o_same(
            &conflict,
            &reason,
            lit(1),
            Some(lit(2)),
            "r2o basic division",
        );
    }

    #[test]
    fn dense_r2o_no_division_needed() {
        let conflict = cp(&[(lit(1), 1), (lit(2), 1)], 1);
        let reason = cp(&[(not(1), 1), (lit(3), 1)], 1);
        assert_r2o_same(&conflict, &reason, lit(1), Some(lit(2)), "r2o no division");
    }

    #[test]
    fn dense_r2o_without_asserting_lit() {
        let conflict = cp(&[(lit(1), 3), (lit(2), 2)], 4);
        let reason = cp(&[(not(1), 2), (lit(3), 1)], 2);
        assert_r2o_same(&conflict, &reason, lit(1), None, "r2o no asserting");
    }

    #[test]
    fn dense_r2o_cancellation() {
        let conflict = cp(&[(lit(1), 2), (lit(2), 3), (lit(3), 2)], 4);
        let reason = cp(&[(not(1), 1), (not(2), 2), (lit(4), 1)], 2);
        assert_r2o_same(&conflict, &reason, lit(1), Some(lit(3)), "r2o cancellation");
    }

    #[test]
    fn dense_r2o_invalid_pivot() {
        let conflict = cp(&[(lit(2), 1)], 1);
        let reason = cp(&[(lit(3), 1)], 1);
        let dc = dense_from_cp(&conflict);
        let dr = dense_from_cp(&reason);
        let err = dc.resolve_round_to_one(&dr, lit(1), None).unwrap_err();
        assert!(matches!(err, CpError::InvalidResolvePivot { .. }));
    }

    #[test]
    fn dense_r2o_large_coefficients() {
        let conflict = cp(&[(lit(1), 1_000_000), (lit(2), 500_000)], 800_000);
        let reason = cp(&[(not(1), 2_000_000), (lit(3), 300_000)], 1_500_000);
        assert_r2o_same(&conflict, &reason, lit(1), Some(lit(2)), "r2o large coeffs");
    }

    #[test]
    fn dense_r2o_pigeonhole_like() {
        let at_most_one = cp(&[(not(1), 1), (not(2), 1), (not(3), 1)], 2);
        let pigeon_assigned = cp(&[(lit(1), 1)], 1);
        assert_r2o_same(
            &at_most_one,
            &pigeon_assigned,
            lit(1),
            Some(not(2)),
            "r2o pigeonhole",
        );
    }

    #[test]
    fn dense_r2o_weighted_pigeonhole() {
        let conflict = cp(&[(lit(1), 3), (lit(2), 3), (lit(3), 3)], 7);
        let reason = cp(&[(not(1), 2), (lit(4), 1)], 2);
        assert_r2o_same(
            &conflict,
            &reason,
            lit(1),
            Some(lit(2)),
            "r2o weighted pigeon",
        );
    }

    // NOTE on the overflow fallback path: the trusted
    // `CpConstraint::resolve_round_to_one` falls back to `CpConstraint::resolve`
    // on a checked-multiply overflow. But `resolve` itself uses the *panicking*
    // `multiply`/degree arithmetic with the SAME scale factors, so any input
    // that overflows round-to-one's checked scaling also makes the trusted
    // fallback panic. The fallback is therefore never reachable in trusted code
    // without panicking, so there is no non-panicking differential case to
    // assert here. `DenseCp` uses checked arithmetic throughout and returns
    // `Err(CoefficientOverflow)` instead of panicking on this (unreachable in
    // practice) path — strictly safer, and the fuzzers stay within the
    // non-overflowing range so the common round-to-one path is matched exactly.

    #[test]
    fn dense_multiply_checked_overflow() {
        let c = cp(&[(lit(1), i128::MAX / 2 + 1)], i128::MAX / 2 + 1);
        let mut d = dense_from_cp(&c);
        let res = d.multiply_checked(3);
        assert!(matches!(res, Err(CpError::CoefficientOverflow)));
    }

    #[test]
    fn dense_multiply_checked_non_positive() {
        let c = cp(&[(lit(1), 2)], 2);
        let mut d = dense_from_cp(&c);
        let res = d.multiply_checked(0);
        assert!(matches!(res, Err(CpError::NonPositiveMultiplier(0))));
    }

    #[test]
    fn dense_slack_and_asserting() {
        let c = cp(&[(lit(1), 1), (lit(2), 1)], 2);
        let d = dense_from_cp(&c);
        // assignment: var1 true, var2 false.
        let assignment: BTreeMap<u32, bool> = BTreeMap::from([(1, true), (2, false)]);
        let cp_slack = c.slack(&assignment);
        let d_slack = d.slack(|lit| {
            let v = assignment.get(&lit.var).copied().unwrap_or(false);
            if lit.negated {
                !v
            } else {
                v
            }
        });
        assert_eq!(cp_slack, d_slack, "slack mismatch");

        let trail = |lit: PbLit| match lit.var {
            1 => Some(1),
            2 => Some(3),
            _ => None,
        };
        assert_eq!(c.is_asserting(trail), d.is_asserting(trail));
    }

    // -- Differential fuzz tests ---------------------------------------------

    const MAX_VAR: u32 = 6;

    #[test]
    fn diff_divide_saturate_gcd_normalize() {
        let mut runs = 0u32;
        for seed in 0..3000u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(2654435761).wrapping_add(1));
            let c = random_cp_with_complements(&mut rng, MAX_VAR);

            // divide by a random positive divisor.
            let divisor = rng.range(1, 7);
            let mut cm = c.clone();
            cm.divide(divisor).unwrap();
            let mut d = dense_from_cp(&c);
            d.divide(divisor).unwrap();
            assert_same(&cm, &d, "fuzz divide");

            // saturate.
            let mut cm = c.clone();
            cm.saturate();
            let mut d = dense_from_cp(&c);
            d.saturate();
            assert_same(&cm, &d, "fuzz saturate");

            // gcd_divide.
            let mut cm = c.clone();
            cm.gcd_divide().unwrap();
            let mut d = dense_from_cp(&c);
            d.gcd_divide().unwrap();
            assert_same(&cm, &d, "fuzz gcd_divide");

            // saturate_and_gcd.
            let mut cm = c.clone();
            cm.saturate_and_gcd().unwrap();
            let mut d = dense_from_cp(&c);
            d.saturate_and_gcd().unwrap();
            assert_same(&cm, &d, "fuzz saturate_and_gcd");

            runs += 1;
        }
        assert!(runs >= 3000, "expected at least 3000 fuzz runs");
    }

    #[test]
    fn diff_weaken_and_weaken_conservative() {
        for seed in 0..3000u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(40503).wrapping_add(7));
            let c = random_cp(&mut rng, MAX_VAR);

            // weaken a random literal (may or may not be present).
            let wvar = rng.range(1, MAX_VAR as i128) as u32;
            let wlit = PbLit {
                var: wvar,
                negated: rng.bool(),
            };
            let mut cm = c.clone();
            cm.weaken(wlit);
            let mut d = dense_from_cp(&c);
            d.weaken(wlit);
            assert_same(&cm, &d, "fuzz weaken");

            // weaken_conservative with a random asserting lit and random
            // falsified-level map.
            let asserting = if rng.bool() {
                Some(PbLit {
                    var: rng.range(1, MAX_VAR as i128) as u32,
                    negated: rng.bool(),
                })
            } else {
                None
            };
            // Build a deterministic falsified map keyed by (var, negated).
            // We must use the SAME function for both implementations, so
            // capture a snapshot vector.
            let mut levels: Vec<((u32, bool), Option<u32>)> = Vec::new();
            for v in 1..=MAX_VAR {
                for neg in [false, true] {
                    let r = rng.range(0, 3);
                    let level = if r == 0 { None } else { Some(r as u32) };
                    levels.push(((v, neg), level));
                }
            }
            let falsified = |lit: PbLit| -> Option<u32> {
                levels
                    .iter()
                    .find(|&&((v, n), _)| v == lit.var && n == lit.negated)
                    .and_then(|&(_, lvl)| lvl)
            };

            let mut cm = c.clone();
            cm.weaken_conservative(asserting, falsified);
            let mut d = dense_from_cp(&c);
            d.weaken_conservative(asserting, falsified);
            assert_same(&cm, &d, "fuzz weaken_conservative");
        }
    }

    #[test]
    fn diff_add_and_multiply() {
        for seed in 0..3000u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(1000003).wrapping_add(11));
            let a = random_cp(&mut rng, MAX_VAR);
            let b = random_cp(&mut rng, MAX_VAR);

            // addition.
            let sum = a.addition(&b);
            let mut d = dense_from_cp(&a);
            let db = dense_from_cp(&b);
            d.add_assign(&db).unwrap();
            assert_same(&sum, &d, "fuzz addition");

            // multiply by random positive factor (keep small to avoid overflow).
            let factor = rng.range(1, 5);
            let mut cm = a.clone();
            cm.multiply(factor).unwrap();
            let mut dm = dense_from_cp(&a);
            dm.multiply(factor).unwrap();
            assert_same(&cm, &dm, "fuzz multiply");

            // add_scaled: a + factor*b should equal addition(a, factor*b)
            // when both are normalized. Compare dense add_scaled against the
            // CpConstraint pathway.
            let mut b_scaled = b.clone();
            b_scaled.multiply(factor).unwrap();
            let cp_combo = a.addition(&b_scaled);
            let mut d2 = dense_from_cp(&a);
            let db2 = dense_from_cp(&b);
            d2.add_scaled(&db2, factor).unwrap();
            assert_same(&cp_combo, &d2, "fuzz add_scaled");
        }
    }

    #[test]
    fn diff_resolve_round_to_one() {
        let mut total = 0u32;
        for seed in 0..6000u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(2246822519).wrapping_add(13));

            // Construct two constraints that share a pivot in opposite polarity.
            // Choose a pivot var and force the polarities.
            let pivot_var = rng.range(1, MAX_VAR as i128) as u32;
            let pivot = PbLit {
                var: pivot_var,
                negated: rng.bool(),
            };
            let neg_pivot = PbLit {
                var: pivot_var,
                negated: !pivot.negated,
            };

            // Build conflict with positive pivot, reason with positive neg_pivot.
            let conflict = build_with_forced(&mut rng, MAX_VAR, pivot, 1, 6);
            let reason = build_with_forced(&mut rng, MAX_VAR, neg_pivot, 1, 6);

            // Skip degenerate cases where after normalization the forced pivot
            // literal vanished (e.g. cancelled), making the pivot invalid.
            if conflict.coefficient(pivot) <= 0 || reason.coefficient(neg_pivot) <= 0 {
                continue;
            }

            // Random asserting literal (sometimes None).
            let asserting = if rng.range(0, 4) == 0 {
                None
            } else {
                Some(PbLit {
                    var: rng.range(1, MAX_VAR as i128) as u32,
                    negated: rng.bool(),
                })
            };

            let cp_res = conflict
                .resolve_round_to_one(&reason, pivot, asserting)
                .unwrap();
            let dc = dense_from_cp(&conflict);
            let dr = dense_from_cp(&reason);
            let d_res = dc.resolve_round_to_one(&dr, pivot, asserting).unwrap();

            assert_eq!(
                cp_res.used_division, d_res.used_division,
                "used_division mismatch (seed {seed}): cp={} dense={}",
                cp_res.used_division, d_res.used_division
            );
            assert_eq!(
                canon_cp(&cp_res.constraint),
                canon_dense(&d_res.constraint),
                "resolved constraint mismatch (seed {seed})\n  conflict={:?}\n  reason={:?}\n  pivot={:?} asserting={:?}",
                canon_cp(&conflict),
                canon_cp(&reason),
                pivot,
                asserting,
            );
            total += 1;
        }
        assert!(
            total >= 4000,
            "expected many non-degenerate r2o cases, got {total}"
        );
    }

    /// Builds a random CpConstraint that is guaranteed to contain `forced`
    /// with a positive coefficient before normalization.
    fn build_with_forced(
        rng: &mut XorShift,
        max_var: u32,
        forced: PbLit,
        min_forced_coeff: i128,
        max_forced_coeff: i128,
    ) -> CpConstraint {
        let mut entries: BTreeMap<PbLit, i128> = BTreeMap::new();
        let n_terms = rng.range(0, max_var as i128) as usize;
        for _ in 0..n_terms {
            let var = rng.range(1, max_var as i128) as u32;
            let negated = rng.bool();
            let coeff = rng.range(-4, 4);
            if coeff == 0 {
                continue;
            }
            entries.insert(PbLit { var, negated }, coeff);
        }
        // Force the pivot literal with a positive coefficient.
        let fc = rng.range(min_forced_coeff, max_forced_coeff);
        entries.insert(forced, fc);
        let degree = rng.range(1, 8);
        CpConstraint::new(entries, degree)
    }

    // -- PROVEN round-to-one: semantic-entailment property test --------------
    //
    // This is the GOLD-STANDARD soundness oracle for the proven round-to-one.
    // For thousands of random (C, R, pivot, partial-trail) cases where C is
    // falsified and R propagates the pivot, it:
    //   1. Computes the proven resolvent C'.
    //   2. Brute-forces ALL 2^n assignments and asserts EVERY assignment that
    //      satisfies BOTH C and R also satisfies C' (semantic entailment:
    //      C ∧ R ⊨ C', the soundness guarantee of cutting-planes resolution).
    //   3. Asserts C' is falsified (RoundingSat-slack < 0) under the trail's
    //      falsifying assignment (the loop invariant).
    // If ANY case fails, the round-to-one is UNSOUND — the test prints the exact
    // (C, R, pivot, C') counterexample. NEVER weaken this test.

    /// A trail value for the property test: a var is True/False/Unassigned.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum TrailVal {
        True,
        False,
        Unassigned,
    }

    /// Returns whether `lit` is falsified under the partial trail `trail`
    /// (indexed by var-1). A literal is falsified iff its var is assigned and
    /// the literal evaluates to false.
    fn lit_falsified(lit: PbLit, trail: &[TrailVal]) -> bool {
        match trail[(lit.var - 1) as usize] {
            TrailVal::Unassigned => false,
            TrailVal::True => lit.negated, // x is true => ~x is false
            TrailVal::False => !lit.negated, // x is false => x is false
        }
    }

    /// RoundingSat slack under a partial trail: (sum of coeffs of NON-falsified
    /// literals) − degree. The constraint is falsified iff this is < 0.
    fn rs_slack(c: &CpConstraint, trail: &[TrailVal]) -> i128 {
        let non_falsified: i128 = c
            .coefficients()
            .iter()
            .filter(|(&lit, _)| !lit_falsified(lit, trail))
            .map(|(_, &coeff)| i128::from(coeff))
            .sum();
        non_falsified - i128::from(c.degree())
    }

    /// Whether a complete assignment (indexed by var-1) satisfies `c`:
    /// sum of coeffs of true literals >= degree.
    fn satisfies(c: &CpConstraint, assign: &[bool]) -> bool {
        let sum_true: i128 = c
            .coefficients()
            .iter()
            .filter(|(&lit, _)| {
                let v = assign[(lit.var - 1) as usize];
                if lit.negated {
                    !v
                } else {
                    v
                }
            })
            .map(|(_, &coeff)| i128::from(coeff))
            .sum();
        sum_true >= i128::from(c.degree())
    }

    /// Whether a complete assignment is consistent with the partial trail.
    fn consistent_with_trail(assign: &[bool], trail: &[TrailVal]) -> bool {
        assign.iter().zip(trail.iter()).all(|(&a, &t)| match t {
            TrailVal::Unassigned => true,
            TrailVal::True => a,
            TrailVal::False => !a,
        })
    }

    /// Builds a random `>=` CpConstraint over vars `1..=n` with mixed-sign raw
    /// coefficients, forcing `forced` to be present with a positive coefficient.
    fn random_forced_cp(rng: &mut XorShift, n: u32, forced: PbLit) -> CpConstraint {
        let mut entries: BTreeMap<PbLit, i128> = BTreeMap::new();
        let n_terms = rng.range(0, n as i128) as usize;
        for _ in 0..n_terms {
            let var = rng.range(1, n as i128) as u32;
            let negated = rng.bool();
            let coeff = rng.range(-5, 5);
            if coeff == 0 {
                continue;
            }
            entries.insert(PbLit { var, negated }, coeff);
        }
        let fc = rng.range(1, 6);
        entries.insert(forced, fc);
        let degree = rng.range(1, 9);
        CpConstraint::new(entries, degree)
    }

    fn dense_from(c: &CpConstraint) -> DenseCp {
        let mut d = DenseCp::with_num_vars(16);
        d.load_from_cp(c);
        d
    }

    #[test]
    fn proven_round_to_one_semantic_entailment() {
        const N: u32 = 8; // <= 10 vars; 2^8 = 256 assignments brute-forced each.
        let mut checked = 0u64; // (C,R) cases that ran the proven resolution
        let mut brute_assignments = 0u64; // total 2^n assignments enumerated

        // ONE pair of buffers threaded through ALL seeds, deliberately never
        // cleared between cases. The production path reuses the solver's
        // long-lived accumulators across every conflict, so a fresh buffer per
        // seed would test a configuration that never occurs and would miss the
        // one bug class the into-buffer refactor can introduce: a stale
        // coefficient or stamp surviving from the previous resolution into the
        // next resolvent. Every case below therefore runs against a DIRTY
        // buffer holding the previous case's output.
        let mut out = DenseCp::new();
        let mut reduced = DenseCp::new();

        for seed in 0..40_000u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1));

            // Choose pivot var and polarity. `pivot` (p) is the asserted trail
            // literal carried by the reason R; `~pivot` is the falsified pivot
            // carried by the conflict C.
            let pivot_var = rng.range(1, N as i128) as u32;
            let pivot = PbLit {
                var: pivot_var,
                negated: rng.bool(),
            };
            let neg_pivot = PbLit {
                var: pivot_var,
                negated: !pivot.negated,
            };

            // Conflict C contains ~pivot; reason R contains pivot.
            let conflict = random_forced_cp(&mut rng, N, neg_pivot);
            let reason = random_forced_cp(&mut rng, N, pivot);

            // Skip degenerate cases where normalization removed the forced pivot.
            if conflict.coefficient(neg_pivot) <= 0 || reason.coefficient(pivot) <= 0 {
                continue;
            }

            // Random partial trail, but force the pivot: p true, ~p false.
            let mut trail = vec![TrailVal::Unassigned; N as usize];
            for slot in trail.iter_mut() {
                *slot = match rng.range(0, 2) {
                    0 => TrailVal::Unassigned,
                    1 => TrailVal::True,
                    _ => TrailVal::False,
                };
            }
            // Pivot var assignment must make `pivot` TRUE.
            trail[(pivot_var - 1) as usize] = if pivot.negated {
                TrailVal::False
            } else {
                TrailVal::True
            };

            // Filter 1: C must be falsified under the trail (RS-slack < 0).
            if rs_slack(&conflict, &trail) >= 0 {
                continue;
            }
            // Filter 2: R must "propagate" the pivot: R is non-falsified with the
            // pivot true (slack_R >= 0), and flipping the pivot to false would
            // falsify R (i.e. the pivot is genuinely forced/asserted by R).
            if rs_slack(&reason, &trail) < 0 {
                continue;
            }
            let mut trail_flip = trail.clone();
            trail_flip[(pivot_var - 1) as usize] = if pivot.negated {
                TrailVal::True
            } else {
                TrailVal::False
            };
            if rs_slack(&reason, &trail_flip) >= 0 {
                // Pivot is not actually forced by R under this trail; skip.
                continue;
            }

            // Compute the PROVEN resolvent.
            let dc = dense_from(&conflict);
            let dr = dense_from(&reason);
            let falsified_fn = |lit: PbLit| lit_falsified(lit, &trail);
            match dc.resolve_proven_round_to_one_into(
                &mut out,
                &mut reduced,
                &dr,
                pivot,
                falsified_fn,
            ) {
                Ok(()) => {}
                // Err here is invalid-pivot or overflow; both are sound
                // fall-back-to-heuristic signals, not soundness failures.
                Err(_) => continue,
            }
            let cprime = out.to_cp_constraint();

            // --- Soundness check (the gold standard): C ∧ R ⊨ C'. ---
            let n = N as usize;
            for bits in 0u32..(1u32 << n) {
                let assign: Vec<bool> = (0..n).map(|i| (bits >> i) & 1 == 1).collect();
                if satisfies(&conflict, &assign) && satisfies(&reason, &assign) {
                    assert!(
                        satisfies(&cprime, &assign),
                        "UNSOUND proven round-to-one (seed {seed}): assignment {assign:?} \
                         satisfies C and R but NOT C'.\n  C  = {conflict:?}\n  R  = {reason:?}\n  \
                         pivot = {pivot:?}\n  C' = {cprime:?}"
                    );
                }
            }
            brute_assignments += 1u64 << n;

            // --- Loop invariant: C' is falsified under the trail (RS-slack < 0).
            // Verify against an explicit falsifying complete assignment that is
            // consistent with the trail (extend unassigned vars to MAXIMISE C''s
            // satisfaction; if even that maximum cannot satisfy C', it is truly
            // falsified). The max-satisfying extension sets each unassigned lit
            // to its satisfying polarity for C'.
            assert!(
                rs_slack(&cprime, &trail) < 0,
                "proven resolvent NOT falsified under trail (seed {seed}): \
                 RS-slack = {} >= 0.\n  C  = {conflict:?}\n  R  = {reason:?}\n  \
                 pivot = {pivot:?}\n  C' = {cprime:?}",
                rs_slack(&cprime, &trail)
            );

            // Cross-check: NO trail-consistent complete assignment satisfies C'
            // (a direct corollary of RS-slack < 0, verified by brute force).
            for bits in 0u32..(1u32 << n) {
                let assign: Vec<bool> = (0..n).map(|i| (bits >> i) & 1 == 1).collect();
                if consistent_with_trail(&assign, &trail) {
                    assert!(
                        !satisfies(&cprime, &assign),
                        "proven resolvent satisfiable by trail-consistent assignment \
                         {assign:?} despite RS-slack < 0 (seed {seed}).\n  C' = {cprime:?}"
                    );
                }
            }

            checked += 1;
        }

        // Ensure the generator actually produced a large body of valid cases.
        assert!(
            checked >= 1000,
            "expected >= 1000 valid proven-r2o entailment cases, got {checked}"
        );
        eprintln!(
            "proven_round_to_one_semantic_entailment: {checked} (C,R) cases, \
             {brute_assignments} total assignments brute-forced"
        );
    }

    /// BUFFER-REUSE EQUIVALENCE.
    ///
    /// `resolve_proven_round_to_one_into` writes into caller-owned buffers that
    /// the solver reuses across every conflict. The entailment property test
    /// above proves each individual resolvent is sound, but it would still pass
    /// if reuse perturbed the RESULT — a stale term is only unsound when it
    /// makes the lemma stronger, and a weaker-but-still-implied lemma slips
    /// through a pure entailment check while silently degrading the solver.
    ///
    /// This pins the stronger property directly: for the same inputs, a buffer
    /// dirtied by an unrelated prior resolution must produce output BIT-IDENTICAL
    /// to a freshly allocated one. Nothing in a release build checks this
    /// otherwise — `conflict_cp.rs` explicitly declines to act as a differential
    /// oracle for the dense path, and the slack/asserting invariants in
    /// `conflict_dense.rs` are `#[cfg(debug_assertions)]`.
    #[test]
    fn proven_round_to_one_into_is_insensitive_to_buffer_reuse() {
        const N: u32 = 8;
        let mut compared = 0u64;

        // Buffers deliberately carried across every case.
        let mut dirty_out = DenseCp::new();
        let mut dirty_reduced = DenseCp::new();

        for seed in 0..40_000u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(7));

            let pivot_var = rng.range(1, N as i128) as u32;
            let pivot = PbLit {
                var: pivot_var,
                negated: rng.bool(),
            };
            let neg_pivot = PbLit {
                var: pivot_var,
                negated: !pivot.negated,
            };

            let conflict = random_forced_cp(&mut rng, N, neg_pivot);
            let reason = random_forced_cp(&mut rng, N, pivot);
            if conflict.coefficient(neg_pivot) <= 0 || reason.coefficient(pivot) <= 0 {
                continue;
            }

            let mut trail = vec![TrailVal::Unassigned; N as usize];
            for slot in trail.iter_mut() {
                *slot = match rng.range(0, 2) {
                    0 => TrailVal::Unassigned,
                    1 => TrailVal::True,
                    _ => TrailVal::False,
                };
            }
            trail[(pivot_var - 1) as usize] = if pivot.negated {
                TrailVal::False
            } else {
                TrailVal::True
            };

            // The SAME preconditions the entailment test applies. They are the
            // documented contract of the proven round-to-one step (C falsified
            // under the trail; R non-falsified and genuinely PROPAGATING the
            // pivot), and `roundToOne` carries a debug assertion that the pivot
            // coefficient divides out to exactly 1 — which only holds inside
            // that contract. Feeding unfiltered inputs tests behaviour the
            // function never promises and fires that assertion in debug builds.
            if rs_slack(&conflict, &trail) >= 0 {
                continue;
            }
            if rs_slack(&reason, &trail) < 0 {
                continue;
            }
            let mut trail_flip = trail.clone();
            trail_flip[(pivot_var - 1) as usize] = if pivot.negated {
                TrailVal::True
            } else {
                TrailVal::False
            };
            if rs_slack(&reason, &trail_flip) >= 0 {
                continue;
            }

            let dc = dense_from(&conflict);
            let dr = dense_from(&reason);

            // FRESH buffers.
            let mut fresh_out = DenseCp::new();
            let mut fresh_reduced = DenseCp::new();
            let fresh = dc.resolve_proven_round_to_one_into(
                &mut fresh_out,
                &mut fresh_reduced,
                &dr,
                pivot,
                |lit: PbLit| lit_falsified(lit, &trail),
            );

            // REUSED buffers, still holding the previous case's contents.
            let reused = dc.resolve_proven_round_to_one_into(
                &mut dirty_out,
                &mut dirty_reduced,
                &dr,
                pivot,
                |lit: PbLit| lit_falsified(lit, &trail),
            );

            assert_eq!(
                fresh.is_ok(),
                reused.is_ok(),
                "seed {seed}: fresh and reused buffers disagreed on success/failure"
            );
            if fresh.is_err() {
                // Both failed: the fail-closed contract says `out` is cleared,
                // so no partial resolvent can leak into the caller's fallback.
                assert_eq!(
                    dirty_out.to_cp_constraint(),
                    DenseCp::new().to_cp_constraint(),
                    "seed {seed}: `out` was not cleared on the error path — a partial \
                     resolvent would leak into the heuristic fallback"
                );
                continue;
            }

            assert_eq!(
                dirty_out.to_cp_constraint(),
                fresh_out.to_cp_constraint(),
                "seed {seed}: resolvent differs between a reused buffer and a fresh one — \
                 state is leaking across resolution steps"
            );
            assert_eq!(
                dirty_out.degree(),
                fresh_out.degree(),
                "seed {seed}: degree differs between a reused buffer and a fresh one"
            );
            compared += 1;
        }

        assert!(
            compared >= 500,
            "expected >= 500 comparable cases, got {compared} — the generator produced \
             too few valid resolutions for this test to mean anything"
        );
    }

    // -- reduce_to_cardinality: semantic-entailment property test ------------
    //
    // GOLD-STANDARD soundness oracle for the OVERFLOW FALLBACK. For thousands of
    // random normalized PB constraints it:
    //   1. Computes the implied cardinality reduction `card = reduce_to_cardinality`.
    //   2. Brute-forces ALL 2^n assignments and asserts EVERY assignment that
    //      satisfies the ORIGINAL also satisfies `card` (semantic entailment:
    //      original ⊨ card — the reduction NEVER cuts off a feasible point).
    // It additionally asserts the produced constraint really is a cardinality
    // (all coefficients == 1) and that its degree m is the LARGEST sound bound
    // (i.e. `card` would become UNSOUND at degree m+1: some model of the
    // original has exactly m true literals). If ANY case fails, the reduction is
    // UNSOUND — the test prints the exact (original, card) counterexample.
    // NEVER weaken this test.

    /// Whether a complete assignment (indexed by var-1) makes `lit` true.
    fn lit_true(lit: PbLit, assign: &[bool]) -> bool {
        let v = assign[(lit.var - 1) as usize];
        if lit.negated {
            !v
        } else {
            v
        }
    }

    #[test]
    fn reduce_to_cardinality_semantic_entailment() {
        const N: u32 = 8; // 2^8 = 256 assignments brute-forced per constraint.
        let mut checked = 0u64; // constraints with a non-trivial reduction
        let mut brute_assignments = 0u64; // total 2^n assignments enumerated
        let mut tightness_checked = 0u64; // cases where the m+1 tightness held

        for seed in 0..40_000u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(0x2545F4914F6CDD1D).wrapping_add(1));

            // Random normalized PB constraint. `random_cp` feeds mixed-sign raw
            // coefficients through `CpConstraint::new`, which normalizes (flips
            // negatives, cancels complements) so the dense copy has all-positive
            // coefficients — exactly the precondition of reduce_to_cardinality.
            let original = random_cp(&mut rng, N);
            let dense = dense_from(&original);

            let Some(card) = dense.reduce_to_cardinality() else {
                // Empty / trivially-true constraint (no cardinality content) or a
                // non-normalized input: the fallback fails closed. Nothing to check.
                continue;
            };

            // Structural check: a genuine cardinality constraint (unit coeffs).
            for (_, coeff) in card.iter_terms() {
                assert_eq!(
                    coeff, 1,
                    "reduction must have unit coefficients (seed {seed})"
                );
            }
            let m = card.degree();
            assert!(
                m >= 1,
                "non-trivial reduction must have degree >= 1 (seed {seed})"
            );

            let card_cp = card.to_cp_constraint();
            let card_lits: Vec<PbLit> = card.iter_terms().map(|(l, _)| l).collect();

            // --- Soundness (the gold standard): original ⊨ card. ---
            let n = N as usize;
            let mut min_true_over_models: i128 = i128::MAX;
            for bits in 0u32..(1u32 << n) {
                let assign: Vec<bool> = (0..n).map(|i| (bits >> i) & 1 == 1).collect();
                if satisfies(&original, &assign) {
                    assert!(
                        satisfies(&card_cp, &assign),
                        "UNSOUND reduce_to_cardinality (seed {seed}): assignment {assign:?} \
                         satisfies the original but NOT the cardinality reduction.\n  \
                         original = {original:?}\n  card = {card_cp:?}"
                    );
                    // Track the minimum number of card-literals true over all
                    // models, to verify m is the LARGEST sound bound.
                    let true_count: i128 =
                        card_lits.iter().filter(|&&l| lit_true(l, &assign)).count() as i128;
                    min_true_over_models = min_true_over_models.min(true_count);
                }
            }
            brute_assignments += 1u64 << n;

            // --- Tightness: m is the LARGEST sound bound. If the original is
            // feasible, some model has exactly m literals true (so degree m+1
            // would be cut off — i.e. unsound). This proves the reduction is not
            // needlessly weak.
            if min_true_over_models != i128::MAX {
                assert_eq!(
                    min_true_over_models, m,
                    "reduce_to_cardinality not tight (seed {seed}): some model has \
                     {min_true_over_models} card-literals true but degree is {m}.\n  \
                     original = {original:?}\n  card = {card_cp:?}"
                );
                tightness_checked += 1;
            }

            checked += 1;
        }

        assert!(
            checked >= 1000,
            "expected >= 1000 non-trivial cardinality reductions, got {checked}"
        );
        assert!(
            tightness_checked >= 500,
            "expected >= 500 feasible-original tightness checks, got {tightness_checked}"
        );
        eprintln!(
            "reduce_to_cardinality_semantic_entailment: {checked} constraints, \
             {brute_assignments} total assignments brute-forced, \
             {tightness_checked} tightness checks"
        );
    }

    #[test]
    fn reduce_to_cardinality_infeasible_yields_contradiction() {
        // sum a_i l_i >= d with d larger than the sum of all coefficients is
        // infeasible; the reduction must be a contradictory cardinality
        // (degree n+1 over n unit literals), which is itself a sound conflict.
        let c = cp(&[(lit(1), 2), (lit(2), 3), (lit(3), 1)], 100);
        let d = dense_from(&c);
        let card = d
            .reduce_to_cardinality()
            .expect("infeasible has a reduction");
        assert_eq!(card.len(), 3, "all literals retained");
        for (_, coeff) in card.iter_terms() {
            assert_eq!(coeff, 1);
        }
        assert_eq!(card.degree(), 4, "n + 1 = 4 over 3 literals: contradictory");
        // No assignment can satisfy sum of 3 unit literals >= 4.
        let card_cp = card.to_cp_constraint();
        for bits in 0u32..8u32 {
            let assign: Vec<bool> = (0..3).map(|i| (bits >> i) & 1 == 1).collect();
            assert!(!satisfies(&card_cp, &assign), "contradiction must be UNSAT");
        }
    }

    #[test]
    fn reduce_to_cardinality_basic_threshold() {
        // 5 x1 + 3 x2 + 2 x3 >= 6. Sorted desc: [5, 3, 2].
        // prefix(1)=5 < 6, prefix(2)=8 >= 6 => m = 2. So x1+x2+x3 >= 2.
        let c = cp(&[(lit(1), 5), (lit(2), 3), (lit(3), 2)], 6);
        let d = dense_from(&c);
        let card = d.reduce_to_cardinality().unwrap();
        assert_eq!(card.degree(), 2);
        assert_eq!(card.coefficient(lit(1)), 1);
        assert_eq!(card.coefficient(lit(2)), 1);
        assert_eq!(card.coefficient(lit(3)), 1);
    }

    #[test]
    fn reduce_to_cardinality_huge_coeffs_no_overflow() {
        // Coefficients near i128::MAX: the threshold uses i128, so no overflow,
        // and the result has unit coefficients regardless of input magnitude.
        let big = i128::MAX / 2;
        let c = cp(&[(lit(1), big), (lit(2), big), (lit(3), big)], big + 10);
        let d = dense_from(&c);
        let card = d.reduce_to_cardinality().unwrap();
        // prefix(1)=big < big+10, prefix(2)=2*big >= big+10 => m = 2.
        assert_eq!(card.degree(), 2);
        for (_, coeff) in card.iter_terms() {
            assert_eq!(coeff, 1);
        }
    }
}
