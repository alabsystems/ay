// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Simplex tableau row representation.
//!
//! Extracted from `types.rs` for code health (#5970).

use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::rational::Rational;
#[cfg(any(test, kani))]
use crate::types::add_sparse_term_rat;
use crate::types::normalize_sparse_coeffs_rat;

/// Precision level of a tableau row's coefficients (#8185).
///
/// Tracks the minimum precision needed to represent ALL coefficients and the
/// constant in a row. Used by adaptive-precision pivot paths to select the
/// fastest arithmetic implementation:
/// - `I64`: all numerators and denominators fit in i64 (hardware multiply/add)
/// - `I128`: all fit in i128 (Rust native, handles overflow from i64 products)
/// - `Big`: at least one coefficient requires arbitrary-precision `BigRational`
///
/// Reference: OpenSMT2 `FastRational.h` uses a similar two-tier approach.
/// Z3's `mpq` tracks limb count for fast-path decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RowPrecision {
    /// All coefficients and constant fit in i64 numerator/denominator.
    I64,
    /// All fit in i128 but at least one exceeds i64.
    I128,
    /// At least one coefficient is arbitrary-precision (Big variant).
    Big,
}

impl RowPrecision {
    /// Merge two precision levels: returns the coarser of the two.
    #[inline]
    pub(crate) fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Big, _) | (_, Self::Big) => Self::Big,
            (Self::I128, _) | (_, Self::I128) => Self::I128,
            _ => Self::I64,
        }
    }

    /// Determine the precision level of a single `Rational` value.
    #[inline]
    pub(crate) fn of_rational(r: &Rational) -> Self {
        match r.try_as_i64() {
            Some(_) => Self::I64,
            None => match r.try_as_i128() {
                Some(_) => Self::I128,
                None => Self::Big,
            },
        }
    }
}

/// A row in the simplex tableau
///
/// Represents: basic_var = Σ(coeff * var) + constant
#[derive(Debug, Clone)]
pub(crate) struct TableauRow {
    /// The basic variable for this row
    pub(crate) basic_var: u32,
    /// Sparse coefficients: (variable, coefficient) — fast Rational for i64 fast path
    pub(crate) coeffs: Vec<(u32, Rational)>,
    /// Constant term (RHS constant after normalization)
    pub(crate) constant: Rational,
    /// Cached precision level of all coefficients + constant (#8185).
    /// Updated on row construction and after substitution/pivot operations.
    pub(crate) precision: RowPrecision,
}

impl TableauRow {
    /// Create a tableau row with canonicalized sparse coefficients.
    pub(crate) fn new_rat(
        basic_var: u32,
        coeffs: Vec<(u32, Rational)>,
        constant: Rational,
    ) -> Self {
        let normalized = normalize_sparse_coeffs_rat(coeffs);
        let precision = Self::compute_precision_of(&normalized, &constant);
        Self {
            basic_var,
            coeffs: normalized,
            constant,
            precision,
        }
    }

    /// Create from BigRational coefficients (convenience for callers not yet migrated).
    #[allow(dead_code)]
    pub(crate) fn new(
        basic_var: u32,
        coeffs: Vec<(u32, BigRational)>,
        constant: BigRational,
    ) -> Self {
        let rat_coeffs: Vec<(u32, Rational)> = coeffs
            .into_iter()
            .map(|(v, c)| (v, Rational::from(c)))
            .collect();
        Self::new_rat(basic_var, rat_coeffs, Rational::from(constant))
    }

    /// Compute the precision level for a set of coefficients and a constant.
    #[inline]
    fn compute_precision_of(coeffs: &[(u32, Rational)], constant: &Rational) -> RowPrecision {
        let mut prec = RowPrecision::of_rational(constant);
        for (_, c) in coeffs {
            prec = prec.merge(RowPrecision::of_rational(c));
            if matches!(prec, RowPrecision::Big) {
                return prec; // can't get worse
            }
        }
        prec
    }

    /// Recompute and cache the precision level from current coefficients + constant.
    /// Called after operations that may change coefficient values (substitute, pivot).
    #[inline]
    pub(crate) fn recompute_precision(&mut self) {
        self.precision = Self::compute_precision_of(&self.coeffs, &self.constant);
    }

    /// Return the cached precision level.
    #[inline]
    pub(crate) fn precision(&self) -> RowPrecision {
        self.precision
    }

    /// Returns `true` when every coefficient and the constant are i64 integers.
    #[inline]
    pub(crate) fn is_all_i64(&self) -> bool {
        if !matches!(self.precision, RowPrecision::I64) {
            return false;
        }
        if !self.constant.is_integer() {
            return false;
        }
        self.coeffs.iter().all(|(_, c)| c.is_integer())
    }

    /// Extract all coefficients as `(var, i64)` pairs.
    pub(crate) fn extract_i64_coeffs(&self) -> Option<Vec<(u32, i64)>> {
        self.coeffs
            .iter()
            .map(|(v, c)| c.to_i64().map(|n| (*v, n)))
            .collect()
    }

    /// Extract coefficients into caller-provided split i64 buffers.
    ///
    /// This avoids allocating a fresh `(var, coeff)` vector when the caller
    /// already has reusable scratch buffers.
    #[allow(dead_code)]
    pub(crate) fn extract_i64_parts_into(
        &self,
        vars_out: &mut Vec<u32>,
        coeffs_out: &mut Vec<i64>,
    ) -> bool {
        vars_out.clear();
        coeffs_out.clear();
        vars_out.reserve(self.coeffs.len());
        coeffs_out.reserve(self.coeffs.len());

        for (v, c) in &self.coeffs {
            let Some(n) = c.to_i64() else {
                vars_out.clear();
                coeffs_out.clear();
                return false;
            };
            vars_out.push(*v);
            coeffs_out.push(n);
        }

        true
    }

    /// Extract the full row (coefficients + constant) as i64 values.
    #[allow(dead_code)]
    pub(crate) fn extract_i64_row(&self) -> Option<(Vec<(u32, i64)>, i64)> {
        let coeffs = self.extract_i64_coeffs()?;
        let constant = self.constant.to_i64()?;
        Some((coeffs, constant))
    }

    /// Get the coefficient for a variable, or zero if not present
    pub(crate) fn coeff(&self, var: u32) -> Rational {
        self.coeffs
            .binary_search_by_key(&var, |(v, _)| *v)
            .ok()
            .map_or_else(Rational::zero, |idx| self.coeffs[idx].1.clone())
    }

    /// Get a reference to the coefficient for a variable, or `None` if zero/absent.
    /// Avoids cloning in hot paths where only a reference is needed.
    #[inline]
    pub(crate) fn coeff_ref(&self, var: u32) -> Option<&Rational> {
        self.coeffs
            .binary_search_by_key(&var, |(v, _)| *v)
            .ok()
            .map(|idx| &self.coeffs[idx].1)
    }

    /// Get coefficient as BigRational (for callers that still need it).
    pub(crate) fn coeff_big(&self, var: u32) -> BigRational {
        self.coeff(var).to_big()
    }

    #[cfg(any(test, kani))]
    pub(crate) fn add_coeff(&mut self, var: u32, coeff: Rational) {
        add_sparse_term_rat(&mut self.coeffs, var, coeff);
    }

    #[cfg(kani)] // Only used by #[cfg(kani)] verification module
    pub(crate) fn contains(&self, var: u32) -> bool {
        self.coeffs.binary_search_by_key(&var, |(v, _)| *v).is_ok()
    }

    #[cfg(any(test, kani))]
    pub(crate) fn remove_coeff(&mut self, var: u32) {
        if let Ok(idx) = self.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
            self.coeffs.remove(idx);
        }
    }

    /// Substitute `entering_var` with a scaled copy of `subst_coeffs` in a single
    /// sorted-merge pass, avoiding O(w²) from repeated `add_coeff` calls (#6194).
    ///
    /// Equivalent to: `remove_coeff(entering_var)` then `add_coeff(v, c * scale)`
    /// for each `(v, c)` in `subst_coeffs`, but runs in O(w log w) instead of O(w²).
    /// `subst_coeffs` must be sorted by variable index (which TableauRow guarantees).
    /// The constant adjustment must be applied separately by the caller.
    /// #8406: Monomorphic i64 fast paths added to scaling and merge addition.
    pub(crate) fn substitute_var(
        &mut self,
        entering_var: u32,
        subst_coeffs: &[(u32, Rational)],
        scale: &Rational,
    ) {
        fn next_old_term(
            iter: &mut std::vec::IntoIter<(u32, Rational)>,
            entering_var: u32,
        ) -> Option<(u32, Rational)> {
            iter.find(|(var, _)| *var != entering_var)
        }

        // Determine scale category once to avoid repeated pattern matching.
        // Most pivot coefficients are ±1 for sparse LRA tableaux.
        let scale_is_one = scale.is_one();
        let scale_is_neg_one = scale.is_neg_one();
        // #8406: Extract i64 scale once for the monomorphic fast path.
        let scale_i64 = match scale {
            Rational::Small(sn, sd) => Some((*sn, *sd)),
            _ => None,
        };

        fn next_scaled_addition(
            iter: &mut std::slice::Iter<'_, (u32, Rational)>,
            entering_var: u32,
            scale: &Rational,
            scale_is_one: bool,
            scale_is_neg_one: bool,
            scale_i64: Option<(i64, i64)>,
        ) -> Option<(u32, Rational)> {
            iter.find_map(|(var, coeff)| {
                if *var == entering_var {
                    return None;
                }
                // Fast paths: avoid full Rational multiply for ±1 scale.
                let scaled = if scale_is_one {
                    coeff.clone()
                } else if scale_is_neg_one {
                    -coeff
                } else if let Some((sn, sd)) = scale_i64 {
                    // #8406: monomorphic i64 fast path
                    match coeff.scale_small_i64(sn, sd) {
                        Some(r) => r,
                        None => coeff * scale,
                    }
                } else {
                    coeff * scale
                };
                if scaled.is_zero() {
                    None
                } else {
                    Some((*var, scaled))
                }
            })
        }

        // Stream old coeffs and scaled substitution terms directly into the
        // merged result so the pivot loop avoids allocating an intermediate
        // additions vector on every affected row.
        let old = std::mem::take(&mut self.coeffs);
        let mut result = Vec::with_capacity(old.len() + subst_coeffs.len());
        let mut old_iter = old.into_iter();
        let mut subst_iter = subst_coeffs.iter();
        let mut old_term = next_old_term(&mut old_iter, entering_var);
        let mut addition = next_scaled_addition(
            &mut subst_iter,
            entering_var,
            scale,
            scale_is_one,
            scale_is_neg_one,
            scale_i64,
        );

        loop {
            match (old_term.as_ref(), addition.as_ref()) {
                (Some((old_var, _)), Some((new_var, _))) => match old_var.cmp(new_var) {
                    std::cmp::Ordering::Less => {
                        result.push(old_term.take().expect("old term present"));
                        old_term = next_old_term(&mut old_iter, entering_var);
                    }
                    std::cmp::Ordering::Greater => {
                        result.push(addition.take().expect("addition present"));
                        addition = next_scaled_addition(
                            &mut subst_iter,
                            entering_var,
                            scale,
                            scale_is_one,
                            scale_is_neg_one,
                            scale_i64,
                        );
                    }
                    std::cmp::Ordering::Equal => {
                        let (var, old_coeff) = old_term.take().expect("old term present");
                        let (_, added_coeff) = addition.take().expect("addition present");
                        // #8406: i64 fast path for merge addition
                        let merged = match old_coeff.add_small_i64(&added_coeff) {
                            Some(r) => r,
                            None => old_coeff + added_coeff,
                        };
                        if !merged.is_zero() {
                            result.push((var, merged));
                        }
                        old_term = next_old_term(&mut old_iter, entering_var);
                        addition = next_scaled_addition(
                            &mut subst_iter,
                            entering_var,
                            scale,
                            scale_is_one,
                            scale_is_neg_one,
                            scale_i64,
                        );
                    }
                },
                (Some(_), None) => {
                    result.push(old_term.take().expect("old term present"));
                    result.extend(old_iter.filter(|(var, _)| *var != entering_var));
                    break;
                }
                (None, Some(_)) => {
                    result.push(addition.take().expect("addition present"));
                    result.extend(std::iter::from_fn(|| {
                        next_scaled_addition(
                            &mut subst_iter,
                            entering_var,
                            scale,
                            scale_is_one,
                            scale_is_neg_one,
                            scale_i64,
                        )
                    }));
                    break;
                }
                (None, None) => break,
            }
        }

        self.coeffs = result;
    }

    /// Like `substitute_var`, but also tracks column-index deltas as a byproduct
    /// of the merge — no post-hoc binary searches needed (#8003).
    ///
    /// Returns `(added, removed)` where:
    /// - `added`: variables that were NOT in this row before but ARE now
    /// - `removed`: variables that WERE in this row before but are NOT now
    ///
    /// `entering_var` is always in `removed` (since it existed and is being
    /// substituted out). The caller's `col_added`/`col_removed` buffers are
    /// cleared and populated.
    #[allow(dead_code)]
    pub(crate) fn substitute_var_with_col_deltas(
        &mut self,
        entering_var: u32,
        subst_coeffs: &[(u32, Rational)],
        scale: &Rational,
        col_added: &mut Vec<u32>,
        col_removed: &mut Vec<u32>,
    ) {
        col_added.clear();
        col_removed.clear();

        let scale_is_one = scale.is_one();
        let scale_is_neg_one = scale.is_neg_one();

        let old = std::mem::take(&mut self.coeffs);
        let mut result = Vec::with_capacity(old.len() + subst_coeffs.len());

        // Two-pointer merge over old row (sorted) and subst_coeffs (sorted).
        // entering_var is skipped in both streams.
        let mut oi = 0usize; // index into old
        let mut si = 0usize; // index into subst_coeffs

        // Skip dead entries (entering_var) efficiently via helper closures.
        // old is sorted, subst_coeffs is sorted.

        // Advance old past entering_var entries
        #[inline(always)]
        fn advance_old(old: &[(u32, Rational)], oi: &mut usize, entering_var: u32) -> bool {
            while *oi < old.len() {
                if old[*oi].0 != entering_var {
                    return true;
                }
                *oi += 1;
            }
            false
        }

        // Advance subst past entering_var entries and compute scaled value.
        // #8406: When scale_i64 is available, uses monomorphic i64 path to
        // bypass Rational enum dispatch in the inner scaling operation.
        #[inline(always)]
        fn advance_subst(
            subst: &[(u32, Rational)],
            si: &mut usize,
            entering_var: u32,
            scale: &Rational,
            scale_is_one: bool,
            scale_is_neg_one: bool,
            scale_i64: Option<(i64, i64)>,
        ) -> Option<(u32, Rational)> {
            while *si < subst.len() {
                let (v, ref c) = subst[*si];
                *si += 1;
                if v == entering_var {
                    continue;
                }
                let scaled = if scale_is_one {
                    c.clone()
                } else if scale_is_neg_one {
                    -c
                } else if let Some((sn, sd)) = scale_i64 {
                    // #8406: monomorphic i64 fast path
                    match c.scale_small_i64(sn, sd) {
                        Some(r) => r,
                        None => c * scale,
                    }
                } else {
                    c * scale
                };
                if !scaled.is_zero() {
                    return Some((v, scaled));
                }
            }
            None
        }

        // #8406: Extract i64 scale once for the monomorphic fast path.
        let scale_i64 = match scale {
            Rational::Small(sn, sd) => Some((*sn, *sd)),
            _ => None,
        };

        // Track that entering_var is being removed (it was in old row)
        let had_entering = old.binary_search_by_key(&entering_var, |(v, _)| *v).is_ok();
        if had_entering {
            col_removed.push(entering_var);
        }

        let has_old = advance_old(&old, &mut oi, entering_var);
        let mut pending_subst = advance_subst(
            subst_coeffs,
            &mut si,
            entering_var,
            scale,
            scale_is_one,
            scale_is_neg_one,
            scale_i64,
        );

        let mut have_old = has_old;

        loop {
            match (have_old, pending_subst.as_ref()) {
                (true, Some((sv, _))) => {
                    let (ov, _) = &old[oi];
                    match ov.cmp(sv) {
                        std::cmp::Ordering::Less => {
                            // Old var not in subst — survives unchanged
                            result.push(old[oi].clone());
                            oi += 1;
                            have_old = advance_old(&old, &mut oi, entering_var);
                        }
                        std::cmp::Ordering::Greater => {
                            // New var from subst — col addition
                            let (v, c) = pending_subst.take().expect("subst present");
                            col_added.push(v);
                            result.push((v, c));
                            pending_subst = advance_subst(
                                subst_coeffs,
                                &mut si,
                                entering_var,
                                scale,
                                scale_is_one,
                                scale_is_neg_one,
                                scale_i64,
                            );
                        }
                        std::cmp::Ordering::Equal => {
                            // Both have this var — merge
                            let (var, ref old_c) = old[oi];
                            let (_, added_c) = pending_subst.take().expect("subst present");
                            // #8406: i64 fast path for merge addition
                            let merged = match old_c.add_small_i64(&added_c) {
                                Some(r) => r,
                                None => old_c + &added_c,
                            };
                            if merged.is_zero() {
                                // Was present, now gone — col removal
                                col_removed.push(var);
                            } else {
                                result.push((var, merged));
                            }
                            oi += 1;
                            have_old = advance_old(&old, &mut oi, entering_var);
                            pending_subst = advance_subst(
                                subst_coeffs,
                                &mut si,
                                entering_var,
                                scale,
                                scale_is_one,
                                scale_is_neg_one,
                                scale_i64,
                            );
                        }
                    }
                }
                (true, None) => {
                    // Drain remaining old entries (skip entering_var)
                    result.push(old[oi].clone());
                    oi += 1;
                    while oi < old.len() {
                        if old[oi].0 != entering_var {
                            result.push(old[oi].clone());
                        }
                        oi += 1;
                    }
                    break;
                }
                (false, Some(_)) => {
                    // Drain remaining subst entries — all are new additions
                    let (v, c) = pending_subst.take().expect("subst present");
                    col_added.push(v);
                    result.push((v, c));
                    while let Some((v, c)) = advance_subst(
                        subst_coeffs,
                        &mut si,
                        entering_var,
                        scale,
                        scale_is_one,
                        scale_is_neg_one,
                        scale_i64,
                    ) {
                        col_added.push(v);
                        result.push((v, c));
                    }
                    break;
                }
                (false, None) => break,
            }
        }

        self.coeffs = result;
    }

    /// Fast-path substitution using i128 arithmetic when all values are i64 integers.
    pub(crate) fn substitute_var_i64(
        &mut self,
        entering_var: u32,
        subst_coeffs: &[(u32, Rational)],
        scale: &Rational,
    ) -> bool {
        let scale_i64 = match scale.to_i64() {
            Some(s) => s,
            None => return false,
        };
        let scale_128 = i128::from(scale_i64);
        let mut subst_i64: Vec<(u32, i128)> = Vec::with_capacity(subst_coeffs.len());
        for &(v, ref c) in subst_coeffs {
            if v == entering_var {
                continue;
            }
            let c_i64 = match c.to_i64() {
                Some(n) => n,
                None => return false,
            };
            let scaled = i128::from(c_i64) * scale_128;
            if scaled != 0 {
                subst_i64.push((v, scaled));
            }
        }
        let old = std::mem::take(&mut self.coeffs);
        let mut result = Vec::with_capacity(old.len() + subst_i64.len());
        let mut oi = 0usize;
        let mut si = 0usize;
        while oi < old.len() && old[oi].0 == entering_var {
            oi += 1;
        }
        loop {
            let have_old = oi < old.len();
            let have_subst = si < subst_i64.len();
            match (have_old, have_subst) {
                (true, true) => {
                    let (ov, ref oc) = old[oi];
                    let (sv, sc) = subst_i64[si];
                    match ov.cmp(&sv) {
                        std::cmp::Ordering::Less => {
                            result.push(old[oi].clone());
                            oi += 1;
                            while oi < old.len() && old[oi].0 == entering_var {
                                oi += 1;
                            }
                        }
                        std::cmp::Ordering::Greater => {
                            result.push((sv, Rational::from_i128(sc)));
                            si += 1;
                        }
                        std::cmp::Ordering::Equal => {
                            let old_val = match oc.to_i64() {
                                Some(n) => i128::from(n),
                                None => {
                                    self.coeffs = old;
                                    return false;
                                }
                            };
                            let merged = old_val + sc;
                            if merged != 0 {
                                result.push((ov, Rational::from_i128(merged)));
                            }
                            oi += 1;
                            si += 1;
                            while oi < old.len() && old[oi].0 == entering_var {
                                oi += 1;
                            }
                        }
                    }
                }
                (true, false) => {
                    while oi < old.len() {
                        if old[oi].0 != entering_var {
                            result.push(old[oi].clone());
                        }
                        oi += 1;
                    }
                    break;
                }
                (false, true) => {
                    while si < subst_i64.len() {
                        let (v, sc) = subst_i64[si];
                        result.push((v, Rational::from_i128(sc)));
                        si += 1;
                    }
                    break;
                }
                (false, false) => break,
            }
        }
        self.coeffs = result;
        self.recompute_precision();
        true
    }

    /// Fast-path i128 substitution with column-index deltas (#8257).
    /// Like `substitute_var_i64` but also computes col_added/col_removed
    /// for the column index, enabling use in the col-index pivot path.
    /// Returns false if any coefficient doesn't fit in i64.
    ///
    /// Key performance advantage: uses pure i128 arithmetic with no Rational
    /// enum dispatch, and the sorted merge naturally produces col deltas.
    pub(crate) fn substitute_var_i64_with_col_deltas(
        &mut self,
        entering_var: u32,
        subst_coeffs: &[(u32, Rational)],
        scale: &Rational,
        col_added: &mut Vec<u32>,
        col_removed: &mut Vec<u32>,
    ) -> bool {
        let scale_i64 = match scale.to_i64() {
            Some(s) => s,
            None => return false,
        };
        let scale_128 = i128::from(scale_i64);

        // Pre-compute scaled substitution terms in i128.
        let mut subst_i64: Vec<(u32, i128)> = Vec::with_capacity(subst_coeffs.len());
        for &(v, ref c) in subst_coeffs {
            if v == entering_var {
                continue;
            }
            let c_i64 = match c.to_i64() {
                Some(n) => n,
                None => return false,
            };
            let scaled = i128::from(c_i64) * scale_128;
            if scaled != 0 {
                subst_i64.push((v, scaled));
            }
        }

        col_added.clear();
        col_removed.clear();

        let old = std::mem::take(&mut self.coeffs);
        let mut result = Vec::with_capacity(old.len() + subst_i64.len());
        let mut oi = 0usize;
        let mut si = 0usize;

        // Skip entering_var in old coefficients.
        while oi < old.len() && old[oi].0 == entering_var {
            col_removed.push(entering_var);
            oi += 1;
        }

        loop {
            let have_old = oi < old.len();
            let have_subst = si < subst_i64.len();
            match (have_old, have_subst) {
                (true, true) => {
                    let (ov, ref oc) = old[oi];
                    let (sv, sc) = subst_i64[si];
                    match ov.cmp(&sv) {
                        std::cmp::Ordering::Less => {
                            // Old-only: survives unchanged.
                            result.push(old[oi].clone());
                            oi += 1;
                            while oi < old.len() && old[oi].0 == entering_var {
                                col_removed.push(entering_var);
                                oi += 1;
                            }
                        }
                        std::cmp::Ordering::Greater => {
                            // New addition from substitution.
                            col_added.push(sv);
                            result.push((sv, Rational::from_i128(sc)));
                            si += 1;
                        }
                        std::cmp::Ordering::Equal => {
                            // Merge: add old + scaled.
                            let old_val = match oc.to_i64() {
                                Some(n) => i128::from(n),
                                None => {
                                    self.coeffs = old;
                                    return false;
                                }
                            };
                            let merged = old_val + sc;
                            if merged != 0 {
                                result.push((ov, Rational::from_i128(merged)));
                            } else {
                                col_removed.push(ov);
                            }
                            oi += 1;
                            si += 1;
                            while oi < old.len() && old[oi].0 == entering_var {
                                col_removed.push(entering_var);
                                oi += 1;
                            }
                        }
                    }
                }
                (true, false) => {
                    while oi < old.len() {
                        if old[oi].0 != entering_var {
                            result.push(old[oi].clone());
                        } else {
                            col_removed.push(entering_var);
                        }
                        oi += 1;
                    }
                    break;
                }
                (false, true) => {
                    while si < subst_i64.len() {
                        let (v, sc) = subst_i64[si];
                        col_added.push(v);
                        result.push((v, Rational::from_i128(sc)));
                        si += 1;
                    }
                    break;
                }
                (false, false) => break,
            }
        }

        self.coeffs = result;
        // NOTE: recompute_precision() is NOT called here - the caller
        // (pivot method) handles it after updating the constant (#8257).
        true
    }

    /// Fast-path i128 substitution with pre-computed scaled terms (#8003 TL65).
    /// Like `substitute_var_i64_with_col_deltas` but takes pre-computed `subst_i128`
    /// terms, avoiding per-row allocation. The caller pre-computes the scaled terms
    /// once per pivot and reuses them across all affected rows.
    ///
    /// `scale_i64`: the entering variable's coefficient in this row (must be i64).
    /// `subst_i128`: pre-computed `(var, coeff)` pairs from the pivot row, already
    /// scaled by the UNIT scale (coefficient 1). The actual scale is applied per-row
    /// by multiplying each subst term by `scale_i64`.
    ///
    /// Returns false if any coefficient in this row doesn't fit in i64.
    pub(crate) fn substitute_var_i64_precomputed(
        &mut self,
        entering_var: u32,
        subst_i128: &[(u32, i128)],
        scale_i64: i64,
        col_added: &mut Vec<u32>,
        col_removed: &mut Vec<u32>,
    ) -> bool {
        let scale_128 = i128::from(scale_i64);

        col_added.clear();
        col_removed.clear();

        let old = std::mem::take(&mut self.coeffs);
        let mut result = Vec::with_capacity(old.len() + subst_i128.len());
        let mut oi = 0usize;
        let mut si = 0usize;

        // Skip entering_var in old coefficients.
        while oi < old.len() && old[oi].0 == entering_var {
            col_removed.push(entering_var);
            oi += 1;
        }

        loop {
            let have_old = oi < old.len();
            let have_subst = si < subst_i128.len();
            match (have_old, have_subst) {
                (true, true) => {
                    let (ov, ref oc) = old[oi];
                    let (sv, sc) = subst_i128[si];
                    let scaled = sc * scale_128;
                    match ov.cmp(&sv) {
                        std::cmp::Ordering::Less => {
                            result.push(old[oi].clone());
                            oi += 1;
                            while oi < old.len() && old[oi].0 == entering_var {
                                col_removed.push(entering_var);
                                oi += 1;
                            }
                        }
                        std::cmp::Ordering::Greater => {
                            if scaled != 0 {
                                col_added.push(sv);
                                result.push((sv, Rational::from_i128(scaled)));
                            }
                            si += 1;
                        }
                        std::cmp::Ordering::Equal => {
                            let old_val = match oc.to_i64() {
                                Some(n) => i128::from(n),
                                None => {
                                    self.coeffs = old;
                                    return false;
                                }
                            };
                            let merged = old_val + scaled;
                            if merged != 0 {
                                result.push((ov, Rational::from_i128(merged)));
                            } else {
                                col_removed.push(ov);
                            }
                            oi += 1;
                            si += 1;
                            while oi < old.len() && old[oi].0 == entering_var {
                                col_removed.push(entering_var);
                                oi += 1;
                            }
                        }
                    }
                }
                (true, false) => {
                    while oi < old.len() {
                        if old[oi].0 != entering_var {
                            result.push(old[oi].clone());
                        } else {
                            col_removed.push(entering_var);
                        }
                        oi += 1;
                    }
                    break;
                }
                (false, true) => {
                    while si < subst_i128.len() {
                        let (v, sc) = subst_i128[si];
                        let scaled = sc * scale_128;
                        if scaled != 0 {
                            col_added.push(v);
                            result.push((v, Rational::from_i128(scaled)));
                        }
                        si += 1;
                    }
                    break;
                }
                (false, false) => break,
            }
        }

        self.coeffs = result;
        true
    }

    /// O(1) work-vector-enhanced substitution (#8003 Gap 2, #8257).
    /// Matches Z3 save_var_pos() + ADD_ROW pattern (sparse_matrix_def.h:321-388).
    ///
    /// Phase 1: Populate work_vec with position indices for O(1) lookup.
    /// Phase 2: For each subst term, look up position in O(1). If existing,
    ///          update in-place (or mark cancelled with CANCELLED sentinel).
    ///          If new, collect into sorted additions vector.
    /// Phase 3: Build result in a single sorted-merge pass over surviving old
    ///          coefficients and sorted new additions — no sort needed.
    ///
    /// #8257: Eliminates O(n*m) quadratic scan from prior version where each
    /// old coefficient was checked against all mods via linear search.
    /// Now uses CANCELLED sentinel in work_vec for O(1) cancellation check.
    ///
    /// #8406: Monomorphic i64 fast path. When `scale` is `Small(sn, sd)`, the
    /// inner loop uses `scale_small_i64` and `add_small_i64` which bypass
    /// Rational enum dispatch entirely, computing in pure i64/i128 arithmetic.
    /// Falls back to generic Rational ops only when i64 overflow occurs.
    pub(crate) fn substitute_var_work_vec(
        &mut self,
        entering_var: u32,
        subst_coeffs: &[(u32, Rational)],
        scale: &Rational,
        work_vec: &mut [i32],
        work_dirty: &mut Vec<u32>,
        col_added: &mut Vec<u32>,
        col_removed: &mut Vec<u32>,
    ) {
        /// Sentinel value in work_vec meaning "this position was cancelled to zero".
        const CANCELLED: i32 = i32::MIN;

        col_added.clear();
        col_removed.clear();

        // Phase 1: populate work_vec with position indices.
        for (pos, &(var, _)) in self.coeffs.iter().enumerate() {
            work_vec[var as usize] = pos as i32;
            work_dirty.push(var);
        }
        let entering_pos = work_vec[entering_var as usize];
        if entering_pos >= 0 {
            col_removed.push(entering_var);
            // Mark entering_var as cancelled so it is skipped in Phase 3.
            work_vec[entering_var as usize] = CANCELLED;
        }

        let scale_is_one = scale.is_one();
        let scale_is_neg_one = scale.is_neg_one();
        // #8406: Extract i64 scale once for the monomorphic fast path.
        let scale_i64 = match scale {
            Rational::Small(sn, sd) => Some((*sn, *sd)),
            _ => None,
        };

        // Collect new additions (vars not in old row). These are already sorted
        // because subst_coeffs comes from a TableauRow which is sorted by var.
        let mut additions: Vec<(u32, Rational)> = Vec::new();

        // Phase 2: Process substitution terms.
        for &(var, ref coeff) in subst_coeffs {
            if var == entering_var {
                continue;
            }
            // #8406: i64 fast path for scaling
            let scaled = if scale_is_one {
                coeff.clone()
            } else if scale_is_neg_one {
                -coeff
            } else if let Some((sn, sd)) = scale_i64 {
                match coeff.scale_small_i64(sn, sd) {
                    Some(r) => r,
                    None => coeff * scale,
                }
            } else {
                coeff * scale
            };
            if scaled.is_zero() {
                continue;
            }

            let pos = if (var as usize) < work_vec.len() {
                work_vec[var as usize]
            } else {
                -1
            };
            if pos >= 0 && pos != CANCELLED {
                // Existing coefficient: merge in-place.
                let existing = &self.coeffs[pos as usize].1;
                let merged = match existing.add_small_i64(&scaled) {
                    Some(r) => r,
                    None => existing + &scaled,
                };
                if merged.is_zero() {
                    // Cancelled to zero: mark in work_vec for O(1) skip in Phase 3.
                    col_removed.push(var);
                    work_vec[var as usize] = CANCELLED;
                } else {
                    // Updated in-place.
                    self.coeffs[pos as usize].1 = merged;
                }
            } else if pos != CANCELLED {
                // New variable: add to sorted additions list.
                col_added.push(var);
                if (var as usize) < work_vec.len() {
                    work_vec[var as usize] = i32::MAX;
                    work_dirty.push(var);
                }
                additions.push((var, scaled));
            }
            // pos == CANCELLED: entering_var position, skip.
        }

        // Phase 3: Compact the coefficient vector.
        // Strategy depends on whether we have additions and/or removals.
        let has_removals = !col_removed.is_empty();
        let add_count = additions.len();

        if add_count == 0 && !has_removals {
            // Ultra-fast path: no additions, no removals — coefficients were
            // updated in-place in Phase 2. Nothing to rebuild.
            // work_vec[var] still holds the original positions, which are still
            // correct since the coefficient vector was not modified structurally.
        } else if add_count == 0 {
            // In-place compaction: remove cancelled entries without allocation.
            // retain() preserves order and is O(n) with no allocation.
            // Track new positions in work_vec as we compact (#8003 TL87).
            let mut write_pos = 0usize;
            for read_pos in 0..self.coeffs.len() {
                let var = self.coeffs[read_pos].0;
                let vi = var as usize;
                if vi < work_vec.len() && work_vec[vi] == CANCELLED {
                    continue;
                }
                if write_pos != read_pos {
                    self.coeffs.swap(write_pos, read_pos);
                }
                // Update work_vec with the new position for this variable.
                if vi < work_vec.len() {
                    work_vec[vi] = write_pos as i32;
                }
                write_pos += 1;
            }
            self.coeffs.truncate(write_pos);
        } else {
            // Full rebuild: merge surviving old coefficients with sorted additions.
            let old_count = self.coeffs.len();
            let mut new_coeffs: Vec<(u32, Rational)> = Vec::with_capacity(old_count + add_count);
            let mut ai = 0usize;
            for i in 0..old_count {
                let var = self.coeffs[i].0;
                let vi = var as usize;
                if vi < work_vec.len() && work_vec[vi] == CANCELLED {
                    continue;
                }
                // Emit all additions with var < current old var.
                while ai < add_count && additions[ai].0 < var {
                    let av = additions[ai].0;
                    let avi = av as usize;
                    // Track new position for added variables (#8003 TL87).
                    if avi < work_vec.len() {
                        work_vec[avi] = new_coeffs.len() as i32;
                    }
                    new_coeffs.push(std::mem::replace(&mut additions[ai], (0, Rational::zero())));
                    ai += 1;
                }
                // Track new position for surviving variables (#8003 TL87).
                if vi < work_vec.len() {
                    work_vec[vi] = new_coeffs.len() as i32;
                }
                new_coeffs.push((var, self.coeffs[i].1.clone()));
            }
            while ai < add_count {
                let av = additions[ai].0;
                let avi = av as usize;
                if avi < work_vec.len() {
                    work_vec[avi] = new_coeffs.len() as i32;
                }
                new_coeffs.push(std::mem::replace(&mut additions[ai], (0, Rational::zero())));
                ai += 1;
            }
            self.coeffs = new_coeffs;
        }

        // NOTE: recompute_precision() is NOT called here because the pivot
        // method updates the constant term AFTER this function returns, then
        // calls recompute_precision() once covering both changes (#8257).
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_row_precision_all_small() {
        let row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(3i64)), (2, Rational::from(-5i64))],
            Rational::from(7i64),
        );
        assert_eq!(row.precision(), RowPrecision::I64);
    }

    #[test]
    fn test_row_precision_fractional_small() {
        let row = TableauRow::new_rat(
            0,
            vec![(1, Rational::new(1, 3)), (2, Rational::new(-7, 11))],
            Rational::new(5, 2),
        );
        assert_eq!(row.precision(), RowPrecision::I64);
    }

    #[test]
    fn test_row_precision_i128_coeff() {
        // 2 * i64::MAX overflows i64 but fits in i128 → I128 precision
        let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
        assert!(matches!(big, Rational::Big(_)));
        let row = TableauRow::new_rat(
            0,
            vec![(1, big), (2, Rational::from(1i64))],
            Rational::from(0i64),
        );
        assert_eq!(row.precision(), RowPrecision::I128);
    }

    #[test]
    fn test_row_precision_truly_big_coeff() {
        // Create a value that exceeds i128 range
        use num_bigint::BigInt;
        use num_rational::BigRational;
        let huge_numer = BigInt::from(i128::MAX) * BigInt::from(2);
        let br = BigRational::new(huge_numer, BigInt::from(1));
        let big_rat = Rational::from_big(br);
        let row = TableauRow::new_rat(
            0,
            vec![(1, big_rat), (2, Rational::from(1i64))],
            Rational::from(0i64),
        );
        assert_eq!(row.precision(), RowPrecision::Big);
    }

    #[test]
    fn test_row_precision_recompute() {
        let mut row = TableauRow::new_rat(0, vec![(1, Rational::from(3i64))], Rational::from(0i64));
        assert_eq!(row.precision(), RowPrecision::I64);

        // Replace with an i128-range coefficient to test recompute
        let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
        row.coeffs = vec![(1, big)];
        row.recompute_precision();
        assert_eq!(row.precision(), RowPrecision::I128);

        // Now replace with a truly big coefficient
        use num_bigint::BigInt;
        use num_rational::BigRational;
        let huge = BigRational::new(BigInt::from(i128::MAX) * BigInt::from(2), BigInt::from(1));
        row.coeffs = vec![(1, Rational::from_big(huge))];
        row.recompute_precision();
        assert_eq!(row.precision(), RowPrecision::Big);
    }

    #[test]
    fn test_row_precision_empty_row() {
        let row = TableauRow::new_rat(0, vec![], Rational::from(42i64));
        assert_eq!(row.precision(), RowPrecision::I64);
    }

    #[test]
    fn test_row_precision_merge() {
        assert_eq!(
            RowPrecision::I64.merge(RowPrecision::I64),
            RowPrecision::I64
        );
        assert_eq!(
            RowPrecision::I64.merge(RowPrecision::I128),
            RowPrecision::I128
        );
        assert_eq!(
            RowPrecision::I128.merge(RowPrecision::I64),
            RowPrecision::I128
        );
        assert_eq!(
            RowPrecision::I64.merge(RowPrecision::Big),
            RowPrecision::Big
        );
        assert_eq!(
            RowPrecision::Big.merge(RowPrecision::I64),
            RowPrecision::Big
        );
        assert_eq!(
            RowPrecision::I128.merge(RowPrecision::Big),
            RowPrecision::Big
        );
        assert_eq!(
            RowPrecision::Big.merge(RowPrecision::Big),
            RowPrecision::Big
        );
    }

    #[test]
    fn test_row_precision_of_rational() {
        assert_eq!(
            RowPrecision::of_rational(&Rational::from(1i64)),
            RowPrecision::I64
        );
        assert_eq!(
            RowPrecision::of_rational(&Rational::new(7, 3)),
            RowPrecision::I64
        );
        let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
        // 2*i64::MAX fits in i128 but not i64, so should be I128 (it's Big variant but fits in i128)
        assert!(matches!(
            RowPrecision::of_rational(&big),
            RowPrecision::I128
        ));
    }

    // --- Per-variable adaptive precision tests (#8185) ---
    #[test]
    fn test_is_all_i64_true() {
        let row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(3i64)), (2, Rational::from(-5i64))],
            Rational::from(7i64),
        );
        assert!(row.is_all_i64());
    }
    #[test]
    fn test_is_all_i64_false_fraction() {
        let row = TableauRow::new_rat(
            0,
            vec![(1, Rational::new(1, 3)), (2, Rational::from(5i64))],
            Rational::from(0i64),
        );
        assert!(!row.is_all_i64());
    }
    #[test]
    fn test_is_all_i64_false_big() {
        let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
        let row = TableauRow::new_rat(
            0,
            vec![(1, big), (2, Rational::from(1i64))],
            Rational::from(0i64),
        );
        assert!(!row.is_all_i64());
    }
    #[test]
    fn test_extract_i64_coeffs_success() {
        let row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(3i64)), (2, Rational::from(-5i64))],
            Rational::from(7i64),
        );
        assert_eq!(
            row.extract_i64_coeffs().expect("ok"),
            vec![(1, 3i64), (2, -5i64)]
        );
    }
    #[test]
    fn test_extract_i64_coeffs_failure() {
        let row = TableauRow::new_rat(0, vec![(1, Rational::new(1, 3))], Rational::from(0i64));
        assert!(row.extract_i64_coeffs().is_none());
    }

    #[test]
    fn test_extract_i64_parts_into_reuses_buffers() {
        let row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(3i64)), (2, Rational::from(-5i64))],
            Rational::from(7i64),
        );
        let mut vars_out = vec![99u32];
        let mut coeffs_out = vec![88i64];

        assert!(row.extract_i64_parts_into(&mut vars_out, &mut coeffs_out));
        assert_eq!(vars_out, vec![1, 2]);
        assert_eq!(coeffs_out, vec![3, -5]);

        vars_out.push(77);
        coeffs_out.push(66);
        assert!(row.extract_i64_parts_into(&mut vars_out, &mut coeffs_out));
        assert_eq!(vars_out, vec![1, 2]);
        assert_eq!(coeffs_out, vec![3, -5]);
    }

    #[test]
    fn test_extract_i64_row_success() {
        let row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(4i64)), (3, Rational::from(-2i64))],
            Rational::from(10i64),
        );
        let (cs, k) = row.extract_i64_row().expect("ok");
        assert_eq!(cs, vec![(1, 4i64), (3, -2i64)]);
        assert_eq!(k, 10);
    }
    #[test]
    fn test_extract_i64_row_failure_constant() {
        let row = TableauRow::new_rat(0, vec![(1, Rational::from(4i64))], Rational::new(1, 3));
        assert!(row.extract_i64_row().is_none());
    }
    #[test]
    fn test_substitute_var_i64_matches_generic() {
        let mut rf = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(3i64)), (3, Rational::from(7i64))],
            Rational::from(10i64),
        );
        let mut rg = rf.clone();
        let sc = vec![
            (1, Rational::from(1i64)),
            (3, Rational::from(-2i64)),
            (4, Rational::from(4i64)),
        ];
        let s = Rational::from(3i64);
        assert!(rf.substitute_var_i64(1, &sc, &s));
        rg.substitute_var(1, &sc, &s);
        assert_eq!(rf.coeffs, rg.coeffs);
    }
    #[test]
    fn test_substitute_var_i64_with_cancellation() {
        let mut row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(5i64)), (3, Rational::from(5i64))],
            Rational::from(0i64),
        );
        assert!(row.substitute_var_i64(
            1,
            &[
                (1, Rational::from(1i64)),
                (3, Rational::from(-1i64)),
                (4, Rational::from(2i64))
            ],
            &Rational::from(5i64)
        ));
        assert_eq!(row.coeffs, vec![(4, Rational::from(10i64))]);
    }
    #[test]
    fn test_substitute_var_i64_empty_subst() {
        let mut row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(3i64)), (2, Rational::from(7i64))],
            Rational::from(0i64),
        );
        assert!(row.substitute_var_i64(1, &[(1, Rational::from(1i64))], &Rational::from(3i64)));
        assert_eq!(row.coeffs, vec![(2, Rational::from(7i64))]);
    }
    #[test]
    fn test_substitute_var_i64_fallback_on_fraction() {
        let mut row = TableauRow::new_rat(
            0,
            vec![(1, Rational::from(3i64)), (2, Rational::from(7i64))],
            Rational::from(0i64),
        );
        assert!(!row.substitute_var_i64(
            1,
            &[(1, Rational::from(1i64)), (3, Rational::from(2i64))],
            &Rational::new(1, 3)
        ));
    }
    #[test]
    fn test_from_i128_small() {
        assert_eq!(Rational::from_i128(42), Rational::Small(42, 1));
    }
    #[test]
    fn test_from_i128_big() {
        let v = i128::from(i64::MAX) * 3;
        let r = Rational::from_i128(v);
        assert!(matches!(r, Rational::Big(_)));
        assert_eq!(r.try_as_i128().expect("fits"), (v, 1));
    }
    #[test]
    fn test_from_i128_negative_big() {
        let v = i128::from(i64::MIN) * 3;
        let r = Rational::from_i128(v);
        assert!(matches!(r, Rational::Big(_)));
        assert_eq!(r.try_as_i128().expect("fits"), (v, 1));
    }
    #[test]
    fn test_from_i128_negative_small() {
        let r = Rational::from_i128(-42);
        assert_eq!(r, Rational::Small(-42, 1));
    }
    #[test]
    fn test_substitute_var_i64_precomputed_matches_generic() {
        // Test that the precomputed path produces the same result as the
        // standard substitute_var_i64_with_col_deltas path.
        let mut row1 = TableauRow::new_rat(
            0,
            vec![
                (1, Rational::from(3i64)),
                (3, Rational::from(7i64)),
                (5, Rational::from(-2i64)),
            ],
            Rational::from(10i64),
        );
        let mut row2 = row1.clone();
        let subst_coeffs = vec![
            (1, Rational::from(1i64)),
            (3, Rational::from(-2i64)),
            (4, Rational::from(4i64)),
        ];
        let scale = Rational::from(3i64);

        // Standard path
        let mut col_added1 = Vec::new();
        let mut col_removed1 = Vec::new();
        assert!(row1.substitute_var_i64_with_col_deltas(
            1,
            &subst_coeffs,
            &scale,
            &mut col_added1,
            &mut col_removed1
        ));

        // Precomputed path: extract i128 terms manually
        let precomputed: Vec<(u32, i128)> = subst_coeffs
            .iter()
            .filter(|(v, _)| *v != 1)
            .map(|(v, c)| (*v, i128::from(c.to_i64().unwrap())))
            .collect();
        let mut col_added2 = Vec::new();
        let mut col_removed2 = Vec::new();
        assert!(row2.substitute_var_i64_precomputed(
            1,
            &precomputed,
            3,
            &mut col_added2,
            &mut col_removed2
        ));

        assert_eq!(row1.coeffs, row2.coeffs, "coefficients must match");
        col_added1.sort_unstable();
        col_added2.sort_unstable();
        col_removed1.sort_unstable();
        col_removed2.sort_unstable();
        assert_eq!(col_added1, col_added2, "col_added must match");
        assert_eq!(col_removed1, col_removed2, "col_removed must match");
    }

    /// Test that substitute_var_work_vec leaves work_vec with correct positions
    /// after substitution that includes removals and additions (#8003 TL87).
    #[test]
    fn test_substitute_var_work_vec_position_tracking() {
        // Row: 0 = 3*v1 + 7*v3 + 5*v5 + 2*v7 + constant
        // Substitute v1 out using: v1 = 1*v2 + (-3)*v3 + 4*v6
        // Scale = 3 (coeff of v1 in this row)
        // Expected:
        //   v1: removed (entering_var)
        //   v2: added (3*1*3 = 3*v2)... wait, let me be precise:
        //   scaled subst coeffs: 3*v2, -9*v3, 12*v6
        //   old: 3*v1, 7*v3, 5*v5, 2*v7
        //   After removing v1: 7*v3, 5*v5, 2*v7
        //   Merging: 3*v2, (7 + -9)*v3 = -2*v3, 5*v5, 12*v6, 2*v7
        //   Result: (v2, 3), (v3, -2), (v5, 5), (v6, 12), (v7, 2)
        let mut row = TableauRow::new_rat(
            0,
            vec![
                (1, Rational::from(3i64)),
                (3, Rational::from(7i64)),
                (5, Rational::from(5i64)),
                (7, Rational::from(2i64)),
            ],
            Rational::from(10i64),
        );
        let subst_coeffs = vec![
            (2, Rational::from(1i64)),
            (3, Rational::from(-3i64)),
            (6, Rational::from(4i64)),
        ];
        let scale = Rational::from(3i64);
        let max_var = 10usize;
        let mut work_vec = vec![-1i32; max_var];
        let mut work_dirty = Vec::new();
        let mut col_added = Vec::new();
        let mut col_removed = Vec::new();

        row.substitute_var_work_vec(
            1,
            &subst_coeffs,
            &scale,
            &mut work_vec,
            &mut work_dirty,
            &mut col_added,
            &mut col_removed,
        );

        // Verify the result coefficients
        assert_eq!(row.coeffs.len(), 5, "should have 5 coefficients");
        assert_eq!(row.coeffs[0], (2, Rational::from(3i64)));
        assert_eq!(row.coeffs[1], (3, Rational::from(-2i64)));
        assert_eq!(row.coeffs[2], (5, Rational::from(5i64)));
        assert_eq!(row.coeffs[3], (6, Rational::from(12i64)));
        assert_eq!(row.coeffs[4], (7, Rational::from(2i64)));

        // Verify work_vec has correct positions for all variables in the result.
        // After Phase 3, work_vec[var] should be the position of var in row.coeffs.
        // Note: work_vec entries are NOT reset by substitute_var_work_vec — the
        // caller is responsible for cleanup using work_dirty.
        for (pos, &(var, _)) in row.coeffs.iter().enumerate() {
            let vi = var as usize;
            assert_eq!(
                work_vec[vi] as usize, pos,
                "work_vec position for var {} should be {} but got {}",
                var, pos, work_vec[vi]
            );
        }

        // Verify col_added and col_removed
        assert!(
            col_removed.contains(&1),
            "entering var should be in col_removed"
        );
        assert!(col_added.contains(&2), "v2 should be in col_added");
        assert!(col_added.contains(&6), "v6 should be in col_added");

        // Clean up work_vec using dirty list
        for &var in &work_dirty {
            work_vec[var as usize] = -1;
        }
        // Verify cleanup
        assert!(
            work_vec.iter().all(|&v| v == -1),
            "work_vec should be fully reset"
        );
    }

    /// Test work_vec position tracking with cancellation (removal path) (#8003 TL87).
    #[test]
    fn test_substitute_var_work_vec_position_tracking_cancellation() {
        // Row: 0 = 5*v1 + 3*v3 + 7*v5
        // Substitute v1 using: v1 = 1*v2 + (-3/5)*v3
        // Scale = 5 (coeff of v1)
        // Scaled: 5*v2, -3*v3
        // After merge: 5*v2, (3 + -3)*v3 = 0*v3 (cancelled!), 7*v5
        // Result: (v2, 5), (v5, 7)
        let mut row = TableauRow::new_rat(
            0,
            vec![
                (1, Rational::from(5i64)),
                (3, Rational::from(3i64)),
                (5, Rational::from(7i64)),
            ],
            Rational::from(0i64),
        );
        let subst_coeffs = vec![(2, Rational::from(1i64)), (3, Rational::new(-3, 5))];
        let scale = Rational::from(5i64);
        let max_var = 8usize;
        let mut work_vec = vec![-1i32; max_var];
        let mut work_dirty = Vec::new();
        let mut col_added = Vec::new();
        let mut col_removed = Vec::new();

        row.substitute_var_work_vec(
            1,
            &subst_coeffs,
            &scale,
            &mut work_vec,
            &mut work_dirty,
            &mut col_added,
            &mut col_removed,
        );

        // Verify result: v3 should be cancelled
        assert_eq!(row.coeffs.len(), 2);
        assert_eq!(row.coeffs[0], (2, Rational::from(5i64)));
        assert_eq!(row.coeffs[1], (5, Rational::from(7i64)));

        // Verify positions in work_vec
        assert_eq!(work_vec[2], 0, "v2 at position 0");
        assert_eq!(work_vec[5], 1, "v5 at position 1");

        // v1 and v3 should be CANCELLED sentinel
        assert_eq!(work_vec[1], i32::MIN, "v1 should be CANCELLED");
        assert_eq!(work_vec[3], i32::MIN, "v3 should be CANCELLED");

        // Verify col_removed includes both v1 (entering) and v3 (cancelled)
        assert!(col_removed.contains(&1), "v1 in col_removed");
        assert!(col_removed.contains(&3), "v3 in col_removed");
        assert!(col_added.contains(&2), "v2 in col_added");

        // Clean up
        for &var in &work_dirty {
            work_vec[var as usize] = -1;
        }
    }
}
