// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV concat-equality normalization preprocessing pass
//!
//! Normalizes bitvector equalities involving `concat` into equalities over
//! extracts. This enables downstream variable substitution to learn component
//! assignments (e.g., learning `a = #xAB` from `(= (concat a b) #xABCD)`).
//!
//! # Problem
//!
//! When `(= (concat high low) other)` is asserted, the bitblaster correctly
//! encodes this, but variable substitution cannot extract the implicit
//! equalities `high = extract(other)[high bits]` and `low = extract(other)[low bits]`.
//!
//! # Algorithm (ported from Bitwuzla)
//!
//! For `(= (concat high low) other)` where `|other| = m` and `|low| = k`:
//!
//! Rewrite to:
//! ```smt2
//! (and
//!   (= high ((_ extract (m-1) k) other))
//!   (= low  ((_ extract (k-1) 0) other)))
//! ```
//!
//! This is the "AY-friendly form" from the design document - we extract
//! from `other` rather than from the concat, avoiding the need for a
//! separate `extract(concat(...))` simplifier.
//!
//! # Reference
//!
//! - the development design notes
//! - `reference/bitwuzla/src/preprocess/pass/variable_substitution.cpp:369`
//! - Issue #1802, supports #1708/#1782

use super::PreprocessingPass;
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Preprocessing pass that normalizes BV equalities involving concat.
pub(crate) struct NormalizeEqBvConcat {
    /// Track terms we've already processed to avoid reprocessing
    processed: HashSet<TermId>,
}

impl NormalizeEqBvConcat {
    /// Create a new NormalizeEqBvConcat pass.
    pub(crate) fn new() -> Self {
        Self {
            processed: HashSet::default(),
        }
    }

    /// Check if a term is a concat operation.
    fn is_concat(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::App(sym, args) if sym.name() == "concat" && args.len() == 2)
    }

    /// Get the high and low operands of a concat term.
    /// Returns None if the term is not a concat.
    fn get_concat_operands(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
        match terms.get(term) {
            TermData::App(sym, args) if sym.name() == "concat" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Visited-set deduplication: the term store is a hash-consed DAG; a naive
    /// recursive walk enumerates every tree PATH (exponential in sharing depth —
    /// the DAG→tree pathology). Skipping a revisited node is sound: `any`
    /// short-circuits on the first `true`, so a node the walk continues past
    /// evaluated `false`, which is fixed for this (term table, needle) pair.
    fn contains_term(terms: &TermStore, root: TermId, needle: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        Self::contains_term_inner(terms, root, needle, &mut visited)
    }

    fn contains_term_inner(
        terms: &TermStore,
        root: TermId,
        needle: TermId,
        visited: &mut HashSet<TermId>,
    ) -> bool {
        if root == needle {
            return true;
        }
        if !visited.insert(root) {
            return false;
        }
        terms
            .children(root)
            .iter()
            .copied()
            .any(|child| Self::contains_term_inner(terms, child, needle, visited))
    }

    fn is_zero_bitvec_const(terms: &TermStore, term: TermId) -> bool {
        matches!(
            terms.get(term),
            TermData::Const(Constant::BitVec { value, .. }) if value == &num_bigint::BigInt::from(0u8)
        )
    }

    fn is_extract(terms: &TermStore, term: TermId) -> bool {
        matches!(
            terms.get(term),
            TermData::App(sym, args) if sym.name() == "extract" && args.len() == 1
        )
    }

    fn is_shift_like_concat_definition(terms: &TermStore, concat_term: TermId) -> bool {
        let Some((high, low)) = Self::get_concat_operands(terms, concat_term) else {
            return false;
        };
        (Self::is_extract(terms, high) && Self::is_zero_bitvec_const(terms, low))
            || (Self::is_zero_bitvec_const(terms, high) && Self::is_extract(terms, low))
    }

    /// Try to normalize a BV equality involving concat.
    ///
    /// For `(= (concat high low) other)` or `(= other (concat high low))`:
    /// Returns Some((high_eq, low_eq)) where:
    /// - high_eq = (= high (extract (m-1) k other))
    /// - low_eq  = (= low  (extract (k-1) 0 other))
    ///
    /// Returns None if the term is not a suitable equality.
    fn try_normalize(terms: &mut TermStore, assertion: TermId) -> Option<(TermId, TermId)> {
        // Match (= lhs rhs) where both sides are bitvectors
        let (lhs, rhs) = match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => (args[0], args[1]),
            _ => return None,
        };

        // Check that we're dealing with bitvectors
        let lhs_sort = terms.sort(lhs).clone();
        let rhs_sort = terms.sort(rhs).clone();
        let total_width = match (&lhs_sort, &rhs_sort) {
            (Sort::BitVec(bv1), Sort::BitVec(bv2)) if bv1.width == bv2.width => bv1.width,
            _ => return None,
        };

        // Determine which side is concat and which is other
        let (high, low, other) = if let Some((h, l)) = Self::get_concat_operands(terms, lhs) {
            // LHS is concat, RHS is other
            (h, l, rhs)
        } else if let Some((h, l)) = Self::get_concat_operands(terms, rhs) {
            // RHS is concat, LHS is other
            (h, l, lhs)
        } else {
            // Neither side is concat
            return None;
        };

        // Don't normalize if other side is also a concat (could cause loops)
        if Self::is_concat(terms, other) {
            return None;
        }

        // Power-of-two `bvmul` and constant shifts are canonicalized into
        // `concat(extract(x), 0)` or `concat(0, extract(x))`. Splitting a
        // variable definition such as `y = concat(extract(x), 0)` into bit
        // equalities prevents the variable-substitution pass from replacing
        // `y`, leaving downstream selector muxes in a much larger form. Let
        // those compact shift-like definitions substitute instead.
        if matches!(terms.get(other), TermData::Var(_, _))
            && Self::is_shift_like_concat_definition(
                terms,
                if Self::is_concat(terms, lhs) {
                    lhs
                } else {
                    rhs
                },
            )
            && !Self::contains_term(
                terms,
                if Self::is_concat(terms, lhs) {
                    lhs
                } else {
                    rhs
                },
                other,
            )
        {
            return None;
        }

        // Get widths
        let low_width = match terms.sort(low) {
            Sort::BitVec(bv) => bv.width,
            _ => return None,
        };
        let high_width = match terms.sort(high) {
            Sort::BitVec(bv) => bv.width,
            _ => return None,
        };

        // Sanity check: widths must add up
        if high_width + low_width != total_width {
            return None;
        }

        // Guard against zero-width operands (would cause underflow in extract indices)
        if low_width == 0 || high_width == 0 {
            return None;
        }

        // Build extracts from `other`:
        // high_extract = (extract (total_width-1) low_width other)
        // low_extract  = (extract (low_width-1) 0 other)
        let high_extract = terms.mk_bvextract(total_width - 1, low_width, other);
        let low_extract = terms.mk_bvextract(low_width - 1, 0, other);

        // Build equalities
        let high_eq = terms.mk_eq(high, high_extract);
        let low_eq = terms.mk_eq(low, low_extract);

        let debug = crate::theory_debug_flags::debug_concat_eq();
        if debug {
            safe_eprintln!(
                "[concat_eq] Normalized: concat({:?}, {:?}) = {:?}",
                high,
                low,
                other
            );
            safe_eprintln!(
                "[concat_eq]   -> high {:?} = extract({}, {}, {:?})",
                high,
                total_width - 1,
                low_width,
                other
            );
            safe_eprintln!(
                "[concat_eq]   -> low  {:?} = extract({}, 0, {:?})",
                low,
                low_width - 1,
                other
            );
        }

        Some((high_eq, low_eq))
    }
}

impl Default for NormalizeEqBvConcat {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for NormalizeEqBvConcat {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let mut modified = false;
        let mut new_assertions = Vec::new();

        for &assertion in assertions.iter() {
            // Skip already processed terms
            if self.processed.contains(&assertion) {
                new_assertions.push(assertion);
                continue;
            }

            if let Some((high_eq, low_eq)) = Self::try_normalize(terms, assertion) {
                // Replace the original equality with AND of the two new equalities
                // FlattenAnd will split this into separate assertions
                let combined = terms.mk_and(vec![high_eq, low_eq]);
                new_assertions.push(combined);
                modified = true;
                self.processed.insert(assertion);
            } else {
                new_assertions.push(assertion);
            }
        }

        if modified {
            *assertions = new_assertions;
        }

        modified
    }

    fn reset(&mut self) {
        // Don't reset processed set - we don't want to reprocess the same
        // terms across fixed-point iterations (they'd just generate the
        // same split again)
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
