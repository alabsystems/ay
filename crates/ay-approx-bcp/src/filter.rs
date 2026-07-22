// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The approximate BCP filter kernel.
//!
//! [`AssignmentMask`] tracks the OR of `literal_bit(l)` for every
//! literal `l` that is *currently falsified* by the partial assignment
//! — equivalently, every literal whose negation is assigned true on
//! the SAT trail.
//!
//! [`may_be_unit_or_falsified`] returns `true` when the clause cannot
//! be ruled out as either unit or fully falsified.  False positives
//! (returning `true` for a clause that is neither unit nor falsified)
//! are tolerated — they only cost a fallthrough to the exact pass.
//! False negatives (returning `false` for a clause that *is* unit or
//! falsified) would violate BCP soundness and are ruled out by
//! the construction below.  A deterministic randomized test exercises
//! that implication in `crate::tests::filter_never_false_negative`.

use crate::signature::{literal_bit, ClauseSignature};

/// Running OR-bitmap of `literal_bit(l)` for every literal `l` that is
/// currently falsified by the partial assignment.
///
/// Equivalent formulations:
///
/// * "OR of hashes of literals that evaluate to false under the trail."
/// * "OR of `literal_bit(-v)` for every variable `v` assigned true, and
///   `literal_bit(v)` for every variable `v` assigned false."
///
/// Insert every currently falsified literal before using the mask with
/// [`may_be_unit_or_falsified`].  The bitmap is lossy, so it cannot be
/// decremented safely without per-bit reference counts: after a
/// backtrack, rebuild it from the remaining assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct AssignmentMask(u64);

impl AssignmentMask {
    /// Empty mask — no literals falsified yet.
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Construct from a raw `u64`.
    ///
    /// For the filter's soundness guarantee, `bits` must contain the
    /// signature bit of every currently falsified literal.  Prefer
    /// building a mask with [`Self::insert_falsified_literal`] when the
    /// assignment is available.
    #[inline]
    #[must_use]
    pub const fn from_raw(bits: u64) -> Self {
        Self(bits)
    }

    /// Return the underlying bits.
    #[inline]
    #[must_use]
    pub const fn bits(self) -> u64 {
        self.0
    }

    /// Mark a literal as currently falsified.  The caller asserts that
    /// `-l` is on the trail (so literal `l` is false in the model).
    ///
    /// Idempotent on the bitmap: re-inserting the same literal, or a
    /// literal that collides to the same bit, is a no-op.
    #[inline]
    pub fn insert_falsified_literal(&mut self, literal: i32) {
        self.0 |= literal_bit(literal);
    }
}

/// Sound approximate filter: does this clause *possibly* need BCP
/// attention?
///
/// Returns `true` iff the clause might be unit or falsified under the
/// current assignment.  Returns `false` only when the signature proves
/// the clause has ≥ 2 literals that are not currently falsified —
/// i.e., it is definitely *not* unit and definitely *not* falsified.
///
/// # Soundness
///
/// Provided `assignment` contains the signature bit of every currently
/// falsified literal, `popcount(clause_sig & !assignment)` is a lower
/// bound on the number of clause literals not currently falsified.
/// Formally, for every literal `l` in the clause:
///
/// * If `l` is currently falsified, its bit is in `assignment`, so it
///   does *not* contribute to `clause_sig & !assignment`.
/// * If `l` is true or unassigned, its bit *may* be in `assignment` due
///   to a collision with some other falsified literal — in which case
///   the popcount under-counts, making the filter more conservative
///   (it will flag more clauses as "maybe unit").
///
/// Therefore:
///
/// ```text
///     popcount(clause_sig & !assignment) ≤ (# literals not currently false)
/// ```
///
/// So `popcount ≥ 2` ⟹ "at least 2 literals are not falsified" ⟹ the
/// clause is neither unit nor falsified and can be safely skipped by
/// BCP.  The contrapositive — the actual soundness direction used here
/// — is that any unit or falsified clause has popcount ≤ 1 and is
/// flagged by the filter.  See `crate::tests::filter_never_false_negative`
/// for a deterministic randomized property test.
#[inline]
#[must_use]
pub fn may_be_unit_or_falsified(clause_sig: ClauseSignature, assignment: AssignmentMask) -> bool {
    let surviving = clause_sig.bits() & !assignment.bits();
    surviving.count_ones() <= 1
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn empty_assignment_flags_every_clause() {
        // With no assignments the filter cannot rule out any clause as
        // "definitely satisfied."  Every clause signature has ≥ 1 bits
        // set (non-empty clauses) and `!assignment == !0`, so the AND
        // preserves them — but then popcount must be ≤ 1 to flag.
        //
        // This test uses a 1-literal clause to guarantee popcount = 1.
        let sig = ClauseSignature::from_literals(&[42]);
        assert!(may_be_unit_or_falsified(sig, AssignmentMask::empty()));
    }

    #[test]
    fn two_literal_unassigned_clause_is_skipped() {
        let sig = ClauseSignature::from_literals(&[1, 2]);
        // Two literals, different bits (verified elsewhere): popcount = 2 → skip.
        assert!(!may_be_unit_or_falsified(sig, AssignmentMask::empty()));
    }

    #[test]
    fn clause_with_all_literals_falsified_is_flagged() {
        let lits = [1i32, 2, 3];
        let sig = ClauseSignature::from_literals(&lits);
        let mut mask = AssignmentMask::empty();
        for &l in &lits {
            mask.insert_falsified_literal(l);
        }
        assert!(may_be_unit_or_falsified(sig, mask));
    }

    #[test]
    fn unit_clause_is_flagged() {
        let lits = [1i32, 2, 3];
        let sig = ClauseSignature::from_literals(&lits);
        let mut mask = AssignmentMask::empty();
        // Falsify all but literal 3.
        mask.insert_falsified_literal(1);
        mask.insert_falsified_literal(2);
        assert!(may_be_unit_or_falsified(sig, mask));
    }
}
