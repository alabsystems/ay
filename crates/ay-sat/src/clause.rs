// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause tier management
//!
//! Implements tier-based clause classification:
//! - CORE (LBD <= 2): "Glue" clauses, never deleted
//! - TIER1 (LBD <= 6): Important clauses, kept if recently used
//! - TIER2 (LBD > 6): Less important, deleted based on activity

use crate::literal::{Literal, Variable};

/// Clause tier based on LBD (Literal Block Distance)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ClauseTier {
    /// Core/Glue clauses (LBD <= 2) - never deleted
    Core,
    /// Tier 1 clauses (2 < LBD <= 6) - kept if recently used
    Tier1,
    /// Tier 2 clauses (LBD > 6) - deleted based on activity
    Tier2,
}

/// LBD threshold for core/glue clauses
pub(crate) const CORE_LBD: u32 = 2;
/// LBD threshold for tier 1 clauses
pub(crate) const TIER1_LBD: u32 = 6;

/// 64-bit clause signature used as a bloom-style filter in BVE.
///
/// The lower 32 bits are buckets for positive literals, the upper 32 bits are
/// buckets for negative literals. Variable hashing deliberately over-approximates
/// membership: collisions are allowed and only introduce false positives.
pub(crate) type ClauseSignature = u64;

const CLAUSE_SIGNATURE_BUCKETS_PER_POLARITY: u32 = 32;
const CLAUSE_SIGNATURE_POLARITY_SHIFT: u32 = 32;

#[inline]
fn clause_signature_bucket(var: Variable) -> u32 {
    // Multiplicative hashing keeps nearby variable IDs from collapsing into
    // the same small bucket range.
    let mixed = u64::from(var.id()).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    (mixed >> 59) as u32
}

/// Compute the signature bit contributed by a single literal.
#[inline]
pub(crate) fn clause_signature_bit(lit: Literal) -> ClauseSignature {
    let bucket = clause_signature_bucket(lit.variable())
        + if lit.is_positive() {
            0
        } else {
            CLAUSE_SIGNATURE_BUCKETS_PER_POLARITY
        };
    1_u64 << bucket
}

/// Compute a 64-bit signature for a clause's current literals.
#[inline]
pub(crate) fn compute_clause_signature(lits: &[Literal]) -> ClauseSignature {
    let mut signature = 0;
    for &lit in lits {
        signature |= clause_signature_bit(lit);
    }
    signature
}

/// Returns true if two clause signatures may contain opposite-polarity matches.
///
/// This is used as a sound negative filter in BVE: `false` means the filtered
/// clauses definitely cannot resolve to a tautology. `true` means "maybe" and
/// requires the normal literal-by-literal check.
#[inline]
pub(crate) fn clause_signatures_may_resolve_tautologically(
    lhs: ClauseSignature,
    rhs: ClauseSignature,
) -> bool {
    lhs & rhs.rotate_left(CLAUSE_SIGNATURE_POLARITY_SHIFT) != 0
}

/// Returns true if the first clause signature may subsume the second.
///
/// This is a sound negative filter: `false` means the first clause definitely
/// does not subsume the second clause. `true` means "maybe" and requires the
/// full literal-by-literal subsumption check because hash collisions are
/// allowed.
#[inline]
pub(crate) fn clause_signature_may_subsume(
    subsuming: ClauseSignature,
    subsumed: ClauseSignature,
) -> bool {
    subsuming & !subsumed == 0
}

/// Returns true if all variables in the first clause signature may be present
/// in the second clause (ignoring polarity).
///
/// Sound negative filter for both subsumption AND self-subsumption
/// (strengthening): `false` means the first clause definitely cannot subsume
/// or strengthen the second clause, because some variable in the first clause
/// is not present in the second at any polarity. `true` means "maybe" and
/// requires the full literal-by-literal check.
///
/// This is strictly weaker than `clause_signature_may_subsume` (which also
/// checks polarity) but covers the strengthening case where exactly one
/// literal has opposite polarity.
#[inline]
pub(crate) fn clause_signature_vars_subset(
    subsuming: ClauseSignature,
    subsumed: ClauseSignature,
) -> bool {
    // Project both signatures to variable-only by OR-ing the positive and
    // negative halves together. Lower 32 bits = positive, upper 32 = negative.
    let sub_vars = (subsuming as u32) | ((subsuming >> 32) as u32);
    let cand_vars = (subsumed as u32) | ((subsumed >> 32) as u32);
    sub_vars & !cand_vars == 0
}
