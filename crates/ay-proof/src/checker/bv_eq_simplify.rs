// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The bounded BV fragment of Clean's `eq_simplify` dialect.
//!
//! Addition is a group operation in Z/(2^w). Thus `(x+a = x+b)` is
//! equivalent to `(a = b)`, including wraparound. Here `a` and `b` are
//! canonical literals and the common `x` is the identical opaque term. No
//! alias, source premise, polynomial normalization or SAT answer is inferred.
//! The native rule is narrower than general equality simplification. Its wire
//! spelling requires Clean's explicit `eq_simplify_bv_offsets` capability.

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_traits::{Signed, ToPrimitive};

use super::ProofCheckError;

/// Two outer orientations, four addend placements, and at most two 128-bit
/// limbs per literal. This reserve covers every slot/sort read and comparison
/// before any inspection, including a failed shape. The matcher allocates
/// nothing; the byte reserve also covers its bounded diagnostic on rejection.
pub(crate) const WORK: usize = 512;
pub(crate) const BYTES: usize = 2_048;

pub(crate) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    argument_count: usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    if !progress(WORK, BYTES) {
        return Err(ProofCheckError::ResourceLimit);
    }
    if premise_count == 0 && argument_count == 0 && recognizes(terms, clause) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidBooleanRule {
        step,
        rule: "eq_simplify".to_string(),
        reason: "not a premise-free canonical BV literal or common-addend simplification"
            .to_string(),
    })
}

/// The same finite judgement used by the exporter. Recognition confers no
/// authority: strict replay still debits [`WORK`] and [`BYTES`] and validates
/// the entire proof and its source assumptions.
pub(crate) fn recognizes(terms: &TermStore, clause: &[TermId]) -> bool {
    let [root] = clause else { return false };
    let Some((left, right)) = bool_equality(terms, *root) else {
        return false;
    };
    orientation(terms, left, right) || orientation(terms, right, left)
}

fn bool_equality(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
        return None;
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    terms.entry_stamp(left)?;
    terms.entry_stamp(right)?;
    (op == "="
        && terms.sort(term) == &Sort::Bool
        && terms.sort(left) == &Sort::Bool
        && terms.sort(right) == &Sort::Bool)
        .then_some((left, right))
}

fn bv_equality(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, u32)> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
        return None;
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    terms.entry_stamp(left)?;
    terms.entry_stamp(right)?;
    let width = terms.sort(left).bitvec_width()?;
    (op == "="
        && terms.sort(term) == &Sort::Bool
        && (1..=128).contains(&width)
        && terms.sort(right) == terms.sort(left))
    .then_some((left, right, width))
}

fn literal(terms: &TermStore, term: TermId, width: u32) -> Option<u128> {
    terms.entry_stamp(term)?;
    let TermData::Const(Constant::BitVec {
        value,
        width: literal_width,
    }) = terms.get(term)
    else {
        return None;
    };
    if *literal_width != width
        || terms.sort(term).bitvec_width() != Some(width)
        || value.is_negative()
        || value.bits() > u64::from(width)
    {
        return None;
    }
    value.to_u128()
}

fn addends(terms: &TermStore, term: TermId, width: u32) -> Option<[TermId; 2]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
        return None;
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    terms.entry_stamp(left)?;
    terms.entry_stamp(right)?;
    (op == "bvadd"
        && [term, left, right]
            .into_iter()
            .all(|part| terms.sort(part).bitvec_width() == Some(width)))
    .then_some([left, right])
}

fn target(terms: &TermStore, term: TermId, first: u128, second: u128, width: u32) -> bool {
    // All target terms were entry-checked by `bool_equality`.
    match terms.get(term) {
        TermData::Const(Constant::Bool(result)) => *result == (first == second),
        _ => bv_equality(terms, term).is_some_and(|(left, right, target_width)| {
            target_width == width
                && literal(terms, left, width) == Some(first)
                && literal(terms, right, width) == Some(second)
        }),
    }
}

fn orientation(terms: &TermStore, source: TermId, result: TermId) -> bool {
    let Some((left, right, width)) = bv_equality(terms, source) else {
        return false;
    };
    if let (Some(first), Some(second)) = (literal(terms, left, width), literal(terms, right, width))
    {
        // A literal equality reduces to its Boolean truth, not to an arbitrary
        // equal expression. Cancellation below may retain the literal test.
        return matches!(terms.get(result), TermData::Const(Constant::Bool(value))
            if *value == (first == second));
    }
    let (Some(left), Some(right)) = (addends(terms, left, width), addends(terms, right, width))
    else {
        return false;
    };
    for common_left in 0..2 {
        for common_right in 0..2 {
            if left[common_left] != right[common_right] {
                continue;
            }
            let (Some(first), Some(second)) = (
                literal(terms, left[1 - common_left], width),
                literal(terms, right[1 - common_right], width),
            ) else {
                continue;
            };
            if target(terms, result, first, second, width) {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests;
