// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reuse fully defined FC index-equality guards within one CNF generation.
//!
//! The caller keeps the BvSolver, arena, and final literal offset unchanged.
//! An exact unordered index-TermId pair therefore names the same Boolean
//! equality across arrays. Normalized keys or merely equal-looking bit slices
//! are NOT cache identities. ROW guards are not recorded or reused here.

use super::{offset_bv_bit, ArrayAxiomResult, BvSolver, HashMap, TermId};
use ay_core::CnfClause;

pub(super) struct IndexEqualityGuards {
    completed: HashMap<(TermId, TermId), i32>,
    max_entries: usize,
}

impl IndexEqualityGuards {
    /// Use the existing global FC pair allowance, without preallocating it.
    /// Every production call has already consumed one pair from that budget;
    /// this additional retention bound also makes an uncached fallback safe.
    /// It bounds entries, not exact allocator bytes or total generation work.
    pub(super) fn new(max_entries: usize) -> Self {
        Self {
            completed: HashMap::default(),
            max_entries,
        }
    }

    /// Called only AFTER the unchanged pair budget, bit-width/missing-bit and
    /// known/normalized-distinct admission checks. Hits do not exempt another
    /// pair from those checks or from its own scalar/nested value consequent.
    pub(super) fn get_or_emit(
        &mut self,
        pair: (TermId, TermId),
        bits: (&[i32], &[i32]),
        bv: &BvSolver<'_>,
        bv_offset: u32,
        next_var: &mut u32,
        result: &mut ArrayAxiomResult,
    ) -> i32 {
        let key = if pair.0 <= pair.1 {
            pair
        } else {
            (pair.1, pair.0)
        };
        if let Some(&guard) = self.completed.get(&key) {
            return guard;
        }
        // Canonicalize ONLY the key: the first emission keeps its original
        // index orientation, literal order and variable allocation sequence.
        let guard = emit_index_equality(bits, bv, bv_offset, next_var, result);
        if self.completed.len() < self.max_entries {
            // Publish only after every XOR and summary-definition clause is
            // present. A full cache emits the same guard without retaining it.
            self.completed.insert(key, guard);
        }
        guard
    }
}

fn emit_index_equality(
    (left, right): (&[i32], &[i32]),
    bv: &BvSolver<'_>,
    bv_offset: u32,
    next_var: &mut u32,
    result: &mut ArrayAxiomResult,
) -> i32 {
    let mut differences = Vec::with_capacity(left.len());
    for (&left_bit, &right_bit) in left.iter().zip(right) {
        if let (Some(left_value), Some(right_value)) = (
            bv.bit_constant_value(left_bit),
            bv.bit_constant_value(right_bit),
        ) {
            if left_value == right_value {
                continue;
            }
        }
        let left_lit = offset_bv_bit(left_bit, bv_offset);
        let right_lit = offset_bv_bit(right_bit, bv_offset);
        let difference = *next_var as i32;
        *next_var += 1;
        differences.push(difference);
        // difference <=> (left_bit XOR right_bit), in legacy clause order.
        result
            .clauses
            .push(CnfClause::new(vec![-difference, left_lit, right_lit]));
        result
            .clauses
            .push(CnfClause::new(vec![-difference, -left_lit, -right_lit]));
        result
            .clauses
            .push(CnfClause::new(vec![-left_lit, right_lit, difference]));
        result
            .clauses
            .push(CnfClause::new(vec![left_lit, -right_lit, difference]));
    }
    let guard = *next_var as i32;
    *next_var += 1;
    // guard <=> !OR(differences). For distinct source terms whose bits are
    // all known-equal, this MUST still emit the true summary unit [guard].
    for &difference in &differences {
        result
            .clauses
            .push(CnfClause::new(vec![-guard, -difference]));
    }
    let mut definition = differences;
    definition.push(guard);
    result.clauses.push(CnfClause::new(definition));
    guard
}

#[cfg(test)]
mod tests;
