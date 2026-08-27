// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Ackermann congruence closure that makes symbolic read indices exact.
//!
//! With a literal index the cell key is the numeric address, so two reads at the
//! same address are literally the same variable and array functionality is free.
//! A symbolic index has no such luxury: `(select A i)` and `(select A j)` become
//! two independent constants, and nothing stops a model from setting `i = j`
//! while `r_i != r_j` — an "array" that is not a function, i.e. a false `sat`.
//!
//! The axioms restore it. See the parent module docs for the two-direction
//! equisatisfiability argument, and
//! `verification/abvfp-symbolic-read-flatten/` for the machine-checked
//! obligations (three solvers) including the mutant that shows the backward
//! direction genuinely breaks without them.

use super::{FlatCell, FlattenAbstain};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TermStore};

/// Cap on congruence pairs emitted for ONE array. The closure is exact only if
/// every pair is asserted, so exceeding this abstains rather than truncating —
/// see [`FlattenAbstain::TooManyReadPairs`]. At the cap one array contributes
/// ~2k axioms, which the bit-blaster absorbs; a formula needing more is past the
/// point where this pass is the right tool.
pub(super) const MAX_CONGRUENCE_PAIRS: usize = 2_048;

/// Ackermann congruence axioms: `(=> (= i j) (= r_i r_j))` for every pair of
/// distinct cells on the SAME array.
///
/// Two LITERAL cells are skipped: distinct literal keys have distinct numeric
/// values, so `(= i j)` is `false` and the implication is a tautology. Every
/// other pair — symbolic/symbolic and symbolic/literal — gets an axiom.
///
/// Pairs are never emitted ACROSS arrays. Two different arrays share nothing
/// even at the same index, and an axiom spanning them would force unrelated
/// arrays to agree — unsound in the opposite direction, deleting real models.
///
/// Returns [`FlattenAbstain::TooManyReadPairs`] rather than a truncated list.
/// A PREFIX of these axioms is not a weaker-but-sound encoding: the omitted
/// pairs are exactly the ones left free to disagree, so truncation is a
/// wrong-`sat` generator. All or nothing.
pub(super) fn congruence_axioms(
    terms: &mut TermStore,
    cells: &[FlatCell],
) -> Result<Vec<TermId>, FlattenAbstain> {
    // Group cell slots by array so the pairing stays within one array.
    let mut by_array: HashMap<TermId, Vec<usize>> = HashMap::default();
    for (slot, cell) in cells.iter().enumerate() {
        by_array.entry(cell.array).or_default().push(slot);
    }

    // Budget check BEFORE building anything, so an overrun costs no terms.
    for slots in by_array.values() {
        let n = slots.len();
        let symbolic = slots
            .iter()
            .filter(|&&s| cells[s].index_value.is_none())
            .count();
        // Pairs needing an axiom: every pair with at least one symbolic side,
        // i.e. all pairs minus the literal/literal ones.
        let lit = n - symbolic;
        let pairs = n * (n - 1) / 2 - lit * lit.saturating_sub(1) / 2;
        if pairs > MAX_CONGRUENCE_PAIRS {
            return Err(FlattenAbstain::TooManyReadPairs);
        }
    }

    // Deterministic order: walk `cells` in discovery order, not the hash map.
    let mut arrays: Vec<TermId> = Vec::new();
    for cell in cells {
        if !arrays.contains(&cell.array) {
            arrays.push(cell.array);
        }
    }

    let mut axioms = Vec::new();
    for array in arrays {
        let slots = &by_array[&array];
        for (a, &p) in slots.iter().enumerate() {
            for &q in &slots[a + 1..] {
                if cells[p].index_value.is_some() && cells[q].index_value.is_some() {
                    continue;
                }
                let idx_eq = terms.mk_eq(cells[p].index_term, cells[q].index_term);
                let val_eq = terms.mk_eq(cells[p].fresh, cells[q].fresh);
                axioms.push(terms.mk_implies(idx_eq, val_eq));
            }
        }
    }
    Ok(axioms)
}
