// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepayment for the existing indexes and move-only proof splice, when the
//! structural-array channel causes L1 to enter those paths.

use super::*;

pub(in crate::executor::proof_propagated_rewrite) fn prepay_indexes(
    roots: usize,
    records: &PropagationRecords,
    progress: &dyn Fn(usize, usize) -> bool,
) -> Option<()> {
    let items = roots
        .checked_add(records.entries.len())?
        .checked_add(records.rewrites.len())?;
    // Three hash tables of scalar IDs: allow bucket/control metadata, load
    // factor and power-of-two growth before any table is constructed.
    progress(items, items.checked_mul(128)?).then_some(())
}

pub(in crate::executor::proof_propagated_rewrite) fn prepay_splice(
    proof: &Proof,
    planned: &splice::PlannedPropagationChains,
    progress: &dyn Fn(usize, usize) -> bool,
) -> Option<()> {
    prepay_chain(proof, progress)?;
    prepay_chain(&planned.shared_chain, progress)?;
    for (chain, _) in planned.solo.values() {
        prepay_chain(chain, progress)?;
    }
    progress(0, 0).then_some(())
}

fn prepay_chain(proof: &Proof, progress: &dyn Fn(usize, usize) -> bool) -> Option<()> {
    for step in &proof.steps {
        // The splicer MOVES arbitrary clauses, rule arguments, names and
        // certificates, rather than cloning their payloads. Its allocations
        // are the rebuilt step vector, scalar ID maps and remapped premises.
        let premises = match step {
            ProofStep::Step { premises, .. } => premises.len(),
            ProofStep::Resolution { .. } => 2,
            ProofStep::Anchor { .. } => 1,
            _ => 0,
        };
        let bytes = std::mem::size_of::<ProofStep>()
            .checked_mul(2)?
            .checked_add(4 * std::mem::size_of::<ProofId>())?
            .checked_add(premises.checked_mul(std::mem::size_of::<ProofId>())?)?;
        if !progress(premises.checked_add(1)?, bytes) {
            return None;
        }
    }
    // Existing name entries are discarded by the existing move-only splice.
    progress(proof.named_steps.len(), 0).then_some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn index_storage_checks_overflow_and_prepays_empty_rewrite_unit_channel() {
        let records = PropagationRecords::default();
        assert!(prepay_indexes(usize::MAX, &records, &|_, _| true).is_none());
        let bytes = Cell::new(0);
        assert!(prepay_indexes(2, &records, &|_, cost| {
            bytes.set(cost);
            true
        })
        .is_some());
        assert_eq!(bytes.get(), 256);
        assert!(prepay_indexes(2, &records, &|_, _| false).is_none());
    }

    #[test]
    fn splice_preflight_charges_shared_solo_and_original_without_mutating_them() {
        let original = Proof::from_steps(vec![ProofStep::Assume(TermId(0))]);
        let planned = splice::PlannedPropagationChains {
            shared_chain: original.clone(),
            shared_conclusions: [(0, ProofId(0))].into_iter().collect(),
            solo: [(1, (original.clone(), ProofId(0)))].into_iter().collect(),
        };
        let calls = Cell::new(0);
        assert!(prepay_splice(&original, &planned, &|_, _| {
            calls.set(calls.get() + 1);
            calls.get() < 4
        })
        .is_none());
        assert_eq!(calls.get(), 4);
        let work = Cell::new(0);
        assert!(prepay_splice(&original, &planned, &|delta, _| {
            work.set(work.get() + delta);
            true
        })
        .is_some());
        assert_eq!(work.get(), 3);
        assert_eq!(original.steps.len(), 1);
        assert_eq!(planned.shared_chain.steps.len(), 1);
        assert_eq!(planned.solo.len(), 1);
    }
}
