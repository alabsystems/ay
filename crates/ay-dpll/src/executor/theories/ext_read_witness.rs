// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The shared read witness of the datatype-array read-over-equality pass.
//!
//! `dt_array_equality_read_congruence_axioms` instantiates `(= X Y) =>
//! (select X w) = (select Y w)` at one symbolic index `w` per index sort, so a
//! clash at an index nothing reads still surfaces
//! (#dt-array-extensionality-witness). The instance is valid at every ground
//! index, so `w` needs no freshness: it is minted once per public query and
//! every later round and retry of that query reuses it.
//!
//! A fresh `w` per call made every round of the combined DT+X deepening loop
//! (`solve_with_dt_axioms`) a renamed copy of the last one, and the reads of
//! each discarded `w` stayed in the store, where the next round's scans gave
//! them axioms of their own (+8 a round on the ay-chc nested-vector replay
//! obligation). The loop's exit for a round that would solve the previous
//! round's assertion window again therefore never fired, and the loop ran to
//! its depth ceiling: 62 rounds and about 10 s of that replay on a slow core.

use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::{ArrayExtWitnessCache, ArrayExtWitnessIdentity};

impl ArrayExtWitnessCache {
    /// The shared read witness of `index_sort` in the current public query,
    /// minted on first use. An entry a store rollback invalidated is minted
    /// again.
    pub(crate) fn shared_read_witness(
        &mut self,
        terms: &mut TermStore,
        index_sort: Sort,
    ) -> TermId {
        if let Some(existing) = self.shared_read.get(&index_sort) {
            if existing.still_matches(terms) {
                return existing.term;
            }
        }
        let term = terms.mk_fresh_var("dt_ext_witness", index_sort.clone());
        if let TermData::Var(name, var_id) = terms.get(term) {
            let identity = ArrayExtWitnessIdentity {
                term,
                name: name.clone(),
                var_id: *var_id,
                sort: index_sort.clone(),
            };
            self.shared_read.insert(index_sort, identity);
        }
        term
    }
}

#[cfg(test)]
mod tests {
    use ay_core::term::TermData;
    use ay_core::{Sort, TermStore};

    use super::ArrayExtWitnessCache;

    #[test]
    fn one_witness_per_index_sort_within_a_public_query() {
        let mut terms = TermStore::new();
        let mut cache = ArrayExtWitnessCache::default();
        let bv64 = Sort::bitvec(64);
        let first = cache.shared_read_witness(&mut terms, bv64.clone());
        assert_eq!(cache.shared_read_witness(&mut terms, bv64.clone()), first);
        assert_eq!(terms.sort(first), &bv64);
        let int = cache.shared_read_witness(&mut terms, Sort::Int);
        assert_ne!(int, first);
        assert_eq!(terms.sort(int), &Sort::Int);
        // A difference witness is a separate identity: the read witness never
        // becomes provenance for an extensionality clause.
        assert!(!cache.is_active_witness(&terms, first));
    }

    #[test]
    fn a_new_public_query_or_a_rollback_mints_a_new_witness() {
        let mut terms = TermStore::new();
        let mut cache = ArrayExtWitnessCache::default();
        let first = cache.shared_read_witness(&mut terms, Sort::Int);
        cache.begin_public_solve(&terms);
        let kept = cache.shared_read_witness(&mut terms, Sort::Int);
        assert_ne!(kept, first);

        // A speculative lane mints the Real witness, then the store unwinds.
        let checkpoint = terms.rollback_checkpoint();
        let rolled_back = cache.shared_read_witness(&mut terms, Sort::Real);
        terms.rollback_to(checkpoint);
        assert!(rolled_back.index() >= terms.len());
        let replacement = cache.shared_read_witness(&mut terms, Sort::Real);
        assert!(replacement.index() < terms.len());
        assert!(matches!(
            terms.get(replacement),
            TermData::Var(name, _) if name.starts_with("dt_ext_witness")
        ));
        assert_eq!(terms.sort(replacement), &Sort::Real);
        // The witness minted before the checkpoint survives the rollback.
        assert_eq!(cache.shared_read_witness(&mut terms, Sort::Int), kept);
    }
}
