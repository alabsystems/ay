// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Internal clause DB operations, factor candidate marking, and solution
//! witness checking.
//!
//! Split from `clause_add.rs` for file-size compliance (#5142).
//! Contains `add_clause_db`, `add_clause_db_checked`, factor candidate
//! marking, and solution witness validation helpers.

use super::*;

mod admitted;
mod publication;

impl Solver {
    /// Allocate an ID for an original/axiomatic clause without colliding with
    /// derived clauses.
    ///
    /// An LRAT writer may reserve `1..=N` for input clauses up front. Those
    /// canonical IDs must be honored even when inprocessing emits a derived
    /// step before the last input arrives. Once that reservation is exhausted
    /// (or when clause tracing has no writer/reservation), originals and
    /// derived clauses share `next_clause_id` so a late theory axiom cannot
    /// reuse a live derived ID.
    pub(super) fn allocate_original_clause_id(&mut self) -> u64 {
        let candidate = self.cold.next_original_clause_id;
        let reserved_end = self
            .proof_manager
            .as_ref()
            .map_or(0, ProofManager::reserved_original_clause_ids);

        if candidate <= reserved_end {
            self.cold.next_original_clause_id += 1;
            if self.cold.next_clause_id <= candidate {
                self.cold.next_clause_id = candidate + 1;
            }
            self.record_issued_original_clause_id(candidate);
            candidate
        } else {
            let id = self.cold.next_clause_id.max(candidate);
            self.cold.next_clause_id = id + 1;
            self.cold.next_original_clause_id = id + 1;
            self.record_issued_original_clause_id(id);
            id
        }
    }

    /// Record that `id` was issued to an original (non-derived) clause.
    ///
    /// Maintains `issued_original_clause_id_max` and the per-ID original
    /// marker. Called only at true original mint sites: both branches of
    /// [`Self::allocate_original_clause_id`] (every original clause add
    /// routes through it) and the debug-only scope-selector axiom
    /// registration in `incremental.rs`, which occupies an original-space
    /// LRAT ID. Derived mints must never call this — the whole point is
    /// that the derived IDs the late-original allocator jumps over stay
    /// unmarked, so streaming-support classification can tell them apart.
    pub(super) fn record_issued_original_clause_id(&mut self, id: u64) {
        if id == 0 {
            return;
        }
        if self.cold.issued_original_clause_id_max < id {
            self.cold.issued_original_clause_id_max = id;
        }
        let idx = (id - 1) as usize;
        if self.cold.original_clause_id_bits.len() <= idx {
            self.cold.original_clause_id_bits.resize(idx + 1, false);
        }
        self.cold.original_clause_id_bits[idx] = true;
    }

    /// Whether `id` was issued to an original (non-derived) clause.
    ///
    /// Range membership (`id <= num_originals`) is NOT sufficient: since
    /// b93692341 the late-original allocator jumps past live derived IDs,
    /// so derived IDs can sit between original IDs. Streaming-support
    /// classification must use this per-ID bit on top of the range bound.
    #[inline]
    pub(super) fn is_original_clause_id(&self, id: u64) -> bool {
        id != 0
            && self
                .cold
                .original_clause_id_bits
                .get((id - 1) as usize)
                .copied()
                .unwrap_or(false)
    }

    #[inline]
    pub(super) fn add_clause_db(&mut self, literals: &[Literal], learned: bool) -> usize {
        self.add_clause_db_checked(literals, learned, learned, &[])
    }

    #[inline]
    fn factor_mark_bit(lit: Literal) -> u8 {
        if lit.is_positive() {
            1
        } else {
            2
        }
    }

    #[inline]
    pub(super) fn mark_factor_candidates_dirty_clause(&mut self, literals: &[Literal]) {
        let mut newly_marked = 0_u64;
        for &lit in literals {
            let var_idx = lit.variable().index();
            if var_idx >= self.cold.factor_candidate_marks.len() {
                continue;
            }
            let bit = Self::factor_mark_bit(lit);
            let old = self.cold.factor_candidate_marks[var_idx];
            if (old & bit) == 0 {
                if let Some((_, writes)) = self.cold.factor_marks_undo.as_mut() {
                    writes.push((var_idx as u32, old));
                }
                self.cold.factor_candidate_marks[var_idx] = old | bit;
                newly_marked = newly_marked.saturating_add(1);
            }
        }
        if newly_marked != 0 {
            self.cold.factor_marked_epoch =
                self.cold.factor_marked_epoch.saturating_add(newly_marked);
        }
    }

    #[inline]
    pub(super) fn consume_factor_candidate_marks(&mut self, consumed_candidates: &[Literal]) {
        for &lit in consumed_candidates {
            let var_idx = lit.variable().index();
            if var_idx >= self.cold.factor_candidate_marks.len() {
                continue;
            }
            let bit = Self::factor_mark_bit(lit);
            let old = self.cold.factor_candidate_marks[var_idx];
            if (old & bit) != 0 {
                if let Some((_, writes)) = self.cold.factor_marks_undo.as_mut() {
                    writes.push((var_idx as u32, old));
                }
                self.cold.factor_candidate_marks[var_idx] = old & !bit;
            }
        }
    }

    /// Add a clause to the database with explicit forward-checker classification.
    ///
    /// `forward_check_derived`: when true, the forward checker verifies the
    /// clause is RUP-implied (derived). When false, the clause is treated as
    /// an axiom (original formula). Most learned clauses are derived, but
    /// theory lemmas are learned-yet-axiomatic (`learned=true`,
    /// `forward_check_derived=false`). Conversely, some inprocessing-derived
    /// irredundant clauses (BVE resolvents, HTR resolvents, factorization
    /// products) are `learned=false` but still derived.
    ///
    /// `resolution_hints`: clause IDs used to derive this clause. Passed
    /// atomically to the clause trace so hints are never missing (#4435).
    #[inline]
    pub(super) fn add_clause_db_checked(
        &mut self,
        literals: &[Literal],
        learned: bool,
        forward_check_derived: bool,
        resolution_hints: &[u64],
    ) -> usize {
        self.add_clause_db_admitted::<admitted::Ordinary>(
            literals,
            learned,
            forward_check_derived,
            resolution_hints,
        )
    }

    /// One publication kernel: counted callers reserve every selected effect
    /// and commit their exact trace row before entering this callback-free body.
    fn add_clause_db_admitted<P: admitted::Trace>(
        &mut self,
        literals: &[Literal],
        learned: bool,
        forward_check_derived: bool,
        resolution_hints: &[u64],
    ) -> usize {
        let registered_original_id = self.prepare_clause_db_check(literals, forward_check_derived);
        let idx = self.store_clause_db(literals, learned);
        // Shadow L0-rebuild epoch (#l0-rebuild-epoch): a new
        // irredundant clause (BVE/HTR/factorize product, bound clause,
        // initial load) is a destructive-class mutation. The initial
        // load bumps before the first rebuild snapshot, which reads
        // fail-closed until that snapshot exists.
        if !learned {
            if forward_check_derived {
                self.cold.derived_irredundant_adds_since_rebuild = self
                    .cold
                    .derived_irredundant_adds_since_rebuild
                    .saturating_add(1);
            }
            self.note_irredundant_mutation();
        }
        let clause_id = self.assign_clause_db_identity(
            idx,
            learned,
            forward_check_derived,
            registered_original_id,
        );
        P::publish(
            self,
            clause_id,
            literals,
            forward_check_derived,
            resolution_hints,
            registered_original_id,
        );
        self.finish_clause_db(idx, literals, forward_check_derived, resolution_hints);
        idx
    }

    /// Check a newly added derived clause against the configured witness.
    ///
    /// Returns immediately if witness checking is disabled, if the clause is
    /// non-derived, or if any literal has an unknown witness value.
    #[inline]
    fn check_solution_on_added_clause(&self, clause: &[Literal], derived: bool) {
        if !derived {
            return;
        }
        let Some(witness) = self.cold.solution_witness.as_ref() else {
            return;
        };

        debug_assert_eq!(
            witness.len(),
            self.num_vars,
            "BUG: witness width {} != num_vars {}",
            witness.len(),
            self.num_vars
        );

        let mut has_unknown = false;
        for &lit in clause {
            let var_idx = lit.variable().index();
            match witness[var_idx] {
                Some(value) if value == lit.is_positive() => return,
                Some(_) => {}
                None => has_unknown = true,
            }
        }

        assert!(
            has_unknown,
            "BUG: derived clause falsified by configured witness: {:?}",
            clause.iter().map(|lit| lit.to_dimacs()).collect::<Vec<_>>()
        );
    }

    /// Online witness check for replaced/shrunken clauses (CaDiCaL parity:
    /// `check_solution_on_shrunken_clause`).
    ///
    /// Unlike `check_solution_on_added_clause`, this checks ALL clauses (not
    /// just learned), because inprocessing strengthening of irredundant clauses
    /// must also preserve the witness.
    #[inline]
    pub(super) fn check_solution_on_replaced_clause(&self, clause: &[Literal]) {
        let Some(witness) = self.cold.solution_witness.as_ref() else {
            return;
        };

        debug_assert_eq!(
            witness.len(),
            self.num_vars,
            "BUG: witness width {} != num_vars {}",
            witness.len(),
            self.num_vars
        );

        let mut has_unknown = false;
        for &lit in clause {
            let var_idx = lit.variable().index();
            match witness[var_idx] {
                Some(value) if value == lit.is_positive() => return,
                Some(_) => {}
                None => has_unknown = true,
            }
        }

        assert!(
            has_unknown,
            "BUG: replaced/shrunken clause falsified by configured witness: {:?}",
            clause.iter().map(|lit| lit.to_dimacs()).collect::<Vec<_>>()
        );
    }
}
