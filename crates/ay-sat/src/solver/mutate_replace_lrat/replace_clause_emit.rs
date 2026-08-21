// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    pub(super) fn record_replacement_lrat_mapping(
        &mut self,
        clause_idx: usize,
        reordered: &[Literal],
        proof_hints: &[u64],
        replacement_clause_id: Option<u64>,
    ) {
        // Keep clause-ID mapping synchronized with LRAT writer IDs.
        if let Some(new_clause_id) = replacement_clause_id {
            debug_assert!(
                new_clause_id != 0,
                "BUG: LRAT sentinel 0 leaked into clause ID update (#4434)"
            );
            debug_assert!(
                clause_idx < self.cold.clause_ids.len(),
                "BUG: clause_idx {} missing LRAT ID slot (clause_ids len={})",
                clause_idx,
                self.cold.clause_ids.len()
            );
            self.cold.clause_ids[clause_idx] = new_clause_id;
            // Do NOT advance next_clause_id here (#5239). Replacement
            // clauses get their IDs from the proof writer. Derived clauses
            // sync next_clause_id from the writer in add_learned_clause.

            // Propagate replacement clause + resolution hints to clause_trace
            // (#4124). The proof_manager already has the LRAT step; the
            // clause_trace needs a matching entry for SMT proof reconstruction.
            if let Some(ref mut trace) = self.cold.clause_trace {
                trace.add_clause_with_hints(
                    new_clause_id,
                    reordered.to_vec(),
                    false,
                    proof_hints.to_vec(),
                );
            }
        }
    }

    pub(super) fn emit_replacement_clause_lrat(
        &mut self,
        clause_idx: usize,
        reordered: &[Literal],
        proof_hints: &[u64],
        proof_kind: ProofAddKind,
        old_clause_id: u64,
        old_lits: &[Literal],
    ) -> Option<Option<u64>> {
        let mut replacement_clause_id = None;
        // Forward check + proof emit: add clause, then delete old (#4564).
        if let Ok(new_id) = self.proof_emit_add(&reordered, &proof_hints, proof_kind) {
            // Guard: LRAT returns Ok(0) as a no-op sentinel after I/O
            // failure (CaDiCaL-style). Do NOT update clause ID state
            // with this sentinel -- it would corrupt clause_ids and
            // next_clause_id. See #4434.
            if self.cold.lrat_enabled && new_id != 0 {
                replacement_clause_id = Some(new_id);
            }
        }
        // #trace-divergence: an in-place replacement whose proof row could
        // not be recorded MUST NOT mutate the arena. In the writer-less
        // clause-trace lane `proof_emit_add` has no id source and returns 0,
        // so the block below would skip the trace entry while the live
        // clause is strengthened anyway — every later chain citing this
        // clause id then replays against the STALE trace snapshot and the
        // derived row is not RUP of the trace (measured: blocksworld
        // `bmc_7` row 61370-class rejections). Fail closed instead: keep
        // the original clause. Solving strength is unchanged outside the
        // trace lane (a writer that returns a real id is unaffected).
        if self.cold.lrat_enabled
            && replacement_clause_id.is_none()
            && self.cold.clause_trace.is_some()
        {
            return None;
        }
        // Fix #6270: Before deleting old_clause_id, check if any variable's
        // unit_proof_id references it. If so, re-derive the unit using the
        // replacement clause ID, preventing stale LRAT hint references.
        if self.cold.lrat_enabled && old_clause_id != 0 {
            for &lit in old_lits {
                let vi = lit.variable().index();
                if vi < self.unit_proof_id.len()
                    && self.unit_proof_id[vi] == old_clause_id
                    && self.unit_proof_sign.get(vi).copied().unwrap_or(0) == lit.sign_i8()
                    && self.var_data[vi].level == 0
                {
                    // The old clause is about to be deleted. Re-derive the unit
                    // from the replacement clause (which has already been added).
                    if let Some(new_id) = replacement_clause_id {
                        let unit_id = self
                            .proof_emit_add(&[lit], &[new_id], ProofAddKind::Derived)
                            .unwrap_or(0);
                        if unit_id != 0 {
                            self.record_unit_proof_id_for_lit(lit, unit_id);
                        }
                    }
                }
            }
        }
        // Derive unit proof IDs for variables whose reason clause is being
        // replaced BEFORE deleting the old clause. The derivation uses
        // old_clause_id as a hint; the old ID must still be in known_lrat_ids.
        // Moving the delete before this call would cause "LRAT hint references
        // unknown/deleted clause" when the derivation tries to reference the
        // just-deleted old clause (#8093).
        self.clear_level0_reasons_removed_by_replacement(
            clause_idx,
            &old_lits,
            &reordered,
            old_clause_id,
        );

        // Delete old clause unconditionally (CaDiCaL: always emit delete
        // for replaced clause regardless of add outcome).
        let _ = self.proof_emit_delete(&old_lits, old_clause_id);
        Some(replacement_clause_id)
    }
}
