// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    pub(in crate::solver) fn replace_clause_impl(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        extra_lrat_hints: &[u64],
        explicit_only: bool,
        proof_kind: ProofAddKind,
    ) -> ReplaceResult {
        let Some((was_irredundant, clause_ref, old_clause_id, old_lits)) =
            self.prepare_clause_replacement_lrat(clause_idx, new_lits, extra_lrat_hints)
        else {
            return ReplaceResult::Skipped;
        };

        if new_lits.is_empty() {
            return self.replace_with_empty_clause_lrat(
                clause_idx,
                new_lits,
                extra_lrat_hints,
                explicit_only,
                old_clause_id,
                &old_lits,
            );
        }

        // CaDiCaL has zero reason-clause protection during level-0 inprocessing.
        // At level 0, replacement is in-place (same arena slot) so the ClauseRef
        // remains valid as a reason reference (#5237, R1:1113).

        // Reorder literals for optimal watch placement (#3812).
        // Without this, after strengthening/BVE the first two literals may both
        // be falsified at low levels, causing BCP to miss unit propagations.
        let mut reordered = new_lits.to_vec();
        let watched =
            self.prepare_watched_literals(&mut reordered, WatchOrderPolicy::AssignmentScore);

        let Some(proof_hints) = self.build_replacement_lrat_hints(
            &old_lits,
            &reordered,
            extra_lrat_hints,
            explicit_only,
            old_clause_id,
        ) else {
            return ReplaceResult::Skipped;
        };

        if self.cold.lrat_enabled {
            self.materialize_level0_unit_proofs();
            if !self.lrat_replacement_level0_reason_units_ready(
                clause_idx,
                &old_lits,
                &reordered,
                old_clause_id,
            ) {
                return ReplaceResult::Skipped;
            }
        }

        let Some(replacement_clause_id) = self.emit_replacement_clause_lrat(
            clause_idx,
            &reordered,
            &proof_hints,
            proof_kind,
            old_clause_id,
            &old_lits,
        ) else {
            return ReplaceResult::Skipped;
        };

        self.record_replacement_lrat_mapping(
            clause_idx,
            &reordered,
            &proof_hints,
            replacement_clause_id,
        );

        self.finish_lrat_clause_replacement(
            clause_ref,
            clause_idx,
            old_clause_id,
            &reordered,
            watched,
            was_irredundant,
            replacement_clause_id,
        )
    }
}
