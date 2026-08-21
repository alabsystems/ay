// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    pub(super) fn prepare_clause_replacement_lrat(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        extra_lrat_hints: &[u64],
    ) -> Option<(bool, ClauseRef, u64, Vec<Literal>)> {
        // CaDiCaL clause.cpp: replacement only during inprocessing at level 0.
        // Soundness-critical: replacing at higher levels corrupts solver state (#4560).
        assert_eq!(
            self.decision_level, 0,
            "BUG: replace_clause_checked at decision level {}",
            self.decision_level,
        );
        // Replacement must produce a non-growing clause. Empty replacements
        // are valid for strengthening-derived contradictions and are handled
        // below by marking UNSAT.
        // No duplicate variables in the replacement (CaDiCaL subsume.cpp pattern).
        // Soundness-critical: duplicates break 2WL invariant (#4560).
        debug_assert!(
            {
                let mut vars: Vec<u32> = new_lits.iter().map(|l| l.variable().0).collect();
                vars.sort_unstable();
                vars.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: replace_clause_checked: duplicate variables in new_lits for clause {clause_idx}",
        );
        // All literal variables must be in range.
        // Soundness-critical: out-of-range causes silent corruption (#4560).
        // MUST be assert!() not debug_assert!() — see #5141.
        assert!(
            new_lits
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: replace_clause_checked: literal variable out of range (num_vars={})",
            self.num_vars,
        );
        // Husk guard (husk adjudication #3/#4): garbage-kept / pending-garbage
        // clauses are logically deleted. `arena.replace()` clears the
        // GARBAGE|PENDING bits and re-attaches watches + BVE occ entries,
        // which would REVIVE a deliberately deleted clause. Skipping is always
        // sound: the husk stays dead and is reaped normally. Mirrors the sink
        // guard in replace_clause_core (mutate_replace.rs).
        if !self.arena.is_active(clause_idx) || self.arena.is_garbage_any(clause_idx) {
            return None;
        }
        // #A2b search-time proof bookkeeping: an LRAT clause replacement
        // rebuilds hint chains and mutates the clause trace (add + delete of
        // a full clause). Charge deterministic units — literal/hint counts,
        // never wall time — against the SAME budget as level-0 unit
        // materialization, so inprocessing-LRAT-heavy runs (QF_ALIA
        // pointer-safe-5 default mode, 2026-07-12 reprofile) can reach
        // exhaustion and degrade to no-proof search at the next safe point
        // (`run_incremental_inprocessing` entry). Synthesized-default
        // certificates only: explicit `--proof`/`:produce-proofs` runs have
        // no budget, so this is a no-op there.
        if self.cold.lrat_enabled {
            // Byte-denominated deterministic units, matching the trace-add
            // charge (a replacement clones the old literals, builds a hint
            // chain, and records an add + a delete).
            let units = (self.arena.len_of(clause_idx) as u64 + new_lits.len() as u64) * 4
                + (extra_lrat_hints.len() as u64) * 8
                + 32;
            let _ = self.charge_proof_bookkeeping(units);
        }
        let was_irredundant = !self.arena.is_learned(clause_idx);
        // New clause must not be longer than original (CaDiCaL subsume.cpp:84).
        // Soundness-critical: growing a clause overwrites adjacent arena memory (#4560).
        // O(1) check — must be assert!() because arena overwrite is silent corruption.
        assert!(
            new_lits.len() <= self.arena.len_of(clause_idx),
            "BUG: replace_clause_checked: new_lits ({}) longer than original ({}) at clause {clause_idx}",
            new_lits.len(),
            self.arena.len_of(clause_idx),
        );
        let clause_ref = ClauseRef(clause_idx as u32);
        let old_clause_id = self.clause_id(clause_ref);
        let old_lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();
        Some((was_irredundant, clause_ref, old_clause_id, old_lits))
    }
}
