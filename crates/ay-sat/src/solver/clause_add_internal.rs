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

impl Solver {
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
            let marks = &mut self.cold.factor_candidate_marks[var_idx];
            if (*marks & bit) == 0 {
                *marks |= bit;
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
            self.cold.factor_candidate_marks[var_idx] &= !bit;
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
        // Most learned clauses are RUP-derived, but theory lemmas are solver-
        // learned axioms from the SMT layer and must be checked as originals.

        // Validate all literals have in-bounds variables (#113, #3330).
        // MUST be assert!() not debug_assert!() — release builds silently
        // corrupt the clause DB if this check is removed (#5141).
        assert!(
            literals
                .iter()
                .all(|lit| lit.variable().index() < self.num_vars),
            "BUG: Clause contains out-of-bounds literal. num_vars={}",
            self.num_vars,
        );
        self.check_solution_on_added_clause(literals, forward_check_derived);

        // Forward DRUP check: verify derived clauses are RUP implied (#4291).
        // In LRAT mode, skip forward DRUP verification for derived clauses.
        // The LRAT proof stream provides its own hint chains verified by the
        // LRAT checker; the forward DRUP checker lacks level-0 assignment
        // context and would false-positive on unit learned clauses (#7108).
        if let Some(ref mut checker) = self.cold.forward_checker {
            if forward_check_derived && !self.cold.lrat_enabled {
                checker.add_derived(literals);
            } else {
                checker.add_original(literals);
            }
        }
        // Clear pending_forward_check: this clause has been forward-checked
        // by the direct checker dispatch above (#4564 contract).
        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }

        // Register original (non-derived) clauses in the proof manager.
        // Uses forward_check_derived (not learned) because derived-irredundant
        // clauses (HBR, BVE resolvents) are derived in proof provenance but
        // irredundant in clause-db semantics (#4648).
        if !forward_check_derived {
            if let Some(ref mut manager) = self.proof_manager {
                manager.register_original_clause(literals);
            }
        }

        let idx = self.arena.add(literals, learned);
        // Stamp learned clauses with the current user-scope depth so pop()
        // can delete them when the enclosing scope is popped (Z3 PR #9221).
        // Ported from Z3 PR #9221: `sat_solver::mk_nary_clause` writes
        // `r->set_scope_lim(m_user_scope_literals.size())` for redundant
        // clauses. AY's equivalent scope counter is `scope_selectors.len()`.
        if learned {
            let depth = self.cold.scope_selectors.len();
            // Saturate at 3 to fit the 2-bit header field; the pop-side
            // sweep bails out when new_depth >= 3 because the stamp cannot
            // distinguish level-N from level-N+1 beyond that.
            let depth_u16 = (depth.min(u16::MAX as usize)) as u16;
            self.arena.set_scope_lim(idx, depth_u16);
        }
        // #unguarded-tvalid-lemmas STAGE 0 (replay counter): birth-solve
        // stamp, recorded beside the scope_lim stamp. `incremental_solve_count`
        // is incremented by `reset_search_state` at solve entry, so clauses
        // born DURING solve N carry stamp N and conflict analysis counts a
        // conflict as "from a prior solve's clause" iff stamp < current count.
        // Clauses added BETWEEN solves carry the previous solve's epoch and
        // therefore also read as prior-solve births — semantically "created
        // before the current solve's search began", which is the intended
        // reading for the cross-solve carryover diagnostic. Gated on
        // count > 0 so single-shot sessions never allocate the side vec
        // (a missing entry reads as epoch 0).
        if self.cold.incremental_solve_count > 0 {
            if idx >= self.cold.clause_birth_solve.len() {
                self.cold.clause_birth_solve.resize(idx + 1, 0);
            }
            self.cold.clause_birth_solve[idx] =
                self.cold.incremental_solve_count.min(u64::from(u32::MAX)) as u32;
        }
        if let Some(ref mut gc_occ) = self.gc_occ {
            // Verify gc_occ can accommodate all literals before adding (#8078).
            for &lit in literals {
                debug_assert!(
                    lit.index() < gc_occ.capacity(),
                    "BUG: add_clause_db_checked: literal {} (var={}) exceeds gc_occ capacity {} \
                     (num_vars={}). gc_occ was not grown for this literal.",
                    lit.raw(),
                    lit.variable().index(),
                    gc_occ.capacity(),
                    self.num_vars,
                );
            }
            gc_occ.add_clause(idx, literals);
        }
        if !learned || literals.len() == 2 {
            self.mark_factor_candidates_dirty_clause(literals);
        }

        // Mark variables in the new clause as subsume-dirty (CaDiCaL flags.subsume).
        // This enables incremental subsumption: only clauses containing recently-
        // added variables are scheduled in the next subsumption round.
        //
        // For learned clauses, dirty marking is DEFERRED to after LBD is set,
        // gated by `mark_subsume_dirty_if_kept()`. CaDiCaL `new_clause` at
        // clause.cpp:140 only calls `mark_added(c)` for `likely_to_be_kept_clause(c)`.
        // Without this gate, tier3 (high-glue) learned clauses that will be deleted
        // at the next reduce_db pollute the dirty set, causing AY to schedule
        // low-quality subsumption candidates that exhaust the effort budget before
        // reaching useful work (#7393).
        if !learned {
            for &lit in literals {
                let v = lit.variable().index();
                if v < self.subsume_dirty.len() {
                    self.subsume_dirty[v] = true;
                }
            }
        }

        // NOTE: The original clause registration above (lines 1687-1691)
        // already handled ProofManager registration. This duplicate block
        // was a merge artifact — removed to prevent double-registration.

        // Assign clause ID unconditionally (#8069: Phase 2a).
        // Original (non-derived) clauses use next_original_clause_id to stay
        // aligned with the pre-registered LRAT IDs (1..=num_originals).
        // Derived clauses use next_clause_id which tracks the proof writer's
        // monotonic ID space (including deletions).
        let clause_id = if !forward_check_derived {
            // Original clause: use its pre-registered LRAT position.
            let id = self.cold.next_original_clause_id;
            self.cold.next_original_clause_id += 1;
            // Keep next_clause_id at least past original IDs so derived
            // clauses don't collide with original IDs.
            if self.cold.next_clause_id <= id {
                self.cold.next_clause_id = id + 1;
            }
            id
        } else {
            let id = self.cold.next_clause_id;
            self.cold.next_clause_id += 1;
            id
        };
        if idx >= self.cold.clause_ids.len() {
            self.cold.clause_ids.resize(idx + 1, 0);
        }
        self.cold.clause_ids[idx] = clause_id;
        if learned && self.cold.bcp_learned_1963_identity_profile {
            if idx >= self.cold.bcp_learned_clause_birth_conflicts.len() {
                self.cold
                    .bcp_learned_clause_birth_conflicts
                    .resize(idx + 1, self.num_conflicts);
            }
            self.cold.bcp_learned_clause_birth_conflicts[idx] = self.num_conflicts;
        }

        // Record to clause trace and proof manager only when LRAT is enabled.
        // The clause ID assignment above is unconditional, but hint construction
        // and proof emission remain gated on lrat_enabled (#8072).
        if self.cold.lrat_enabled {
            if let Some(ref mut manager) = self.proof_manager {
                manager.register_clause_id(clause_id);
            }

            // #A2b search-time proof bookkeeping: every clause-trace add
            // clones the literal + hint vectors purely for certificate
            // reconstruction (--no-proof does none of this). Charge
            // deterministic units — the bytes recorded into the trace, the
            // documented #A2b bookkeeping meter (`take_clause_trace`) —
            // against the shared budget so trace-heavy searches (QF_ALIA
            // pointer-safe-5 default mode) can exhaust it and degrade at the
            // next safe point. No budget (explicit proof modes) => no-op.
            if self.cold.clause_trace.is_some() {
                let units = (literals.len() as u64) * 4 + (resolution_hints.len() as u64) * 8 + 16;
                let _ = self.charge_proof_bookkeeping(units);
            }
            if let Some(ref mut trace) = self.cold.clause_trace {
                trace.add_clause_with_hints(
                    clause_id,
                    literals.to_vec(),
                    !forward_check_derived,
                    resolution_hints.to_vec(),
                );
            }
        }

        // Clause provenance tracking (#8321): tag new clause by origin.
        // Original (non-derived) clauses are ProblemEncoding; derived clauses
        // are tagged Learned here as a default. Callers that know the precise
        // origin (TheoryLemma, Inprocessing) override via a direct tag() call.
        if forward_check_derived {
            self.provenance
                .tag(idx, crate::clause_provenance::ClauseProvenance::Learned);
        } else {
            self.provenance.tag(
                idx,
                crate::clause_provenance::ClauseProvenance::ProblemEncoding,
            );
        }

        // SAT diagnostic trace: clause_add event (Wave 2, #4211)
        if let Some(ref writer) = self.cold.diagnostic_trace {
            let dimacs_lits: Vec<i64> = literals.iter().map(|l| i64::from(l.to_dimacs())).collect();
            let clause_id = if idx < self.cold.clause_ids.len() {
                self.cold.clause_ids[idx]
            } else {
                idx as u64
            };
            // Use forward_check_derived for provenance (not learned) because
            // derived-irredundant clauses are derived in proof origin (#4648).
            // Derive ClauseKind from (forward_check_derived, diagnostic_pass)
            // for specific attribution. BVE resolvents, vivification
            // strengthened clauses, and theory lemmas get distinct event kinds (#4172).
            let kind = if forward_check_derived {
                crate::diagnostic_trace::ClauseKind::Learned
            } else {
                match self.cold.diagnostic_pass {
                    DiagnosticPass::Input => crate::diagnostic_trace::ClauseKind::Original,
                    DiagnosticPass::BVE => crate::diagnostic_trace::ClauseKind::Resolvent,
                    DiagnosticPass::Vivify | DiagnosticPass::Subsume => {
                        crate::diagnostic_trace::ClauseKind::Strengthened
                    }
                    // Theory lemmas reach add_clause_db via add_theory_lemma
                    // without setting a diagnostic pass, so pass==None + learned
                    // uniquely identifies them.
                    DiagnosticPass::None => crate::diagnostic_trace::ClauseKind::Theory,
                    _ => crate::diagnostic_trace::ClauseKind::Learned,
                }
            };
            writer.emit_clause_add(
                clause_id,
                &dimacs_lits,
                self.cold.diagnostic_pass,
                kind,
                resolution_hints,
            );
        }

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
