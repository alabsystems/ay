// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Terminal proof-chain construction for level-0 conflicts.

use super::super::*;
use crate::kani_compat::det_hash_set_new;
use crate::solver::solve::theory_callback::TheoryCallback;

mod terminal;

impl Solver {
    /// Record the BCP resolution chain for a level-0 conflict (#4176).
    pub(in crate::solver) fn record_level0_conflict_chain(&mut self, conflict_ref: ClauseRef) {
        debug_assert_eq!(
            self.decision_level, 0,
            "record_level0_conflict_chain called at non-zero decision level"
        );
        debug_assert!(
            {
                let conflict_lits = self.arena.literals(conflict_ref.0 as usize);
                conflict_lits.iter().all(|lit| self.lit_val(*lit) < 0)
            },
            "BUG: level-0 conflict clause {} has non-false literal",
            conflict_ref.0
        );

        // The bounded ResolutionDag route reconstructs the terminal proof
        // postsolve, before any of the unbounded legacy allocations below.
        // The one level-0 conflict with a fixed-size chain, a unit falsified
        // by a file-visible unit, is emitted here instead, the way
        // `add_original_empty_clause` emits an original empty clause, so the
        // postsolve walk finds an authenticated terminal and allocates nothing.
        if self.cold.backward_proof_limits.is_some() {
            if !self.emit_complementary_unit_terminal(conflict_ref) {
                self.mark_empty_clause_deferred_for_bounded_proof();
            }
            return;
        }
        if !self.has_live_clause_trace() && !self.cold.lrat_enabled {
            // Proof-free posture (`--competition`, `--no-proof`): no chain to
            // record, only the refutation and the scope depth it was derived
            // at, which `pop()` uses to decide whether it survives.
            self.raise_empty_clause_flag();
            return;
        }
        if self.cold.lrat_enabled {
            self.record_lrat_level0_conflict_chain(conflict_ref);
        } else {
            let chain = self.collect_resolution_chain(conflict_ref, None, &det_hash_set_new());
            self.mark_empty_clause_with_hints_and_trace(&chain, chain.clone());
        }
    }

    /// Emit the terminal chain of a unit clause falsified by a file-visible
    /// level-0 unit: two producer-prevalidated hints, `[unit, conflict]`, in
    /// the order the bounded walk would replay them. Returns `false`, leaving
    /// the conflict to the metered postsolve walk, for every other shape and
    /// for a failed emission (the bounded output is then already poisoned).
    fn emit_complementary_unit_terminal(&mut self, conflict_ref: ClauseRef) -> bool {
        let Some(deadline) = self
            .cold
            .backward_proof_limits
            .as_ref()
            .map(|limits| limits.deadline)
        else {
            return false;
        };
        let &[lit] = self.arena.literals(conflict_ref.0 as usize) else {
            return false;
        };
        let conflict_id = self.clause_id(conflict_ref);
        if !self.lrat_hint_id_visible(conflict_id) {
            return false;
        }
        let Some(unit_id) = self.visible_unit_proof_id_for_lit(lit.negated()) else {
            return false;
        };
        self.mark_empty_clause_with_bounded_prevalidated_hints(&[unit_id, conflict_id], deadline)
            .is_ok()
    }

    fn record_lrat_level0_conflict_chain(&mut self, conflict_ref: ClauseRef) {
        match self.record_lrat_level0_conflict_admitted(
            conflict_ref,
            &conflict_analysis_minimize_lrat::root::Ordinary,
        ) {
            Ok(()) => (),
            Err(never) => match never {},
        }
    }

    /// Root (level-0) assignments that carry neither a reason clause nor a
    /// unit proof ID, so no derivation exists for them. A level-0 lazy theory
    /// reason the theory could not reconstruct later is demoted to exactly
    /// this shape (`materialize_lazy_reasons_for_level_range`). Diagnostic
    /// only; `tracing` evaluates it only when the debug event is enabled.
    pub(in crate::solver) fn unjustified_root_assignment_count(&self) -> usize {
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        self.trail[..level0_end]
            .iter()
            .filter(|&&lit| {
                let vd = self.var_data[lit.variable().index()];
                let clause_justified = is_clause_reason(vd.reason) && !vd.is_lazy_theory_reason();
                !clause_justified
                    && self.visible_unit_proof_id_for_lit(lit).is_none()
                    && self.level0_var_proof_id(lit.variable().index()).is_none()
            })
            .count()
    }

    /// Record a level-0 theory model conflict, then declare UNSAT
    /// (#cert-level0-theory-conflict).
    ///
    /// The `TheoryModelCheck::Conflict` arm of the unified CDCL loop used to
    /// DISCARD the theory's conflict clause and call `declare_unsat()`
    /// directly. `finalize_unsat_proof` then stamps `trace.mark_empty()`
    /// (`solve/finalize_unsat.rs`) onto a clause trace holding NO derivation,
    /// producing a trace that CLAIMS UNSAT and cannot back it — the
    /// certificate consumer's `EmptyMarkerWithoutDerivedEmpty` decline.
    ///
    /// Recording the T-lemma confers NO authority. It lands as an
    /// `is_original` trace entry — the same shape a successful mint already
    /// has — and the exact fragment independently re-derives authority for
    /// EVERY original entry (`sat_proof_manager/exact_fragment/build_steps.rs`
    /// gates a theory annotation on `clauses_equivalent` plus
    /// `rebind_theory_annotation`) and never trusts the flag. A T-lemma with
    /// no registered proof therefore still declines, now naming the real
    /// reason: `UnauthenticatedOriginalClause`.
    ///
    /// When there is nothing to record — the theory asserted UNSAT with no
    /// explanation at all, or the lemma is not a usable level-0 conflict
    /// (`add_theory_lemma_scoped` may attach an unassigned scope selector, and
    /// `add_theory_conflict_lemma` then leaves no terminal chain) — the trace
    /// keeps today's imprecise decline. MEASURED: stamping
    /// `mark_proof_work_exhausted()` to make that decline honest is NOT safe.
    /// The stamp is consumed by `sat_proof_manager` ("skipping best-effort
    /// default certificate"), which abandons SAT proof reconstruction
    /// outright; the SMT proof then degenerates to a `TheoryLemma { Generic }`
    /// that mandatory strict certification rejects, turning published UNSAT
    /// verdicts into `unknown`. Nothing mints from that shape either way, so
    /// the imprecise decline is strictly better than losing correct answers.
    pub(in crate::solver) fn declare_level0_theory_conflict_unsat<C: TheoryCallback>(
        &mut self,
        callback: &mut C,
        clause: Vec<Literal>,
    ) -> SatResult {
        if !clause.is_empty() {
            // #8467: materialize before the lemma is added (lazy table
            // indexes are not arena offsets).
            //
            // `add_theory_conflict_lemma` does the whole job: it writes the
            // `is_original` trace entry and, on detecting the all-false lemma
            // at level 0, emits the terminal chain itself. Driving
            // `record_level0_conflict_chain` afterwards appends a DUPLICATE
            // empty clause and trades this decline for
            // `EntryAfterTerminalEmpty` — measured on every reproducing
            // instance.
            callback.materialize_lazy_reasons(self);
            self.add_theory_conflict_lemma(clause);
        }
        self.declare_unsat()
    }

    fn materialize_level0_conflict_clause_id(
        &mut self,
        conflict_ref: ClauseRef,
        conflict_lits: &[Literal],
    ) -> u64 {
        let mut conflict_id = self.cached_conflict_clause_id(conflict_ref);
        if conflict_id == 0 && self.proof_manager.is_some() {
            let trusted_id = self
                .proof_emit_add(conflict_lits, &[], ProofAddKind::TrustedTransform)
                .unwrap_or(0);
            if trusted_id != 0 {
                let conflict_idx = conflict_ref.0 as usize;
                if conflict_idx < self.cold.clause_ids.len() {
                    self.cold.clause_ids[conflict_idx] = trusted_id;
                }
                conflict_id = trusted_id;
            }
        }
        conflict_id
    }

    fn level0_conflict_proof_chain_complete(
        &self,
        conflict_lits: &[Literal],
        proof_hints: &[u64],
        conflict_id: u64,
    ) -> bool {
        if self.proof_manager.is_none() {
            return true;
        }
        let mut proof_hint_ids = det_hash_set_new();
        proof_hint_ids.extend(proof_hints.iter().copied());
        conflict_id != 0
            && self.lrat_hint_id_visible(conflict_id)
            && conflict_lits.iter().all(|lit| {
                self.level0_var_proof_id_for_lit(lit.negated())
                    .is_some_and(|id| proof_hint_ids.contains(&id))
            })
    }
}
