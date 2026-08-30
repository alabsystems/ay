// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Terminal proof-chain construction for level-0 conflicts.

use super::super::*;
use crate::kani_compat::det_hash_set_new;
use crate::solver::solve::theory_callback::TheoryCallback;

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
        if self.cold.backward_proof_limits.is_some() {
            self.mark_empty_clause_deferred_for_bounded_proof();
            return;
        }
        if !self.has_live_clause_trace() && !self.cold.lrat_enabled {
            self.has_empty_clause = true;
            if self.cold.empty_clause_scope_depth == 0 {
                self.cold.empty_clause_scope_depth = self.cold.scope_selectors.len();
            }
            return;
        }
        if self.cold.lrat_enabled {
            self.record_lrat_level0_conflict_chain(conflict_ref);
        } else {
            let chain = self.collect_resolution_chain(conflict_ref, None, &det_hash_set_new());
            self.mark_empty_clause_with_hints_and_trace(&chain, chain.clone());
        }
    }

    fn record_lrat_level0_conflict_chain(&mut self, conflict_ref: ClauseRef) {
        self.materialize_level0_unit_proofs();
        let conflict_lits = self.arena.literals(conflict_ref.0 as usize).to_vec();
        self.seed_level0_conflict_unit_chain(&conflict_lits);
        let unit_chain = self.collect_level0_unit_chain();
        let conflict_id = self.materialize_level0_conflict_clause_id(conflict_ref, &conflict_lits);

        let mut proof_hints: Vec<u64> = unit_chain
            .into_iter()
            .rev()
            .filter(|&hint| hint != 0)
            .collect();
        if conflict_id != 0 {
            proof_hints.push(conflict_id);
        }
        let trace_chain = self.collect_level0_conflict_trace_chain(conflict_ref);
        let proof_complete =
            self.level0_conflict_proof_chain_complete(&conflict_lits, &proof_hints, conflict_id);
        let trace_complete =
            self.level0_conflict_trace_chain_complete(trace_chain.as_deref(), conflict_id);
        if !proof_complete || !trace_complete {
            // Never attach a partial terminal chain. The semantic UNSAT result
            // remains valid, while every certificate consumer fails closed.
            if let Some(trace) = self.live_clause_trace_mut() {
                trace.mark_proof_work_exhausted();
            }
            self.refresh_proof_consumer_state();
            self.mark_empty_clause_deferred_for_bounded_proof();
            return;
        }
        self.mark_empty_clause_with_hints_and_trace(&proof_hints, trace_chain.unwrap_or_default());
    }

    fn seed_level0_conflict_unit_chain(&mut self, conflict_lits: &[Literal]) {
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
        for &lit in conflict_lits {
            let var_idx = lit.variable().index();
            if var_idx < self.var_data.len() && self.min.minimize_flags[var_idx] & LRAT_A == 0 {
                self.min.minimize_flags[var_idx] |= LRAT_A;
                self.min.lrat_to_clear.push(var_idx);
            }
        }
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

    fn collect_level0_conflict_trace_chain(&mut self, conflict_ref: ClauseRef) -> Option<Vec<u64>> {
        // ClauseTrace is independently replayed as positive RUP, so publish
        // root reasons first and the all-false conflict clause last.
        self.collect_complete_resolution_chain(conflict_ref, None, &det_hash_set_new())
            .map(|mut chain| {
                chain.reverse();
                let mut seen = det_hash_set_new();
                chain.retain(|id| seen.insert(*id));
                chain
            })
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

    fn level0_conflict_trace_chain_complete(
        &self,
        trace_chain: Option<&[u64]>,
        conflict_id: u64,
    ) -> bool {
        let Some(trace) = self.live_clause_trace() else {
            return true;
        };
        let Some(chain) = trace_chain else {
            return false;
        };
        let mut missing_ids = det_hash_set_new();
        missing_ids.extend(chain.iter().copied());
        for entry in trace.entries() {
            missing_ids.remove(&entry.id);
            if missing_ids.is_empty() {
                break;
            }
        }
        !trace.is_truncated()
            && !trace.proof_work_exhausted()
            && chain.last() == Some(&conflict_id)
            && chain.iter().all(|&id| id != 0)
            && missing_ids.is_empty()
    }
}
