// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause addition and management methods for the SAT solver.
//!
//! Includes: empty clause handling (mark_empty_clause*), clause addition
//! (add_clause*, add_theory_lemma, add_theory_propagation), watch literal
//! reordering, clause DB internals, factor candidate marking, and
//! solution-witness checking on clause changes.

use super::*;

/// Maximum number of literals a clause may contain before the solver splits it
/// into an equisatisfiable chain of sub-clauses (#oversized).
///
/// The clause arena stores the literal count in only 16 bits, so a clause must
/// have at most `u16::MAX` (65535) literals to be representable. We split at a
/// margin below that so each chain link (chunk + up to two auxiliary literals
/// + any replicated scope selectors) still fits comfortably under the hard
/// limit.
pub(super) const OVERSIZED_CLAUSE_SPLIT_THRESHOLD: usize = 60_000;

/// Oversized-clause splitting is ALWAYS ON. (The former
/// `AY_SPLIT_OVERSIZED_CLAUSES=0` opt-out — which stored oversized clauses
/// truncated and poisoned any resulting UNSAT down to `Unknown` — is removed;
/// splitting is the sound, lossless default.)
pub(super) fn oversized_clause_split_enabled() -> bool {
    true
}

impl Solver {
    /// Mark that an empty clause was derived (UNSAT), with optional LRAT
    /// resolution hints.
    ///
    /// Callers that have resolution chain data (e.g. `record_level0_conflict_chain`)
    /// pass the chain as `hints` so the LRAT proof entry includes the derivation.
    /// Most callers pass `&[]` (no hints available).
    ///
    /// This also records the empty clause to the trace if enabled.
    #[inline]
    pub(super) fn mark_empty_clause_with_hints(&mut self, hints: &[u64]) {
        self.mark_empty_clause_with_hints_and_trace(hints, Vec::new());
    }

    /// Emit and record the bounded backward producer's terminal empty clause.
    ///
    /// Unlike [`Self::mark_empty_clause_with_hints`], this always emits a new
    /// terminal addition. Backward reconstruction may have appended reserved
    /// learned steps after an earlier empty marker, so only this successful
    /// addition is allowed to establish the terminal-proof flags.
    pub(super) fn mark_empty_clause_with_bounded_prevalidated_hints(
        &mut self,
        hints: &[u64],
        deadline: Option<ay_core::time::Instant>,
    ) -> std::io::Result<()> {
        assert!(
            self.cold.solution_witness.is_none(),
            "BUG: derived empty clause (UNSAT) but a satisfying assignment was configured"
        );

        if !self.has_empty_clause {
            self.cold.empty_clause_scope_depth = self.cold.scope_selectors.len();
        }
        self.has_empty_clause = true;

        // A stale marker must not license UNSAT if this new terminal write
        // fails after bounded learned steps have already been appended.
        self.cold.empty_clause_in_proof = false;
        self.cold.empty_clause_lrat_id = None;
        let added_before = self
            .proof_manager
            .as_ref()
            .map_or(0, ProofManager::added_count);
        let clause_id = self.proof_emit_bounded_terminal_rup(hints, deadline)?;
        let added_after = self
            .proof_manager
            .as_ref()
            .map_or(added_before, ProofManager::added_count);
        if clause_id == 0 || added_after != added_before.saturating_add(1) {
            return Err(std::io::Error::other(
                "bounded terminal LRAT addition was not recorded",
            ));
        }

        self.cold.empty_clause_in_proof = true;
        self.cold.empty_clause_lrat_id = Some(clause_id);
        if self.cold.next_clause_id <= clause_id {
            self.cold.next_clause_id = clause_id + 1;
        }
        if let Some(trace) = self.live_clause_trace_mut() {
            trace.add_clause_with_hints(clause_id, Vec::new(), false, Vec::new());
        }
        Ok(())
    }

    /// Mark empty clause with both LRAT proof hints and clause-trace resolution
    /// hints attached atomically (#4435).
    pub(super) fn mark_empty_clause_with_hints_and_trace(
        &mut self,
        hints: &[u64],
        trace_hints: Vec<u64>,
    ) {
        if self.cold.backward_proof_limits.is_some() {
            self.mark_empty_clause_deferred_for_bounded_proof();
            return;
        }

        // Solution-guided debugging (#4615): if a known satisfying assignment
        // exists, deriving the empty clause is a soundness bug. CaDiCaL parity:
        // check_no_solution_after_learning_empty_clause.
        assert!(
            self.cold.solution_witness.is_none(),
            "BUG: derived empty clause (UNSAT) but a satisfying assignment was \
             configured via set_solution — solver incorrectly claims unsatisfiable"
        );

        let first_empty_clause = !self.has_empty_clause;
        // Only record the scope depth on the first occurrence; a base-level
        // empty clause (depth 0) must never be overwritten by a scoped one.
        if first_empty_clause {
            self.cold.empty_clause_scope_depth = self.cold.scope_selectors.len();
        }
        self.has_empty_clause = true;

        // Write empty clause to proof writer and allocate LRAT ID atomically.
        // Guard: only on the first derivation — repeated calls must NOT
        // advance next_clause_id (Fix 1 of #4475: ID drift on repeated calls).
        if !self.cold.empty_clause_in_proof {
            let proof_steps_before = self
                .proof_manager
                .as_ref()
                .map_or(0, ProofManager::added_count);
            // proof_emit_add handles both forward checking (#4483) and proof
            // emission, satisfying the single-authority contract (#4564).
            // For LRAT mode, proof_emit_add also prepends level-0 unit proof
            // IDs (#7108). This is safe even when the caller already includes
            // level-0 IDs because the hint chain deduplicates.
            let proof_clause_id = match self.proof_emit_add(&[], hints, ProofAddKind::Derived) {
                Ok(id) if id != 0 => Some(id),
                _ => None,
            };
            let proof_steps_after = self
                .proof_manager
                .as_ref()
                .map_or(proof_steps_before, ProofManager::added_count);
            if proof_steps_after > proof_steps_before {
                self.cold.empty_clause_in_proof = true;
                self.cold.empty_clause_lrat_id = proof_clause_id;
            }

            // Assign clause ID and record to clause trace.
            // When LRAT is enabled, resync with proof writer's ID if deletion
            // steps consumed IDs (#4398). In fail-close mode, non-empty LRAT
            // writes are intentionally suppressed, so writer IDs may lag solver
            // IDs. Keep solver IDs monotonic to avoid duplicate IDs in ClauseTrace.
            //
            // When LRAT is disabled but clause_trace is enabled (SMT proof path),
            // still allocate a clause ID and record the empty clause with its
            // resolution hints so that process_trace can reconstruct the proof
            // chain (#6368).
            if self.cold.lrat_enabled {
                let clause_id = if let Some(pid) = proof_clause_id.filter(|&id| id != 0) {
                    // Guard: LRAT returns Ok(0) as io_failed sentinel (#4434, #4572).
                    // Only sync when the writer returned a real ID.
                    // NOTE: uses pid+1 (not pid) because no add_clause_db follows.
                    // Contrast with enqueue_derived_unit which sets pid and lets
                    // add_clause_db increment (#4886).
                    self.cold.next_clause_id = pid + 1;
                    pid
                } else {
                    let id = self.cold.next_clause_id;
                    self.cold.next_clause_id += 1;
                    id
                };
                self.cold.empty_clause_lrat_id = Some(clause_id);
                // Record to clause trace if enabled — hints attached atomically
                if let Some(trace) = self.live_clause_trace_mut() {
                    trace.add_clause_with_hints(clause_id, vec![], false, trace_hints);
                }
            } else if self.has_live_clause_trace() {
                // SMT proof path: clause trace enabled without LRAT. Allocate a
                // local clause ID and record the empty clause with resolution
                // hints so process_trace can build a proper derivation (#6368).
                let clause_id = self.cold.empty_clause_lrat_id.unwrap_or_else(|| {
                    let id = self.cold.next_clause_id;
                    self.cold.next_clause_id += 1;
                    id
                });
                self.cold.empty_clause_lrat_id = Some(clause_id);
                if let Some(trace) = self.live_clause_trace_mut() {
                    trace.add_clause_with_hints(clause_id, vec![], false, trace_hints);
                }
            }
        }
    }

    /// Record semantic UNSAT while deferring every proof/trace allocation to
    /// bounded postsolve reconstruction.
    pub(super) fn mark_empty_clause_deferred_for_bounded_proof(&mut self) {
        assert!(
            self.cold.solution_witness.is_none(),
            "BUG: derived empty clause (UNSAT) but a satisfying assignment was configured"
        );
        if !self.has_empty_clause {
            self.cold.empty_clause_scope_depth = self.cold.scope_selectors.len();
        }
        self.has_empty_clause = true;
    }

    /// Mark that an empty clause was derived (UNSAT) with no resolution hints.
    #[inline]
    pub(super) fn mark_empty_clause(&mut self) {
        self.mark_empty_clause_with_hints(&[]);
    }

    /// Mark the empty clause with LRAT hints reconstructed from the level-0 trail.
    ///
    /// Used by inprocessing fallback paths that detect UNSAT without a concrete
    /// conflict clause to pass to `record_level0_conflict_chain`.
    #[inline]
    pub(super) fn mark_empty_clause_with_level0_hints(&mut self) {
        if self.cold.lrat_enabled {
            self.ensure_level0_unit_proof_ids();
            let hints = self.build_finalize_empty_clause_hints();
            self.mark_empty_clause_with_hints(&hints);
        } else {
            self.mark_empty_clause();
        }
    }

    /// Add a clause.
    pub fn add_clause(&mut self, mut literals: Vec<Literal>) -> bool {
        self.add_clause_reusing_buffer(&mut literals)
    }

    /// Add a clause from a caller-owned reusable buffer.
    ///
    /// This preserves [`Self::add_clause`] semantics, including scope selector
    /// insertion, original ledger registration, proof ID assignment, duplicate
    /// removal, and tautology handling. The caller's buffer is cleared before
    /// return while retaining its allocation.
    pub fn add_clause_reusing_buffer(&mut self, literals: &mut Vec<Literal>) -> bool {
        let was_empty = literals.is_empty();
        if let Some(selector) = self.cold.scope_selectors.last().copied() {
            literals.push(Literal::positive(selector));
        }

        if literals.is_empty() {
            // A base-level empty input clause is an original axiom, not an
            // unsupported zero-hint derivation. Register its original ID and
            // derive the proof-terminal empty clause from that ID so standalone
            // LRAT checkers see a complete chain (`2 0 1 0` for a one-clause
            // input). Scoped empty assertions retain the established scoped
            // UNSAT marker semantics and are retracted by pop().
            return self.add_original_empty_clause(false);
        }

        self.set_diagnostic_pass(DiagnosticPass::Input);
        let result = self.add_clause_unscoped_inner(literals, false, false);
        self.clear_diagnostic_pass();
        if was_empty {
            // A scoped empty assertion is represented by its positive scope
            // selector. It is false while the scope's implicit negative
            // selector assumption is active and disappears on pop().
            false
        } else {
            result
        }
    }

    /// Register an empty input clause in every original-clause authority
    /// without trying to place it in the non-empty clause arena.
    fn add_original_empty_clause(&mut self, global: bool) -> bool {
        if global {
            self.cold.original_ledger.push_clause_global(&[]);
        } else {
            self.cold.original_ledger.push_clause(&[]);
        }
        self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
        self.cold.uniform_formula_cache = None;

        if let Some(ref mut checker) = self.cold.forward_checker {
            checker.add_original(&[]);
        }
        if let Some(ref mut manager) = self.proof_manager {
            manager.register_original_clause(&[]);
        }

        let clause_id = self.allocate_original_clause_id();

        if self.cold.lrat_enabled {
            if let Some(ref mut manager) = self.proof_manager {
                manager.register_clause_id(clause_id);
            }
            if self.has_live_clause_trace() {
                let _ = self.charge_proof_bookkeeping(16);
            }
            if let Some(trace) = self.live_clause_trace_mut() {
                trace.add_clause_with_hints(clause_id, Vec::new(), true, Vec::new());
            }
        }

        if self.cold.lrat_enabled {
            if let Some(deadline) = self
                .cold
                .backward_proof_limits
                .as_ref()
                .map(|limits| limits.deadline)
            {
                // This one-ID derivation is producer-prevalidated and already
                // fully bounded. Emit it now because an original empty clause
                // has no arena seed for postsolve reconstruction.
                let _ =
                    self.mark_empty_clause_with_bounded_prevalidated_hints(&[clause_id], deadline);
            } else {
                self.mark_empty_clause_with_hints(&[clause_id]);
            }
        } else {
            self.mark_empty_clause();
        }
        if global {
            // A global empty clause added inside a push scope must remain UNSAT
            // after pop(), unlike an ordinary scoped contradiction.
            self.cold.empty_clause_scope_depth = 0;
        }
        false
    }

    fn reserve_skipped_original_lrat_id(&mut self, literals: &[Literal]) {
        if !self.cold.lrat_enabled {
            return;
        }

        let clause_id = self.allocate_original_clause_id();

        if let Some(ref mut manager) = self.proof_manager {
            manager.register_original_clause(literals);
            manager.register_clause_id(clause_id);
        }
    }

    /// Add a pre-sorted clause, skipping the sort step but still deduping.
    ///
    /// The caller guarantees that literals are sorted by `.0` value.
    /// This function performs an O(n) dedup pass and tautology check on
    /// the sorted input, which is cheaper than add_clause's O(n log n)
    /// sort + O(n) dedup. For BV instances with 100K+ clauses, this
    /// saves ~10% of clause-addition time.
    ///
    /// If duplicate literals or tautologies (x and !x) are found, they
    /// are handled correctly (duplicates removed, tautologies skipped).
    pub fn add_clause_prenormalized(&mut self, literals: &[Literal]) -> bool {
        if literals.is_empty() {
            return self.add_original_empty_clause(false);
        }

        // O(n) dedup + tautology check on pre-sorted input.
        // This is critical for correctness: Tseitin/BV clauses can contain
        // duplicate literals after CNF transformation, and passing duplicates
        // to the original ledger causes FINALIZE_SAT_FAIL during model
        // reconstruction (#8782).
        let mut deduped: Vec<Literal> = Vec::with_capacity(literals.len());
        for &lit in literals {
            if let Some(&last) = deduped.last() {
                if lit == last {
                    // Duplicate literal — skip
                    continue;
                }
                if lit.variable() == last.variable() {
                    // Tautology (x and !x) — skip entire clause
                    return true;
                }
            }
            deduped.push(lit);
        }

        if deduped.is_empty() {
            return self.add_original_empty_clause(false);
        }

        // Record in original ledger (same as add_clause_unscoped).
        self.cold.original_ledger.push_clause(&deduped);
        self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
        self.cold.uniform_formula_cache = None;

        let _ = self.add_clause_db(&deduped, false);
        true
    }

    /// Add a pre-sorted clause and return its arena offset (#8275).
    ///
    /// Like `add_clause_prenormalized`, but returns `Some(arena_offset)` for
    /// clauses with length >= 3 that were added to the arena. Returns `None`
    /// for unit/binary clauses (handled inline by 2WL) or tautologies.
    ///
    /// The arena offset serves as the clause ID for JIT compilation: BV
    /// compiled functions use it so that conflict analysis can construct
    /// `ClauseRef(arena_offset)` to access the clause in the standard way.
    pub fn add_clause_prenormalized_returning_offset(
        &mut self,
        literals: &[Literal],
    ) -> Option<usize> {
        if literals.is_empty() {
            self.add_original_empty_clause(false);
            return None;
        }

        // O(n) dedup + tautology check on pre-sorted input.
        let mut deduped: Vec<Literal> = Vec::with_capacity(literals.len());
        for &lit in literals {
            if let Some(&last) = deduped.last() {
                if lit == last {
                    continue;
                }
                if lit.variable() == last.variable() {
                    return None; // Tautology
                }
            }
            deduped.push(lit);
        }

        if deduped.is_empty() {
            self.add_original_empty_clause(false);
            return None;
        }

        // Record in original ledger.
        self.cold.original_ledger.push_clause(&deduped);
        self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
        self.cold.uniform_formula_cache = None;

        let offset = self.add_clause_db(&deduped, false);

        // Return offset only for ternary+ clauses (JIT-compilable).
        if deduped.len() >= 3 {
            Some(offset)
        } else {
            None
        }
    }

    /// Add a clause without any scope selector (global clause).
    ///
    /// Use this for clauses that should persist across all push/pop scopes.
    /// Unlike `add_clause`, this does NOT add a scope selector even if
    /// we're currently inside a push() scope.
    ///
    /// Global clauses are recorded in the original ledger via `push_clause_global`
    /// which buffers them separately when inside a push scope, replaying them
    /// after `pop_scope` truncation to ensure they survive (#9378).
    #[allow(clippy::needless_pass_by_value)]
    pub fn add_clause_global(&mut self, literals: Vec<Literal>) -> bool {
        self.set_diagnostic_pass(DiagnosticPass::Input);
        let result = self.add_clause_unscoped_global(literals, false);
        self.clear_diagnostic_pass();
        result
    }

    /// Add a clause scoped to an ancestor push depth.
    ///
    /// Depth `0` is global. Depth `self.scope_depth()` matches [`Self::add_clause`].
    /// This is used by incremental SMT layers when an assertion is first encoded
    /// in a deeper scope than the scope where it semantically belongs.
    pub fn add_clause_at_scope_depth(
        &mut self,
        literals: Vec<Literal>,
        scope_depth: usize,
    ) -> bool {
        debug_assert!(
            scope_depth <= self.cold.scope_selectors.len(),
            "requested scope depth {} exceeds active depth {}",
            scope_depth,
            self.cold.scope_selectors.len()
        );

        if scope_depth == 0 {
            return self.add_clause_global(literals);
        }
        if scope_depth == self.cold.scope_selectors.len() {
            return self.add_clause(literals);
        }

        let mut literals = literals;
        let selector = self.cold.scope_selectors[scope_depth - 1];
        literals.push(Literal::positive(selector));

        self.set_diagnostic_pass(DiagnosticPass::Input);
        let result = self.add_clause_unscoped(literals, false);
        self.clear_diagnostic_pass();
        result
    }

    /// Like `add_clause_unscoped` but records the clause as global in the
    /// original ledger so it survives `pop_scope` truncation (#9378).
    ///
    /// Used by `add_clause_global` for Tseitin definition clauses that must
    /// persist across all push/pop scopes.
    #[allow(clippy::needless_pass_by_value)]
    pub(super) fn add_clause_unscoped_global(
        &mut self,
        literals: Vec<Literal>,
        learned: bool,
    ) -> bool {
        let mut literals = literals;
        self.add_clause_unscoped_inner(&mut literals, learned, true)
    }

    #[allow(clippy::needless_pass_by_value)]
    pub(super) fn add_clause_unscoped(&mut self, literals: Vec<Literal>, learned: bool) -> bool {
        let mut literals = literals;
        self.add_clause_unscoped_inner(&mut literals, learned, false)
    }

    fn add_clause_unscoped_inner(
        &mut self,
        literals: &mut Vec<Literal>,
        learned: bool,
        global: bool,
    ) -> bool {
        // IC3 incremental clause addition (#8569): instead of fully
        // invalidating the assumption cache (which forces O(num_vars) full
        // reset), mark new clauses as pending. The IC3 incremental reset
        // path handles them in O(new_clauses) time: attach watches and
        // propagate any new units. This is the key optimization for IC3
        // throughput — IC3 adds blocking clauses between every query.
        //
        // Previous behavior (#8443): `assumption_cache_valid = false` forced
        // full `reset_search_state()` on every `add_clause` call.
        if !learned {
            self.cold.ic3_new_clauses_pending = true;
        }
        // All literal variables must be in range
        debug_assert!(
            literals
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: add_clause_unscoped: literal variable out of range (num_vars={})",
            self.num_vars,
        );
        if literals.is_empty() {
            if learned {
                self.mark_empty_clause();
            } else {
                self.add_original_empty_clause(global);
            }
            literals.clear();
            return false;
        }

        // Normalize: remove duplicate literals and discard tautologies.
        // Duplicate literals confuse the 2-watched literal scheme (both watches
        // on the same variable). Tautologies (x ∨ ¬x) are always satisfied.
        // CaDiCaL does this in External::add(); add_theory_lemma() already did.
        literals.sort_by_key(|l| l.0);
        literals.dedup();
        for i in 1..literals.len() {
            if literals[i].variable() == literals[i - 1].variable() {
                if !learned {
                    self.reserve_skipped_original_lrat_id(literals.as_slice());
                }
                literals.clear();
                return true; // Tautology — always satisfied, nothing to add
            }
        }
        if literals.is_empty() {
            if learned {
                self.mark_empty_clause();
            } else {
                self.add_original_empty_clause(global);
            }
            literals.clear();
            return false;
        }

        // #oversized: a clause with more literals than the arena's 16-bit
        // length field can represent (> u16::MAX) cannot be stored intact. By
        // default we split it into an equisatisfiable chain of sub-clauses,
        // each within the arena limit, using fresh auxiliary variables. This is
        // the only sound way to SOLVE such instances (a single negated
        // `distinct` over hundreds of terms produces C(n,2) literals). When
        // splitting is disabled, fall through and let the arena store the
        // clause truncated, setting a sticky poison flag so any resulting UNSAT
        // is downgraded to Unknown (SAT stays sound — truncation strengthens).
        if literals.len() > OVERSIZED_CLAUSE_SPLIT_THRESHOLD {
            if oversized_clause_split_enabled() {
                return self.add_oversized_clause_split(literals, learned, global);
            }
            self.cold.oversized_clause_poison = true;
        }

        // #7981: CaDiCaL-parity reactivation — when a new clause references a
        // variable eliminated by BVE or substituted by SCC decompose, reactivate
        // it immediately with competitive VSIDS activity. Without this, the
        // eliminated variable sits at zero activity in the decision heap and may
        // never be branched on, causing incomplete search and false UNSAT.
        // Reference: CaDiCaL external.cpp:160-161 (internalize reactivation).
        {
            let reactivation_activity = self.vsids.current_increment();
            for lit in literals.iter() {
                let var_idx = lit.variable().index();
                if var_idx < self.var_lifecycle.len()
                    && self.var_lifecycle.is_removed(var_idx)
                    && self.var_lifecycle.can_reactivate(var_idx)
                {
                    self.var_lifecycle.reactivate(var_idx);
                    self.inproc.bve.clear_removed_external(var_idx);
                    let var = Variable(var_idx as u32);
                    if self.vsids.activity(var) == 0.0 {
                        self.vsids.set_activity(var, reactivation_activity);
                    }
                }
            }
        }

        // Record original (non-learned) clauses in the immutable ledger.
        // Only clauses from the public add_clause/add_clause_global API reach
        // here; derived clauses (BVE resolvents, theory lemmas) go through
        // add_clause_watched → add_clause_db and are NOT recorded, because
        // the ledger must reflect the true user input formula only.
        // #5031: original_clauses needed in release for incremental-solve
        // clause_db rebuild in reset_search_state.
        if !learned {
            // Global clauses use push_clause_global to survive pop_scope (#9378).
            if global {
                self.cold
                    .original_ledger
                    .push_clause_global(literals.as_slice());
            } else {
                self.cold.original_ledger.push_clause(literals.as_slice());
            }
            // New irredundant clause invalidates the uniform formula cache.
            self.cold.uniform_formula_cache = None;

            // IC3 incremental deferral (#8569): when the assumption cache is
            // valid (we're between incremental solves), defer arena addition
            // and watch attachment to the next solve's reset path. This keeps
            // `incremental_original_boundary` at the old value so
            // `attach_new_clauses_incremental` can find and process the new
            // clauses (add to arena + attach watches + propagate units).
            //
            // Without deferral, add_clause_db adds to the arena without
            // attaching watches (watches are set up by initialize_watches in
            // the full reset path). The incremental reset path skips
            // initialize_watches, leaving the clause unwatched and invisible
            // to BCP — causing soundness bugs (missed conflicts).
            //
            // #lra-inc-engine (S1): the incremental QF_LRA engine lane FORCES an
            // incremental reset every check-sat even when `assumption_cache_valid`
            // is false (benign per-check-sat var growth invalidates it). Without
            // this extra condition those files would take the non-deferral branch
            // below (arena add, no watches) and then hit the FORCED incremental
            // reset (which skips initialize_watches and whose attach range is
            // already empty because the boundary was advanced) — leaving the
            // delta clauses unwatched → BCP missed conflicts (#8078). Deferring
            // when `inc_engine_reset_mode` keeps the boundary put so the coming
            // incremental reset's `attach_new_clauses_incremental` builds their
            // watches. CHC/PDR (ic3_mode WITHOUT this flag) is unaffected.
            if self.cold.assumption_cache_valid || self.cold.inc_engine_reset_mode {
                literals.clear();
                return true;
            }

            // Non-incremental path: add to arena immediately and keep
            // boundary in sync. reset_search_state will handle watches.
            self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
        }

        let _ = self.add_clause_db(literals.as_slice(), learned);

        literals.clear();
        true
    }

    /// Split a clause with more than [`OVERSIZED_CLAUSE_SPLIT_THRESHOLD`]
    /// literals into an equisatisfiable chain of sub-clauses, each within the
    /// arena's representable size, and add each sub-clause through the normal
    /// `add_clause_unscoped_inner` path (#oversized).
    ///
    /// Construction (standard ladder/cascade encoding of a big OR). Let the
    /// non-selector body literals be `b_0 … b_{N-1}` split into `m` chunks and
    /// `S` be the set of active scope-selector literals already present in the
    /// clause. With fresh auxiliary variables `a_1 … a_{m-1}` we emit:
    ///
    /// * `(chunk_0 ∨ a_1 ∨ S)`
    /// * `(¬a_i ∨ chunk_i ∨ a_{i+1} ∨ S)`  for `0 < i < m-1`
    /// * `(¬a_{m-1} ∨ chunk_{m-1} ∨ S)`
    ///
    /// This is equisatisfiable with `(b_0 ∨ … ∨ b_{N-1} ∨ S)`: projecting the
    /// fresh `a_i` away yields exactly the original disjunction. The scope
    /// selectors `S` are replicated into **every** sub-clause so that asserting
    /// a selector true (the way `pop()` disables a scope) satisfies the whole
    /// chain, exactly as it would the original clause.
    ///
    /// Each sub-clause is at most `chunk + 2 (aux) + |S|` literals, which the
    /// chunk sizing keeps strictly below the split threshold, so the recursive
    /// `add_clause_unscoped_inner` calls never re-trigger a split.
    fn add_oversized_clause_split(
        &mut self,
        literals: &mut Vec<Literal>,
        learned: bool,
        global: bool,
    ) -> bool {
        // Partition into active scope selectors (replicated into every link)
        // and body literals (chained). Selectors are identified via
        // `scope_selector_set`, which marks exactly the variables that are
        // live scope selectors at this point.
        let selector_set = &self.cold.scope_selector_set;
        let mut selectors: Vec<Literal> = Vec::new();
        let mut body: Vec<Literal> = Vec::with_capacity(literals.len());
        for &lit in literals.iter() {
            let vi = lit.variable().index();
            if vi < selector_set.len() && selector_set[vi] && lit.is_positive() {
                // Scope selectors are added as positive literals (clause_add).
                selectors.push(lit);
            } else {
                body.push(lit);
            }
        }
        literals.clear();

        // Chunk size leaves room for the two auxiliary literals and the
        // replicated selectors so each emitted sub-clause stays below the
        // split threshold. Guard against pathological selector counts.
        let reserve = selectors.len() + 2;
        let chunk = OVERSIZED_CLAUSE_SPLIT_THRESHOLD
            .saturating_sub(reserve)
            .max(1);

        let num_chunks = body.len().div_ceil(chunk);
        debug_assert!(
            num_chunks >= 2,
            "BUG: oversized split produced fewer than two chunks (body={}, chunk={})",
            body.len(),
            chunk
        );

        // Allocate the `num_chunks - 1` linking auxiliary variables up front.
        //
        // Use `new_var()` (not `new_var_internal()`) so `user_num_vars` tracks
        // these auxiliaries. Theory layers built on top of this solver (the
        // ay-dpll DPLL(T) eager-extension pipeline) compute the next free SAT
        // variable as `user_num_vars() + scope_depth()` and allocate fresh
        // theory-split variables from there. If the auxiliaries did not advance
        // `user_num_vars`, those theory variables would alias our auxiliaries,
        // corrupting the variable space and yielding a spurious `unknown`
        // (#oversized).
        let mut aux_vars: Vec<Variable> = Vec::with_capacity(num_chunks - 1);
        for _ in 0..num_chunks - 1 {
            aux_vars.push(self.new_var());
        }

        let mut all_added = true;
        for c in 0..num_chunks {
            let start = c * chunk;
            let end = ((c + 1) * chunk).min(body.len());
            let mut sub: Vec<Literal> = Vec::with_capacity((end - start) + 2 + selectors.len());
            // Incoming link: ¬a_c (for all but the first chunk).
            if c > 0 {
                sub.push(Literal::negative(aux_vars[c - 1]));
            }
            sub.extend_from_slice(&body[start..end]);
            // Outgoing link: a_{c+1} (for all but the last chunk).
            if c + 1 < num_chunks {
                sub.push(Literal::positive(aux_vars[c]));
            }
            // Replicate scope selectors into every link.
            sub.extend_from_slice(&selectors);
            // Each sub-clause is within the split threshold, so this recursive
            // call cannot re-enter the oversized path.
            if !self.add_clause_unscoped_inner(&mut sub, learned, global) {
                all_added = false;
            }
        }
        all_added
    }

    /// Reorder clause literals for optimal watch selection using explicit state slices.
    fn reorder_clause_for_watches_with_state(
        vals: &[i8],
        var_data: &[VarData],
        literals: &mut [Literal],
    ) {
        if literals.len() < 2 {
            return;
        }

        // Score each literal: higher is better for watching
        // Unassigned = highest priority (we want to detect unit propagation)
        // True at high level = good (clause is satisfied, watches stable)
        // False at high level = better than false at low level
        let score = |lit: Literal| -> i64 {
            let v = vals[lit.index()];
            if v == 0 {
                i64::MAX // Unassigned - best
            } else {
                let level = i64::from(var_data[lit.variable().index()].level);
                if v > 0 {
                    // Literal is true
                    1_000_000 + level
                } else {
                    // Literal is false
                    level
                }
            }
        };

        // Find best two literals
        let mut best_idx = 0;
        let mut best_score = score(literals[0]);
        for (i, &lit) in literals.iter().enumerate().skip(1) {
            let s = score(lit);
            if s > best_score {
                best_score = s;
                best_idx = i;
            }
        }
        literals.swap(0, best_idx);

        let mut second_idx = 1;
        let mut second_score = score(literals[1]);
        for (i, &lit) in literals.iter().enumerate().skip(2) {
            let s = score(lit);
            if s > second_score {
                second_score = s;
                second_idx = i;
            }
        }
        literals.swap(1, second_idx);

        // Postcondition: no non-watched literal has a better score than the worst
        // watched literal. Violations indicate a bug in the scoring/selection logic.
        // (#3812: unified watch-attachment contract)
        debug_assert!(
            {
                let s0 = score(literals[0]);
                let s1 = score(literals[1]);
                let min_watch = s0.min(s1);
                literals[2..].iter().all(|lit| score(*lit) <= min_watch)
            },
            "BUG: reorder_clause_for_watches postcondition: non-watched literal has better score than watched"
        );
    }

    /// Learned-clause ordering: keep 1UIP at position 0 and place the max
    /// non-UIP decision level at position 1.
    fn reorder_learned_clause_for_watches(var_data: &[VarData], literals: &mut [Literal]) {
        if literals.len() <= 2 {
            return;
        }
        let max_idx = literals[1..]
            .iter()
            .enumerate()
            .max_by_key(|(_, lit)| var_data[lit.variable().index()].level)
            .map(|(i, _)| i + 1)
            .unwrap_or(1);
        if max_idx != 1 {
            literals.swap(1, max_idx);
        }
    }

    #[inline(always)]
    fn learned_clause_tail_reorder_key(var_data: &[VarData], lit: Literal) -> (u32, u32) {
        let data = var_data[lit.variable().index()];
        (data.level, data.trail_pos)
    }

    /// Reorder the learned-clause tail in place by descending assignment recency.
    ///
    /// Positions 0 and 1 are the watched literals and must remain untouched.
    /// The active learned-tail reorder gates bound this insertion sort to at
    /// most 61 tail literals, avoiding heap allocation while keeping counter
    /// accounting explicit.
    fn reorder_learned_clause_tail_by_assignment_recency(
        var_data: &[VarData],
        literals: &mut [Literal],
    ) -> u64 {
        let mut swaps = 0_u64;
        for i in 3..literals.len() {
            let mut j = i;
            while j > 2 {
                let prev_key = Self::learned_clause_tail_reorder_key(var_data, literals[j - 1]);
                let current_key = Self::learned_clause_tail_reorder_key(var_data, literals[j]);
                if prev_key >= current_key {
                    break;
                }
                literals.swap(j - 1, j);
                swaps += 1;
                j -= 1;
            }
        }
        swaps
    }

    fn learned_clause_tail_reorder_swap_count(var_data: &[VarData], literals: &[Literal]) -> u64 {
        let mut swaps = 0_u64;
        for i in 2..literals.len() {
            let current_key = Self::learned_clause_tail_reorder_key(var_data, literals[i]);
            for prev_lit in &literals[2..i] {
                if Self::learned_clause_tail_reorder_key(var_data, *prev_lit) < current_key {
                    swaps += 1;
                }
            }
        }
        swaps
    }

    pub(super) fn maybe_reorder_learned_tail_at_creation(&mut self, literals: &mut [Literal]) {
        let len = literals.len();
        if self.cold.bcp_learned_617_tail_reorder && (6..=17).contains(&len) {
            let swaps =
                Self::reorder_learned_clause_tail_by_assignment_recency(&self.var_data, literals);
            self.stats.record_bcp_learned_617_tail_reorder(swaps);
        } else if self.cold.bcp_learned_18_tail_reorder && len == 18 {
            let swaps =
                Self::reorder_learned_clause_tail_by_assignment_recency(&self.var_data, literals);
            self.stats.record_bcp_learned_18_tail_reorder(swaps);
        } else if (19..=63).contains(&len) {
            if let Some(budget) = self.cold.bcp_learned_1963_tail_reorder_swap_budget {
                let swaps = Self::learned_clause_tail_reorder_swap_count(&self.var_data, literals);
                if swaps <= budget {
                    let applied_swaps = Self::reorder_learned_clause_tail_by_assignment_recency(
                        &self.var_data,
                        literals,
                    );
                    debug_assert_eq!(applied_swaps, swaps);
                    self.stats
                        .record_bcp_learned_1963_tail_reorder_budget_applied(swaps);
                } else {
                    self.stats
                        .record_bcp_learned_1963_tail_reorder_budget_skipped(swaps);
                }
            } else if self.cold.bcp_learned_1963_tail_reorder {
                let swaps = Self::reorder_learned_clause_tail_by_assignment_recency(
                    &self.var_data,
                    literals,
                );
                self.stats.record_bcp_learned_1963_tail_reorder(swaps);
            }
        }
    }

    /// Prepare watched literals according to the selected ordering policy.
    pub(super) fn prepare_watched_literals_with_state(
        vals: &[i8],
        var_data: &[VarData],
        literals: &mut [Literal],
        policy: WatchOrderPolicy,
    ) -> Option<(Literal, Literal)> {
        if literals.len() < 2 {
            return None;
        }
        match policy {
            WatchOrderPolicy::Preserve => {}
            WatchOrderPolicy::AssignmentScore => {
                Self::reorder_clause_for_watches_with_state(vals, var_data, literals);
            }
            WatchOrderPolicy::LearnedBacktrack => {
                Self::reorder_learned_clause_for_watches(var_data, literals);
                let second_level = var_data[literals[1].variable().index()].level;
                let max_non_uip_level = literals[1..]
                    .iter()
                    .map(|lit| var_data[lit.variable().index()].level)
                    .max()
                    .unwrap_or(0);
                debug_assert_eq!(
                    second_level, max_non_uip_level,
                    "BUG: learned clause watch invariant violated: lits[1] must be the highest non-UIP level"
                );
            }
        }
        let lit0 = literals[0];
        let lit1 = literals[1];
        debug_assert_ne!(
            lit0, lit1,
            "BUG: watch literals must be distinct (policy={policy:?}, lit={lit0:?})"
        );
        Some((lit0, lit1))
    }

    /// Prepare watched literals according to the selected ordering policy.
    pub(super) fn prepare_watched_literals(
        &self,
        literals: &mut [Literal],
        policy: WatchOrderPolicy,
    ) -> Option<(Literal, Literal)> {
        Self::prepare_watched_literals_with_state(&self.vals, &self.var_data, literals, policy)
    }

    /// Attach the selected watched-literal pair to watch lists.
    pub(super) fn attach_clause_watches(
        &mut self,
        clause_ref: ClauseRef,
        watched: (Literal, Literal),
        is_binary: bool,
    ) {
        // BINARY_FLAG watches must correspond to true 2-literal clauses
        // (f0bafebd root cause, wf_0c7d84e9): the BCP binary path propagates
        // the embedded blocker without reading the arena — a longer clause
        // watched as binary propagates unsoundly (ignores its other literals),
        // skips the liveness check, and survives deletion as a stale watch
        // (delete_binary_clause_watches only unlinks true binaries), which
        // manufactured a proof-less level-0 unit through a deleted-rung husk.
        debug_assert_eq!(
            is_binary,
            self.arena.len_of(clause_ref.0 as usize) == 2,
            "BUG: watch binary flag mismatch for clause {} (len {})",
            clause_ref.0,
            self.arena.len_of(clause_ref.0 as usize),
        );
        self.watches
            .watch_clause(clause_ref, watched.0, watched.1, is_binary);
    }

    /// Attach a clause's watches into pre-sized regions (exact initial build).
    ///
    /// Same binary-flag contract as [`attach_clause_watches`]; only the
    /// storage path differs.
    ///
    /// [`attach_clause_watches`]: Solver::attach_clause_watches
    pub(super) fn attach_clause_watches_presized(
        &mut self,
        clause_ref: ClauseRef,
        lit0: Literal,
        lit1: Literal,
        is_binary: bool,
    ) {
        debug_assert_eq!(
            is_binary,
            self.arena.len_of(clause_ref.0 as usize) == 2,
            "BUG: watch binary flag mismatch for clause {} (len {})",
            clause_ref.0,
            self.arena.len_of(clause_ref.0 as usize),
        );
        self.watches
            .watch_clause_presized(clause_ref, lit0, lit1, is_binary);
    }
}
