// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory lemma and theory propagation clause addition.
//!
//! Split from `clause_add.rs` for file-size compliance (#5142).
//! Contains `add_theory_lemma` and `add_theory_propagation`.

use super::*;

impl Solver {
    /// Store an unscoped theory clause without inheriting the current user
    /// assertion depth.
    ///
    /// `add_clause_db_checked` stamps every learned clause with the active
    /// scope depth. Plain theory lemmas and propagation reasons are global by
    /// API contract within the live search, so that generic stamp would let
    /// `pop()` delete them immediately.
    /// Scoped theory APIs append a positive selector guard; those clauses are
    /// still reclaimed by `gc_scoped_clauses` after the selector is popped.
    /// This does not make learned theory clauses permanent across an
    /// incremental reset: they retain their bounded, deletable, theory-re-driven
    /// lifetime and are intentionally absent from the immutable input ledger.
    fn add_unscoped_theory_clause_db(&mut self, literals: &[Literal]) -> usize {
        let idx = self.add_clause_db_checked(literals, true, false, &[]);
        self.arena.set_scope_lim(idx, 0);
        idx
    }

    /// Determine the proof emission kind for theory lemmas.
    ///
    /// Preprocessing extension lemmas (e.g., XOR Gauss-Jordan) use
    /// `TrustedTransform` because they are derivable from consumed
    /// original clauses. SMT theory lemmas use `Axiom` (#7913).
    #[inline]
    fn theory_lemma_proof_kind(&self) -> ProofAddKind {
        if self.cold.extension_trusted_lemmas {
            ProofAddKind::TrustedTransform
        } else {
            ProofAddKind::Axiom
        }
    }

    /// Add a theory lemma with the same active-scope lifetime as `add_clause`.
    ///
    /// `add_theory_lemma` is intentionally an immediate watched-clause path, but
    /// it is unscoped. Incremental SMT callers need both properties: lemmas
    /// must participate in propagation/conflict analysis immediately, and they
    /// must be disabled when the current assertion scope is popped. Appending
    /// the positive scope selector matches `add_clause`'s guard convention.
    pub fn add_theory_lemma_scoped(&mut self, mut literals: Vec<Literal>) -> Option<ClauseRef> {
        if let Some(selector) = self.cold.scope_selectors.last().copied() {
            literals.push(Literal::positive(selector));
        }
        self.add_theory_lemma(literals)
    }

    /// Add a THEORY-CONFLICT lemma (#unguarded-tvalid-lemmas STAGE 1).
    ///
    /// Routing gate for T-VALID conflict lemmas — clauses that are theory
    /// tautologies over term-semantic atom literals (e.g. an LRA Farkas-core
    /// conflict lemma: the negation of a theory-inconsistent atom
    /// conjunction), valid at every scope forever. Callers must route ONLY
    /// such clauses here; theory PROPAGATION reasons and lazily-added
    /// circuit/definition clauses stay on the scoped APIs.
    ///
    /// Default (`unguarded_theory_conflict_lemmas` off): identical to
    /// [`Self::add_theory_lemma_scoped`] — the innermost scope selector is
    /// appended and the lemma dies with its scope. Unchanged behavior.
    ///
    /// Flag on (the incremental QF_LRA engine lane, which excludes proof
    /// sessions): route to the EXISTING unscoped [`Self::add_theory_lemma`]
    /// path, whose `add_unscoped_theory_clause_db` stamps `scope_lim = 0` —
    /// OpenSMT-style permanent retention across `pop()`. Invariants that
    /// make this sound (each verified in this codebase state):
    ///
    /// * T-validity provenance: the swapped call sites map conflicts from
    ///   `TermId`-keyed atom maps with fail-closed partial-mapping guards
    ///   (`map_conflict_lits` in ay-dpll `split_incremental.rs` returns
    ///   `Unmapped` => no clause; the eager extension's `term_to_literal`
    ///   mapping in `extension/check.rs` returns `Unknown` on a partial
    ///   clause, #3826), and any pre-minimization removes only literals
    ///   falsified at level 0 — root facts that are themselves
    ///   session-permanent (level-0 propagation can only fire from
    ///   unguarded/permanent clauses; scoped clauses carry an unassigned
    ///   `+selector` at level 0).
    /// * Atom binding stability: `pop()` never shrinks `num_vars` or reuses
    ///   variable indices (see `Solver::pop`), so a persisted lemma's
    ///   literals keep their term semantics for the whole session.
    /// * Ledger sync: the unscoped path never touches `original_ledger`
    ///   (theory lemmas are learned-tier, "intentionally absent from the
    ///   immutable input ledger" — see `add_unscoped_theory_clause_db`), so
    ///   the `reset_search_state` census (`active_original_count`, which
    ///   filters `is_learned`) cannot be desynced by these lemmas, and a
    ///   destructive-rebuild fallback simply DROPS them (sound: they are
    ///   re-derivable theory axioms).
    /// * Pop-time GC: `gc_scoped_clauses` deletes only clauses CONTAINING
    ///   the popped `+selector` (an unguarded lemma has none) and
    ///   `gc_leaked_learned_clauses` deletes only `scope_lim > new_depth`
    ///   (an unguarded lemma is stamped 0; the ic3-mode inc-engine lane
    ///   skips that sweep entirely).
    /// * Stale-ref hazards from the #inc-scoped-lemmas autopsy are closed
    ///   centrally: `pop()` drops `pending_theory_conflicts`
    ///   unconditionally, and the ledger arena rebuild normalizes every
    ///   `var_data.reason` to `NO_REASON` (#inc-rebuild-reasons).
    /// * Memory bound: the lemma lands in the DELETABLE tier
    ///   (`reduce_permanent_protect_lbd() + 1` below), so `reduce_db`
    ///   bounds the retained pool exactly as for every other theory lemma.
    pub fn add_theory_conflict_lemma(&mut self, literals: Vec<Literal>) -> Option<ClauseRef> {
        if self.cold.unguarded_theory_conflict_lemmas {
            return self.add_theory_lemma(literals);
        }
        self.add_theory_lemma_scoped(literals)
    }

    /// Add a theory lemma clause during solving.
    ///
    /// Unlike `add_clause`, this properly sets up watches so the clause can
    /// participate in propagation. This is essential for eager DPLL(T) where
    /// theory solvers add lemmas during the SAT search.
    ///
    /// The clause is reordered so that:
    /// - `literals[0]` is unassigned or the most recently assigned satisfying literal
    /// - `literals[1]` is unassigned or the next best choice for watching
    ///
    /// Returns the clause reference, or None if the clause is trivially SAT/UNSAT.
    pub fn add_theory_lemma(&mut self, mut literals: Vec<Literal>) -> Option<ClauseRef> {
        if literals.is_empty() {
            self.mark_empty_clause();
            return None;
        }

        // Remove duplicate literals and check for tautology
        literals.sort_by_key(|l| l.0);
        literals.dedup();

        // Bump VSIDS activity for variables in theory lemmas (#4919).
        // Without this, theory-relevant variables don't get prioritized in
        // the VSIDS decision heuristic. Boolean conflict analysis bumps
        // variables in learned clauses (conflict_analysis.rs:255), but
        // theory lemmas went through add_theory_lemma without bumping.
        // This causes the DPLL solver to spend decisions on low-activity
        // Boolean encoding variables instead of theory atoms, starving
        // the theory of conflicts and propagations.
        for lit in &literals {
            let var = lit.variable();
            if var.index() < self.num_vars {
                self.vsids.bump(
                    var,
                    &self.vals,
                    self.active_branch_heuristic != BranchHeuristic::Vmtf,
                );
            }
        }

        // Check for tautology (both x and ¬x)
        for i in 1..literals.len() {
            if literals[i].variable() == literals[i - 1].variable() {
                // Tautology - clause is always true
                return None;
            }
        }

        // All literal variables must be in range for safe assignment indexing.
        // Grow solver if extension produces out-of-range literals.
        {
            let max_var = literals
                .iter()
                .map(|l| l.variable().index())
                .max()
                .unwrap_or(0);
            if max_var >= self.num_vars {
                self.ensure_num_vars(max_var + 1);
            }
        }

        // Option C fail-close for #4492: LRAT cannot justify SMT theory lemmas
        // with SAT-resolution hints. Once theory lemmas appear, disable external
        // LRAT emission and rely on clause-trace/SMT proof paths instead.
        //
        // Preprocessing extensions (e.g., XOR Gauss-Jordan) classify equivalent
        // lemmas as TrustedTransform instead. ProofManager still suppresses and
        // fails closed on any such LRAT step without an explicit chain, because
        // serialized LRAT has no trusted-transform marker.
        if !self.cold.extension_trusted_lemmas {
            if let Some(ref mut manager) = self.proof_manager {
                if manager.is_lrat() {
                    manager.block_lrat_for_theory_lemmas();
                }
            }
        }

        // Handle unit clause
        if literals.len() == 1 {
            let lit = literals[0];
            let var = lit.variable();
            let value = self.var_value_from_vals(var.index());
            if value == Some(lit.is_positive()) && self.var_data[var.index()].level == 0 {
                // Already established permanently at root.
                return None;
            }

            // Every other unit must be stored. In particular, a true assignment
            // above root is retractable and an unassigned unit enqueued at the
            // current level has no watches that can restore it after backtrack.
            let idx = self.add_unscoped_theory_clause_db(&literals);
            self.provenance
                .tag(idx, crate::clause_provenance::ClauseProvenance::TheoryLemma);
            self.mark_subsume_dirty_if_kept(idx);
            let pid = self
                .proof_emit_add_prechecked(&literals, &[], self.theory_lemma_proof_kind())
                .unwrap_or(0);
            #[cfg(debug_assertions)]
            {
                self.cold.pending_forward_check = None;
            }
            let clause_ref = ClauseRef(idx as u32);
            let clause_id = self.clause_id(clause_ref);

            if value == Some(!lit.is_positive()) && self.decision_level == 0 {
                self.record_level0_conflict_chain(clause_ref);
                return None;
            }

            // The arena and proof-manager IDs are deliberately distinct for
            // hidden LRAT TrustedTransform additions. Preserve the emitted ID
            // until queued installation; clause-trace and suppressed-Axiom
            // modes fall back to the arena ID because `pid` is zero there.
            if pid != 0 && pid != clause_id {
                self.pending_theory_unit_proof_ids.push((clause_ref, pid));
            }

            if self.decision_level == 0 {
                debug_assert!(value.is_none());
                let installed = self.install_theory_unit_at_root(clause_ref);
                debug_assert!(installed);
                return Some(clause_ref);
            }

            // Queue before an optional immediate enqueue. The queue owns
            // mandatory callback-aware root installation for false, true
            // non-root, and unassigned unit axioms alike.
            self.pending_theory_conflicts.push_back(clause_ref);

            if value.is_none() {
                // Preserve immediate theory-propagation semantics. Above root,
                // the queued entry will subsequently re-install this at root.
                let proof_id = if pid != 0 { pid } else { clause_id };
                if proof_id != 0 {
                    self.record_unit_proof_id_for_lit(lit, proof_id);
                }
                self.enqueue(lit, None);
            }

            return Some(clause_ref);
        }

        // Reorder literals to find best watched literals.
        let watched = self
            .prepare_watched_literals(&mut literals, WatchOrderPolicy::AssignmentScore)
            .expect("theory lemma multi-literal path requires at least 2 literals");

        debug_assert!(
            literals.len() >= 2,
            "BUG: theory lemma multi-literal path reached with {} literals",
            literals.len(),
        );
        // Theory lemmas are axioms from the SMT layer, NOT derived
        // by SAT resolution. Use forward_check_derived=false so the
        // forward checker adds them as originals (not RUP-checked).
        let idx = self.add_unscoped_theory_clause_db(&literals);
        self.provenance
            .tag(idx, crate::clause_provenance::ClauseProvenance::TheoryLemma);
        // Theory lemmas default to LBD 0, which `reduce_permanent_protect_lbd`
        // protects permanently — so on instances that generate many lemmas
        // (eager EUF on QF_UF hardware-BMC) they accumulate without bound and
        // the search cannot converge in bounded memory (observed RSS -> 33 GB).
        // Give them a deletable (but still favored) LBD so `reduce_db` keeps the
        // database bounded; they are re-derivable theory axioms, and `reduce_db`
        // already protects in-use reason/proof clauses. (#perf; the former
        // `AY_THEORY_LEMMA_DELETABLE=0` legacy always-keep switch is removed —
        // deletable is the permanent default.)
        {
            let lbd = self.reduce_permanent_protect_lbd().saturating_add(1);
            self.arena.set_lbd(idx, lbd);
        }
        // Theory lemmas are always kept (LBD 0) — mark dirty (#7393).
        self.mark_subsume_dirty_if_kept(idx);
        // Write to proof to keep LRAT clause ID counters in sync (#4123).
        let _ = self.proof_emit_add_prechecked(&literals, &[], self.theory_lemma_proof_kind());
        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }
        let clause_ref = ClauseRef(idx as u32);

        // Set up watches on first two literals.
        self.attach_clause_watches(clause_ref, watched, literals.len() == 2);
        let (lit0, lit1) = watched;

        // Check if the clause is already falsified or unit
        let lit0_val = self.lit_value(lit0);
        let lit1_val = self.lit_value(lit1);

        if lit0_val == Some(false) && lit1_val == Some(false) {
            // All literals are false - conflict detected
            // Only set has_empty_clause at level 0 (original fix for #132).
            // At higher levels, this is a normal conflict - the XOR extension
            // (or other theories) may add conflict clauses at any level,
            // and we should backtrack normally rather than claim UNSAT.
            if self.decision_level == 0 {
                self.record_level0_conflict_chain(clause_ref);
            } else {
                // At level > 0, BCP won't discover this conflict because
                // both watched literals are already assigned — no trail event
                // will trigger watch propagation for this clause. Queue it so
                // the main solve loop can initiate conflict analysis (#6262).
                //
                // A theory callback may add a whole batch before returning to
                // the CDCL loop. Every all-false lemma is an independent live
                // conflict; overwriting a single pending slot would silently
                // drop all but the last and violate the conflict-free-trail
                // invariant before the next decision.
                self.pending_theory_conflicts.push_back(clause_ref);
            }
            return Some(clause_ref);
        } else if lit0_val.is_none() && lit1_val == Some(false) {
            // Unit clause - propagate lit0
            self.enqueue(lit0, Some(clause_ref));
        }

        Some(clause_ref)
    }

    /// Add a theory propagation directly to the trail without watch-list overhead (#4919).
    ///
    /// This is the lightweight counterpart to `add_theory_lemma`. It handles the
    /// common case where the theory knows a literal is implied (all reason literals
    /// are falsified, one literal is unassigned). Instead of adding the clause to
    /// the watch lists and waiting for BCP, this method:
    ///
    /// 1. Stores the clause in the arena (needed as reason during conflict analysis)
    /// 2. Directly enqueues the propagated literal on the trail
    /// 3. Skips watch-list attachment, VSIDS bumping, sort/dedup/tautology checks
    ///
    /// This matches Z3's `ctx().assign()` pattern for theory propagation where
    /// the literal goes directly to the trail with a lazy justification.
    ///
    /// # Arguments
    /// - `clause`: The full reason clause with the propagated literal as the FIRST
    ///   element. Format: `[propagated_lit, ¬reason₁, ¬reason₂, ...]`
    /// - `propagated`: The literal to enqueue (must equal `clause[0]`)
    ///
    /// Scope-aware twin of `add_theory_propagation` (#inc-scoped-lemmas): the
    /// positive scope selector is appended as an extra guard literal. Under
    /// the scope assumption (selector assumed false) the guard is falsified,
    /// so the reason-clause invariant (all non-propagated literals false)
    /// still holds; on pop the guarded clause is reclaimed with its scope
    /// instead of leaving a stale arena offset behind a live watch/reason.
    /// Identical to the unscoped call when no selectors exist.
    pub fn add_theory_propagation_scoped(
        &mut self,
        mut clause: Vec<Literal>,
        propagated: Literal,
    ) -> Option<ClauseRef> {
        if let Some(selector) = self.cold.scope_selectors.last().copied() {
            clause.push(Literal::positive(selector));
        }
        self.add_theory_propagation(clause, propagated)
    }

    /// # Safety invariant
    /// The caller must ensure:
    /// - `propagated` is unassigned
    /// - All other literals in `clause` are falsified under the current assignment
    /// - `propagated == clause[0]`
    pub fn add_theory_propagation(
        &mut self,
        mut clause: Vec<Literal>,
        propagated: Literal,
    ) -> Option<ClauseRef> {
        if clause.is_empty() {
            return None;
        }

        // Ensure propagated literal is at position 0 for correct reason extraction.
        // During conflict analysis, the solver reads reason[var] and uses literals[1..]
        // as the reason for the assignment. Position 0 is the asserted literal.
        if clause[0] != propagated {
            if let Some(pos) = clause.iter().position(|&l| l == propagated) {
                clause.swap(0, pos);
            } else {
                // propagated literal not in clause — fallback to full add_theory_lemma
                return self.add_theory_lemma(clause);
            }
        }

        debug_assert!(
            clause[0] == propagated,
            "BUG: add_theory_propagation: clause[0] != propagated"
        );

        // Normalize reason literals: remove duplicates and tautologies (#6506).
        // Theory solvers (e.g. LRA eager_row_bound_derivation) can produce
        // clauses with duplicate reason literals. Duplicates break the 2WL
        // invariant — initialize_watches() panics when both watch positions
        // hold the same literal.
        //
        // #7851 D3: Fast-path for already-deduplicated reasons.
        // LRA's collect_interval_reasons uses a `seen` HashSet (implied_interval.rs:156)
        // which guarantees no duplicates. Check with a linear scan first; only
        // fall through to the O(n log n) sort+dedup if duplicates are detected.
        // Z3 trusts theory reasons in its assign() path (arith_solver.cpp:1229-1241).
        if clause.len() >= 2 {
            // Fast duplicate/tautology check: O(n) scan before O(n log n) sort.
            let prop_var = propagated.variable();
            let mut needs_normalization = false;
            {
                // Check for prop_var in reason tail.
                for lit in &clause[1..] {
                    if lit.variable() == prop_var {
                        needs_normalization = true;
                        break;
                    }
                }
                // Check for duplicate literals in tail (pairwise scan).
                // For small tails (common case), this is cheaper than sort.
                if !needs_normalization && clause.len() <= 64 {
                    'outer: for i in 1..clause.len() {
                        for j in (i + 1)..clause.len() {
                            if clause[i].variable() == clause[j].variable() {
                                needs_normalization = true;
                                break 'outer;
                            }
                        }
                    }
                } else if !needs_normalization {
                    // For large clauses, fall back to sort-based detection.
                    needs_normalization = true;
                }
            }

            if needs_normalization {
                // Sort reason literals for dedup.
                clause[1..].sort_by_key(|l| l.0);
                // Remove consecutive duplicates in the tail only.
                let mut write = 1;
                for read in 2..clause.len() {
                    if clause[read] != clause[write] {
                        write += 1;
                        if write != read {
                            clause[write] = clause[read];
                        }
                    }
                }
                clause.truncate(write + 1);

                // Remove reason literals sharing a variable with propagated.
                // Same polarity = exact duplicate of propagated (redundant).
                // Opposite polarity = tautology → fall back to add_theory_lemma.
                if clause[1..]
                    .iter()
                    .any(|l| l.variable() == prop_var && *l != propagated)
                {
                    return self.add_theory_lemma(clause);
                }
                clause.retain(|l| *l == propagated || l.variable() != prop_var);

                // Check for tautologies among reason literals (same variable,
                // opposite polarity). After sort, same-variable literals are adjacent.
                for i in 2..clause.len() {
                    if clause[i].variable() == clause[i - 1].variable() {
                        return self.add_theory_lemma(clause);
                    }
                }
            }
        }

        // A length-1 propagation is an unconditional theory unit, not a
        // reasoned propagation. Route it through the unit-lemma path so
        // non-root assignments get mandatory callback-aware root handling
        // and the same proof provenance as every other theory unit.
        if clause.len() == 1 {
            return self.add_theory_lemma(clause);
        }

        // Fast check: if propagated literal is already assigned, skip or detect conflict.
        let var = propagated.variable();
        if var.index() >= self.num_vars {
            return None;
        }
        let val = self.vals[propagated.index()];
        if val > 0 {
            // Already true — propagation is redundant
            return None;
        }
        if val < 0 {
            // Already false — this is a conflict. Use full path for proper handling.
            return self.add_theory_lemma(clause);
        }

        // All literal variables must be in range
        debug_assert!(
            clause.iter().all(|l| l.variable().index() < self.num_vars),
            "BUG: add_theory_propagation: literal variable out of range"
        );

        // Reason literals (positions 1..n) must all be falsified under the
        // current assignment. If any reason literal is unassigned or satisfied,
        // the propagation reason is invalid for conflict analysis (#6262).
        // Fall back to add_theory_lemma which handles watches correctly.
        for lit in &clause[1..] {
            if self.lit_val(*lit) >= 0 {
                return self.add_theory_lemma(clause);
            }
        }

        // LRAT: block external LRAT for SMT theory lemmas.
        // Preprocessing extensions (XOR GJ) use trusted transforms (#7913).
        if !self.cold.extension_trusted_lemmas {
            if let Some(ref mut manager) = self.proof_manager {
                if manager.is_lrat() {
                    manager.block_lrat_for_theory_lemmas();
                }
            }
        }

        // Store clause in arena and set up watches (#6262).
        //
        // Originally this path skipped watch setup for speed. But without
        // watches, BCP cannot rediscover the clause after backtracking
        // undoes the propagation. This caused finalize_sat_model failures:
        // the clause sits in the DB, all literals false, no BCP trigger.
        //
        // With watches on clause[0] (propagated) and clause[1] (highest
        // false reason), BCP will re-discover unit propagation after
        // backtracking past the propagated literal's level.
        let idx = self.add_unscoped_theory_clause_db(&clause);
        self.provenance.tag(
            idx,
            crate::clause_provenance::ClauseProvenance::TheoryPropagation,
        );
        // Theory lemmas are always kept (LBD 0) — mark dirty (#7393).
        self.mark_subsume_dirty_if_kept(idx);
        let _ = self.proof_emit_add_prechecked(&clause, &[], self.theory_lemma_proof_kind());
        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }
        let clause_ref = ClauseRef(idx as u32);

        // Multi-literal: set up watches before enqueue.
        // clause[0] = propagated (about to be true), clause[1] = first reason (false).
        // This is the standard unit-propagation watch state.
        self.attach_clause_watches(clause_ref, (clause[0], clause[1]), clause.len() == 2);
        self.enqueue(propagated, Some(clause_ref));

        Some(clause_ref)
    }

    /// Add a lazy theory propagation to the trail without materializing the
    /// reason clause (#8467).
    ///
    /// Instead of allocating and storing the full reason clause in the arena,
    /// this method stores a lightweight `reason_data: u64` handle in the
    /// `lazy_theory_reasons` table and records the table index in `VarData.reason`
    /// with the `FLAG_LAZY_THEORY_REASON` flag set.
    ///
    /// The full reason clause is only materialized on demand during conflict
    /// analysis when `ReasonKind::LazyTheory(idx)` is encountered. ~90% of
    /// propagated variables are never resolved, so their reasons never need
    /// to be materialized.
    ///
    /// # Arguments
    /// - `propagated`: The literal to enqueue on the trail
    /// - `reason_data`: Theory-opaque u64 handle for lazy reason reconstruction
    ///
    /// # Safety invariant
    /// The caller must ensure `propagated` is currently unassigned.
    pub fn add_lazy_theory_propagation(&mut self, propagated: Literal, reason_data: u64) {
        let var = propagated.variable();
        if var.index() >= self.num_vars {
            return;
        }

        // Skip if already assigned
        let val = self.vals[propagated.index()];
        if val != 0 {
            return;
        }

        // Allocate a slot in the lazy_theory_reasons table
        let idx = self.cold.lazy_theory_reasons.len();
        debug_assert!(
            idx < u32::MAX as usize,
            "BUG: lazy_theory_reasons table overflow"
        );
        self.cold.lazy_theory_reasons.push(reason_data);
        self.cold.lazy_theory_propagated.push(propagated);
        let lazy_idx = idx as u32;

        // Enqueue with the lazy reason index stored in VarData.reason
        // and the FLAG_LAZY_THEORY_REASON flag set.
        let level = self.decision_level;
        let trail_pos = self.trail.len() as u32;
        let is_positive = propagated.is_positive();
        let var_idx = var.index();

        // Set literal value
        self.vals[propagated.index()] = 1;
        self.vals[propagated.negated().index()] = -1;

        // Phase saving (unless suppressed during vivification/lucky probing)
        if !self.suppress_phase_saving {
            self.phase[var_idx] = if is_positive { 1 } else { -1 };
        }

        // Set VarData with lazy reason flag.
        // The seen flag is intentionally NOT preserved: enqueue_lazy_theory_propagation
        // is called during BCP/propagation which occurs AFTER conflict analysis has
        // called clear(), so seen should always be 0. Preserving a stale seen flag
        // from a prior analysis would corrupt the resolvent_size accounting (#8511).
        self.var_data[var_idx] = VarData {
            level,
            trail_pos,
            reason: lazy_idx,
            flags: VarData::FLAG_LAZY_THEORY_REASON_PUB,
            _pad: [0; 3],
        };

        // Push to trail
        self.trail.push(propagated);
        self.num_propagations += 1;
    }

    /// Materialize a lazy theory reason using the given Extension (#8467).
    ///
    /// Reads the `reason_data` from `lazy_theory_reasons[lazy_idx]`, calls
    /// `Extension::explain_lazy_reason()` to get the full clause, stores it
    /// in the arena, and updates `VarData` to point to the new clause.
    ///
    /// Returns the `ClauseRef` of the materialized clause, or `None` if
    /// the reason could not be reconstructed (bound was retracted).
    pub(super) fn materialize_lazy_reason_with_ext(
        &mut self,
        lazy_idx: u32,
        ext: &mut dyn Extension,
        max_reason_level: Option<u32>,
    ) -> Option<ClauseRef> {
        let idx = lazy_idx as usize;
        debug_assert!(
            idx < self.cold.lazy_theory_reasons.len(),
            "BUG: lazy_idx {} out of bounds (len={})",
            idx,
            self.cold.lazy_theory_reasons.len()
        );

        let reason_data = self.cold.lazy_theory_reasons[idx];
        let propagated = self.cold.lazy_theory_propagated[idx];
        let propagated_level = self.var_data[propagated.variable().index()].level;

        let clause = ext.explain_lazy_reason(propagated, reason_data)?;

        if clause.is_empty() {
            return None;
        }

        // Store the materialized clause in the arena.
        // clause[0] must be the propagated literal.
        debug_assert!(
            clause[0] == propagated || clause.contains(&propagated),
            "BUG: materialized lazy reason does not contain propagated literal"
        );

        let mut clause = clause;
        // Ensure propagated is at position 0
        if clause[0] != propagated {
            if let Some(pos) = clause.iter().position(|&l| l == propagated) {
                clause.swap(0, pos);
            }
        }

        // Normalize reason literals: remove duplicates and reject tautologies
        // (#6506 parity with the eager add_theory_propagation_reason path).
        //
        // The lazy path stores the materialized clause directly as a
        // propagation reason (vd.reason), bypassing the eager path's
        // sort/dedup/tautology normalization. A theory explanation that
        // contains both `x` and `¬x` (e.g. `¬propagated` among the reason
        // literals, or two complementary reason literals) is TAUTOLOGICAL:
        // it is trivially true and does not actually justify the propagation.
        //
        // Storing such a clause as a reason corrupts the 2WL invariant
        // (duplicate variables at the two watch positions) and trips the
        // duplicate-variable canary in replace_clause_checked during the next
        // level-0 GC. In release builds (asserts off) the duplicate-variable
        // clause silently breaks watching and can produce WRONG UNSAT.
        //
        // Soundness: rejecting the lazy reason here (return None) demotes the
        // propagated variable to a decision in conflict analysis, which is
        // always sound (it only WEAKENS the learned clause). This mirrors the
        // existing reason-falsification guard below. A pure duplicate (same
        // polarity) is harmless and simply deduplicated; only a complementary
        // pair (tautology) forces rejection.
        if clause.len() >= 2 {
            // Fast O(n) scan for any repeated variable in the clause. The tail
            // is typically tiny and produced by collect_interval_reasons with a
            // `seen` set, so the common case is no repeats and we skip the
            // O(n log n) work entirely.
            let mut has_repeat_var = false;
            'scan: for i in 0..clause.len() {
                for j in (i + 1)..clause.len() {
                    if clause[i].variable() == clause[j].variable() {
                        has_repeat_var = true;
                        break 'scan;
                    }
                }
            }
            if has_repeat_var {
                // Sort the reason tail (keep propagated at position 0) so
                // same-variable literals become adjacent for dedup/tautology
                // detection. The propagated literal itself may also be checked
                // against the tail for the complementary case.
                clause[1..].sort_by_key(|l| l.0);
                // Reject if any reason literal is the negation of an earlier
                // literal (complementary pair = tautology). After sorting the
                // tail, complementary tail literals are adjacent; the
                // propagated literal (position 0) is compared against the tail
                // separately.
                let prop_var = propagated.variable();
                for &reason_lit in clause.iter().skip(1) {
                    // `¬propagated` among the reasons → tautology.
                    if reason_lit.variable() == prop_var && reason_lit != propagated {
                        self.cold.lazy_materialization_failed = true;
                        return None;
                    }
                }
                for i in 2..clause.len() {
                    if clause[i].variable() == clause[i - 1].variable()
                        && clause[i] != clause[i - 1]
                    {
                        // Complementary reason literals → tautology.
                        self.cold.lazy_materialization_failed = true;
                        return None;
                    }
                }
                // No tautology: remove exact-duplicate literals. After sorting
                // the tail, duplicates are adjacent. Also drop reason literals
                // that exactly equal the propagated literal (redundant).
                let mut write = 1;
                for read in 1..clause.len() {
                    let lit = clause[read];
                    if lit == propagated {
                        continue;
                    }
                    if write > 1 && clause[read] == clause[write - 1] {
                        continue;
                    }
                    clause[write] = lit;
                    write += 1;
                }
                clause.truncate(write);
                // Degenerate: all reason literals were duplicates of the
                // propagated literal, leaving a unit. A unit reason is not this
                // path's contract (no falsified premises to justify it); reject
                // and let conflict analysis treat the variable as a decision.
                if clause.len() < 2 {
                    return None;
                }
            }
        }

        let max_reason_level = max_reason_level
            .map(|level| level.min(propagated_level))
            .unwrap_or(propagated_level);

        // #8511: Reason falsification guard for lazy justification.
        //
        // The lazy path reconstructs reasons at conflict-analysis time via
        // explain_propagation() -> collect_interval_reasons(). Between
        // propagation time and materialization time, the theory state may have
        // changed (simplex pivots, implied bounds recomputed, new atoms
        // asserted). The reconstructed reasons may reference atoms that are
        // not currently falsified on the trail. Using such reasons in conflict
        // analysis produces over-constrained learned clauses that block valid
        // solutions, causing false UNSAT.
        //
        // This matches the #6262 falsification guard on the eager propagation
        // path in propagate_impl (extension/propagate.rs:1370).
        //
        // When a reason literal is not falsified, reject the entire lazy
        // reason (return None). The variable's VarData retains the lazy flag
        // and conflict analysis treats it as a decision, which is sound.
        for &reason_lit in clause.iter().skip(1) {
            if self.lit_val(reason_lit) >= 0 {
                // Reason literal is unassigned or satisfied — stale reason.
                // Reject this lazy materialization.
                return None;
            }
            let reason_level = self.var_data[reason_lit.variable().index()].level;
            if reason_level > max_reason_level {
                // A propagated assignment can survive any backtrack down to its
                // own level. Its stored reason must therefore be falsified by
                // literals no higher than the propagated assignment's level, and
                // no higher than any stricter caller-provided survivor level.
                return None;
            }
        }

        // LRAT: block external LRAT for theory lemmas.
        if !self.cold.extension_trusted_lemmas {
            if let Some(ref mut manager) = self.proof_manager {
                if manager.is_lrat() {
                    manager.block_lrat_for_theory_lemmas();
                }
            }
        }

        let arena_idx = self.add_unscoped_theory_clause_db(&clause);
        self.provenance.tag(
            arena_idx,
            crate::clause_provenance::ClauseProvenance::TheoryPropagation,
        );
        let _ = self.proof_emit_add_prechecked(&clause, &[], self.theory_lemma_proof_kind());
        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }
        let clause_ref = ClauseRef(arena_idx as u32);

        // Set up watches for the materialized clause.
        if clause.len() >= 2 {
            self.attach_clause_watches(clause_ref, (clause[0], clause[1]), clause.len() == 2);
        }

        // Update VarData to point to the real clause, clearing the lazy flag.
        let var_idx = propagated.variable().index();
        let vd = &mut self.var_data[var_idx];
        let seen_flag = vd.flags & VarData::FLAG_SEEN_PUB;
        vd.reason = arena_idx as u32;
        vd.flags = seen_flag; // Clear lazy flag, preserve seen
                              // Note: FLAG_BINARY_REASON is not set because this is a clause reason

        Some(clause_ref)
    }

    /// Pre-materialize lazy theory reasons at the current decision level (#8467, #8373).
    ///
    /// Called before conflict analysis so that 1UIP resolution never encounters
    /// unmaterialized lazy reasons. This avoids needing an Extension pointer
    /// during conflict analysis.
    ///
    pub(in crate::solver) fn materialize_current_level_lazy_reasons(
        &mut self,
        ext: &mut dyn Extension,
    ) {
        // Reset the sticky failure flag at each call so stale failures from
        // earlier conflicts do not bleed into the current analysis (#8707).
        self.cold.lazy_materialization_failed = false;
        let failed = self.materialize_lazy_reasons_for_level_range(
            ext,
            self.decision_level,
            true,
            Some(self.decision_level),
            Some(self.decision_level),
        );
        self.cold.lazy_materialization_failed = failed;
    }

    /// Materialize lazy reasons that will survive a backtrack to `target_level`.
    ///
    /// This runs before the extension pops theory scopes. It keeps lower-level
    /// SAT assignments from retaining opaque theory-local handles after
    /// chronological backtracking or trail-reuse restarts.
    pub(in crate::solver) fn materialize_lazy_reasons_through_level_for_backtrack(
        &mut self,
        ext: &mut dyn Extension,
        target_level: u32,
    ) {
        self.cold.lazy_materialization_failed = self.materialize_lazy_reasons_for_level_range(
            ext,
            target_level,
            false,
            Some(target_level),
            Some(target_level),
        );
    }

    /// Materialize all lazy reasons currently on the trail before an extension
    /// restart resets theory state. This is not immediately followed by 1UIP
    /// analysis, so failures only demote stale lazy handles and do not poison the
    /// next analysis.
    pub(in crate::solver) fn materialize_all_lazy_reasons_before_extension_restart(
        &mut self,
        ext: &mut dyn Extension,
    ) {
        let _ = self.materialize_lazy_reasons_for_level_range(
            ext,
            self.decision_level,
            false,
            None,
            Some(0),
        );
        self.cold.lazy_materialization_failed = false;
    }

    fn materialize_lazy_reasons_for_level_range(
        &mut self,
        ext: &mut dyn Extension,
        level: u32,
        exact_level_only: bool,
        fail_level: Option<u32>,
        max_reason_level: Option<u32>,
    ) -> bool {
        if self.cold.lazy_theory_reasons.is_empty() {
            return false;
        }
        // Walk the trail materializing selected lazy reasons.
        //
        // This is safe because:
        // 1. Materialization is idempotent (already-materialized reasons have
        //    their lazy flag cleared, so is_lazy_theory_reason() returns false).
        // 2. Backtrack callers materialize surviving levels before extension
        //    scopes are popped, preserving lazy handle ownership.
        let mut failed_at_fail_level = false;
        for trail_idx in 0..self.trail.len() {
            let lit = self.trail[trail_idx];
            let var_idx = lit.variable().index();
            let var_level = self.var_data[var_idx].level;
            if exact_level_only {
                if var_level != level {
                    continue;
                }
            } else if var_level > level {
                continue;
            }
            if self.var_data[var_idx].is_lazy_theory_reason() {
                let lazy_idx = self.var_data[var_idx].reason;
                if self
                    .materialize_lazy_reason_with_ext(lazy_idx, ext, max_reason_level)
                    .is_none()
                {
                    // Materialization failed: the theory could not reconstruct
                    // the reason (e.g., bounds were retracted by backtracking).
                    // Convert to a decision so conflict analysis handles it
                    // correctly instead of encountering an unmaterialized lazy
                    // reason and treating it as a decision WITHOUT clearing the
                    // lazy flag (#8511).
                    //
                    // Soundness: treating a propagated variable as a decision
                    // adds its negation to the learned clause instead of
                    // resolving through the (unavailable) reason. This makes
                    // the learned clause WEAKER (more literals = fewer pruned
                    // assignments), which is sound. The alternative — leaving
                    // the lazy flag set — causes conflict analysis to skip
                    // resolution, producing an overly STRONG clause that can
                    // prune valid solutions, causing false UNSAT.
                    let vd = &mut self.var_data[var_idx];
                    let seen_flag = vd.flags & VarData::FLAG_SEEN_PUB;
                    vd.reason = NO_REASON;
                    vd.flags = seen_flag; // Clear lazy flag, preserve seen
                    if fail_level == Some(var_level) {
                        failed_at_fail_level = true;
                    }
                }
            }
        }
        failed_at_fail_level
    }

    /// Clear lazy reason tables after solve returns (#8467).
    ///
    /// IMPORTANT: Must also clear FLAG_LAZY_THEORY_REASON on trail variables,
    /// otherwise resume_solving (which does NOT reset the trail) will encounter
    /// stale lazy flags pointing into the now-empty tables, causing
    /// index-out-of-bounds panics in materialize_lazy_reason_with_ext.
    pub fn clear_lazy_reason_tables(&mut self) {
        if !self.cold.lazy_theory_reasons.is_empty() {
            for trail_idx in 0..self.trail.len() {
                let lit = self.trail[trail_idx];
                let var_idx = lit.variable().index();
                let vd = &mut self.var_data[var_idx];
                if vd.is_lazy_theory_reason() {
                    vd.reason = NO_REASON;
                    vd.flags &= !VarData::FLAG_LAZY_THEORY_REASON_PUB;
                }
            }
        }
        self.cold.lazy_theory_reasons.clear();
        self.cold.lazy_theory_propagated.clear();
        self.cold.lazy_materialization_failed = false;
    }
}
