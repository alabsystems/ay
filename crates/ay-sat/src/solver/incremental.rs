// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving: push/pop scopes, value queries, trail access.

use super::*;

/// Assignment classification for external consumers (#8153).
///
/// Distinguishes how a variable received its truth value during CDCL search.
/// Used by the `ModelProvenance` explainability API to report whether each
/// variable was actively chosen by the branching heuristic or forced by
/// unit propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarAssignmentKind {
    /// Decided by CDCL branching heuristic (no reason clause).
    Decision,
    /// Propagated by BCP (has a reason clause or binary literal reason).
    Propagated,
    /// Not currently assigned on the trail.
    Unassigned,
}

impl Solver {
    /// Push a new assertion scope.
    ///
    /// Clauses added after a `push()` are scoped and removed by `pop()`, while
    /// learned clauses are retained.
    pub fn push(&mut self) {
        // Invalidate IC3 assumption cache (#8443): scope changes alter the
        // effective clause set.
        self.cold.assumption_cache_valid = false;

        // Permanently disable clause-deleting inprocessing techniques once
        // incremental mode is entered (#3662).
        self.disable_destructive_inprocessing();
        // Mark that push/pop has been used — original_ledger may
        // contain scope-selector clauses after pop() (#5077).
        self.cold.has_ever_scoped = true;

        // Force ghost literal guards in conflict analysis (#8489).
        // Incremental mode creates ghost-like variables: after pop() and
        // reset_search_state(), variables from popped scopes retain stale
        // var_data.level values while being unassigned. The JIT conflict
        // processor's vals[] filter catches most cases, but the Rust-side
        // bookkeeping must also guard against ghosts to prevent counter
        // inflation and u32 underflow in the ghost correction loop.
        // This is permanent — once set, ghost_guard_needed stays true.
        self.ghost_guard_needed = true;

        // Snapshot ledger size so pop() can truncate scoped clauses (#8472).
        // Must be recorded BEFORE any clauses are added in this scope.
        self.cold.original_ledger.push_scope();

        // Scoped BVE (#8369): snapshot num_vars BEFORE allocating the scope
        // selector variable.
        self.cold.scope_var_starts.push(self.num_vars);
        self.cold
            .scope_reconstruction_starts
            .push(self.inproc.reconstruction.len());

        let selector = self.new_var_internal();

        // Recompile JIT conflict processor if needed (#8489): new_var_internal()
        // grew var_data, but the conflict processor's compiled code has baked-in
        // buffer offsets. Recompile to match the new var count.
        //
        // STATUS (2026-07-14 triage): unlike the solver-start install path
        // (jit_compile.rs), which is double-gated on
        // AY_COMPETITION_JIT_MODE == "current" plus competition profile
        // metadata, this install path is gated only on cfg(feature = "jit")
        // and !jit_disabled (checked inside compile_conflict_processor).
        // It bypasses the env gate: on aarch64, an incremental push() can
        // engage the conflict JIT even when the competition profile says
        // off. Flagged as needing a deliberate decision — do not change
        // behavior without one. See
        // the development design notes
        #[cfg(feature = "jit")]
        self.compile_conflict_processor();

        let idx = selector.index();
        if idx >= self.cold.scope_selector_set.len() {
            self.cold.scope_selector_set.resize(idx + 1, false);
        }
        self.cold.scope_selector_set[idx] = true;
        // Permanently record this variable as a scope selector (#5522).
        // Unlike scope_selector_set (cleared on pop), was_scope_selector is
        // never cleared. Used by verify_against_original to skip scoped
        // clauses while still verifying base-formula clauses.
        if idx >= self.cold.was_scope_selector.len() {
            self.cold.was_scope_selector.resize(idx + 1, false);
        }
        self.cold.was_scope_selector[idx] = true;
        self.cold.scope_selectors.push(selector);
        // Register ¬selector as an LRAT axiom so the checker can verify
        // derivations that depend on assumption decisions (#7108).
        // The axiom consumes an LRAT ID; advance solver-side counters to
        // prevent subsequent add_clause from reusing the same ID.
        #[cfg(debug_assertions)]
        {
            let mut axiom_id = 0u64;
            if let Some(ref mut pm) = self.proof_manager {
                let neg_selector = Literal::negative(selector);
                axiom_id = pm.register_lrat_axiom(&[neg_selector]);
                if axiom_id != 0 {
                    if self.cold.next_original_clause_id <= axiom_id {
                        self.cold.next_original_clause_id = axiom_id + 1;
                    }
                    if self.cold.next_clause_id <= axiom_id {
                        self.cold.next_clause_id = axiom_id + 1;
                    }
                }
            }
            self.cold.scope_selector_axiom_ids.push(axiom_id);
        }
        self.freeze(selector);
        // Save forward checker state so it resumes active RUP checking after
        // pop(), even if this scope ends in UNSAT (#4481).
        self.forward_checker_push();
        self.emit_diagnostic_scope_push(selector, 0);
    }

    /// Pop the most recent assertion scope.
    ///
    /// Returns `false` if there is no active scope.
    #[must_use = "returns false if no scope was active"]
    pub fn pop(&mut self) -> bool {
        // Invalidate IC3 assumption cache (#8443).
        self.cold.assumption_cache_valid = false;

        let scope_depth_before = self.cold.scope_selectors.len();
        let Some(selector) = self.cold.scope_selectors.pop() else {
            return false;
        };
        #[cfg(debug_assertions)]
        self.cold.scope_selector_axiom_ids.pop();
        self.cold.scope_selector_set[selector.index()] = false;
        self.cold.scope_var_starts.pop();
        self.melt(selector);

        // Scoped BVE (#8369): restore variables eliminated during this scope.
        let scope_recon_start = self.cold.scope_reconstruction_starts.pop();
        if let Some(recon_start) = scope_recon_start {
            self.restore_scoped_bve_eliminations(recon_start);
        }

        // Clear has_empty_clause only if it was set *inside* the scope being
        // popped (or deeper). Base-level empty clauses (depth 0) are permanent
        // UNSAT and must survive every pop.
        let mut retracted_empty_clause = false;
        if self.has_empty_clause
            && self.cold.empty_clause_scope_depth > self.cold.scope_selectors.len()
        {
            // Retract the empty clause from the LRAT proof stream (Fix 2 of #4475).
            if let Some(ec_id) = self.cold.empty_clause_lrat_id.take() {
                let _ = self.proof_emit_delete(&[], ec_id);
            }
            self.has_empty_clause = false;
            self.cold.empty_clause_in_proof = false;
            retracted_empty_clause = true;
        }

        // #inc-pending-conflict: drop any undrained pending theory conflict
        // unconditionally (previously only cleared when retracting an empty
        // clause). The ref points at a clause that was all-false under the
        // popped scope's trail — gc_scoped_clauses below may delete that very
        // clause, and the next solve's arena rebuild invalidates the offset
        // entirely. reset_search_state also clears this at solve entry; this
        // clear additionally protects resume-style flows that skip the reset.
        self.pending_theory_conflict = None;

        // Restore forward checker state so it resumes active RUP checking
        // after a scoped UNSAT (#4481).
        self.forward_checker_pop();

        // Permanently disable clauses guarded by this selector, even if there
        // are still outer scopes active.
        let _ = self.add_clause_unscoped(vec![Literal::positive(selector)], false);

        // Reclaim memory from permanently-satisfied scoped clauses (#1444).
        // Clauses containing Literal::positive(selector) are satisfied once
        // the unit clause [+selector] propagates. Remove them eagerly so that
        // long incremental sessions don't accumulate dead clauses in the arena
        // and watch lists. This is the AY equivalent of Z3's gc_vars(max_var)
        // in sat_gc.cpp:403-462.
        self.gc_scoped_clauses(selector);

        // Sweep learned clauses that survived the scope-selector cleanup but
        // were derived during the popped scope (Z3 PR #9221). CDCL resolvents
        // may resolve away the scope-selector literal, leaving learned clauses
        // that carry no scope guard yet still reflect reasoning performed
        // inside the popped scope. Left in place, these clauses pollute watch
        // lists and bias VSIDS for subsequent proofs, producing the
        // prior-scope-dependent non-determinism described in Z3 #9220.
        //
        // Z3's implementation: `sat_solver::user_pop` (sat_solver.cpp, PR
        // #9221 diff) iterates `m_learned` and deletes clauses whose saturated
        // `scope_lim` exceeds the new scope depth. AY mirrors that: the new
        // scope depth equals `scope_selectors.len()` after the pop above.
        self.gc_leaked_learned_clauses();

        // Truncate the original ledger to remove clauses added during this
        // scope (#8472). This includes both the scoped clauses (with +selector
        // guard) and the [+selector] unit clause that pop() just added.
        // After truncation, the ledger accurately reflects only the clauses
        // that survive across scopes. The [+selector] unit and scoped clauses
        // remain in the live arena until the next rebuild, but the rebuild
        // will correctly reconstruct from the trimmed ledger.
        self.cold.original_ledger.pop_scope();
        // Keep incremental_original_boundary in sync with ledger size so that
        // reset_search_state does not attempt to re-add already-present clauses.
        self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();

        // Invalidate JIT conflict processor on pop (#8489): the scope may have
        // added variables (scope selectors) that changed num_vars. The conflict
        // processor's capacity was sized to the num_vars at compilation time.
        // After pop, the next solve will recompile if needed via
        // compile_conflict_processor(), but we must drop the stale processor
        // to prevent it from processing clauses with variable indices that
        // were valid during the scope but have stale var_data after pop.
        #[cfg(feature = "jit")]
        {
            self.jit_conflict_processor = None;
        }

        self.emit_diagnostic_scope_pop(scope_depth_before, selector, retracted_empty_clause);
        true
    }

    /// Get the current scope depth.
    ///
    /// Returns the number of active push() scopes.
    pub fn scope_depth(&self) -> usize {
        self.cold.scope_selectors.len()
    }

    /// Whether any push() scope is active with scoped BVE tracking (#8369).
    pub fn has_scoped_bve(&self) -> bool {
        !self.cold.scope_var_starts.is_empty()
    }

    /// Runtime precondition for disabling destructive inprocessing (#8162 Part A).
    ///
    /// Returns `true` when the solver is currently operating in an incremental
    /// context where destructive inprocessing (BVE, BCE, CCE, sweep, SBVA,
    /// congruence, factorize, decompose, condition, compaction, symmetry)
    /// would be unsound or unsound-to-reverse.
    ///
    /// Unlike the `has_been_incremental` permanent latch (which is set on
    /// the first `push()` and never cleared), `in_scoped_mode()` returns
    /// `false` once the solver has returned to scope depth 0 with no
    /// uncommitted scoped reconstruction state. This is the correct guard
    /// for inprocessing techniques that only require "no live scope right
    /// now" — not "no scope ever".
    ///
    /// During migration (Part A step 1), guard sites use
    /// `in_scoped_mode() || has_been_incremental` as a superset-OR so
    /// behavior is identical while the new query is exercised in tests.
    /// Once all 13 sites are migrated and benchmarks validate the change,
    /// the permanent flag is removed and only `in_scoped_mode()` remains.
    ///
    /// Reference: the development design notes §1.2.
    #[inline]
    pub(crate) fn in_scoped_mode(&self) -> bool {
        !self.cold.scope_selectors.is_empty() || self.has_uncommitted_scoped_state()
    }

    /// Structural witness: residual scoped state not yet drained.
    ///
    /// Briefly `true` during `pop()` between `scope_selectors.pop()` and
    /// the subsequent reconstruction-stack drain. The two `scope_*_starts`
    /// vectors are pushed/popped in lockstep with `scope_selectors` but are
    /// checked separately here as a defensive guard: if any of them is
    /// non-empty while `scope_selectors` is empty, the solver is mid-pop
    /// and destructive inprocessing must wait.
    #[inline]
    fn has_uncommitted_scoped_state(&self) -> bool {
        !self.cold.scope_reconstruction_starts.is_empty() || !self.cold.scope_var_starts.is_empty()
    }

    // NOTE (push/pop clause-leak): the former #8579 helpers
    // `set_scope_selector_vals_for_bve` / `restore_scope_selector_vals`
    // (which temporarily assigned scope selectors to their "scope-active"
    // polarity around BVE) were removed. Forcing vals[+S] = -1 made BVE's
    // root-false pruning strip the +S scope guard from resolvents, leaking
    // guardless irredundant clauses derived from scoped assertions across
    // pop(). Scope selectors must remain unassigned during inprocessing so
    // every derived clause inherits the guards of its parents. See
    // solve/inprocessing_incremental.rs for the full soundness analysis.

    /// Get the variable-index floor of the outermost active scope (#8369).
    pub fn scope_var_start(&self) -> Option<usize> {
        self.cold.scope_var_starts.first().copied()
    }

    /// Restore variables eliminated by BVE during the scope being popped (#8369).
    fn restore_scoped_bve_eliminations(&mut self, recon_start: usize) {
        if self.inproc.reconstruction.len() <= recon_start {
            return;
        }
        let drain_result = self
            .inproc
            .reconstruction
            .drain_witness_entries_from(recon_start);
        let reactivation_activity = self.vsids.current_increment();
        let mut reactivated_bve_vars = false;
        for &idx in &drain_result.reactivate_vars {
            if idx < self.var_lifecycle.len() && self.var_lifecycle.can_reactivate(idx) {
                self.var_lifecycle.reactivate(idx);
                self.inproc.bve.clear_removed_external(idx);
                let var = Variable(idx as u32);
                if self.vsids.activity(var) == 0.0 {
                    self.vsids.set_activity(var, reactivation_activity);
                }
                reactivated_bve_vars = true;
            }
        }
        if reactivated_bve_vars {
            self.inproc.bve.invalidate_occ_lists();
        }
    }

    /// Get the current assignment for a variable
    pub fn value(&self, var: Variable) -> Option<bool> {
        self.var_value_from_vals(var.index())
    }

    /// Get the current decision level
    ///
    /// Returns 0 at the root level, incremented after each decision.
    pub fn current_decision_level(&self) -> u32 {
        self.decision_level
    }

    /// Get the decision level at which a variable was assigned
    ///
    /// Returns None if the variable is unassigned.
    pub fn var_level(&self, var: Variable) -> Option<u32> {
        if self.var_is_assigned(var.index()) {
            Some(self.var_data[var.index()].level)
        } else {
            None
        }
    }

    /// Query whether a variable was decided or propagated (#8153).
    ///
    /// Returns `Decision` for variables chosen by the CDCL branching heuristic
    /// (no reason clause), `Propagated` for variables forced by unit propagation
    /// (has a reason clause or binary literal reason), and `Unassigned` for
    /// variables not on the trail.
    ///
    /// Part of the `ModelProvenance` explainability API.
    pub fn var_assignment_kind(&self, var: Variable) -> VarAssignmentKind {
        if !self.var_is_assigned(var.index()) {
            return VarAssignmentKind::Unassigned;
        }
        if self.var_data[var.index()].reason == NO_REASON {
            VarAssignmentKind::Decision
        } else {
            VarAssignmentKind::Propagated
        }
    }

    /// Get the variable indices from the reason clause of a propagated variable (#8307).
    ///
    /// For a propagated variable, returns the 0-based variable indices of the
    /// *other* literals in the reason clause (the antecedents that forced this
    /// assignment). Returns `None` for decision variables, unassigned variables,
    /// or if the reason clause is unavailable.
    ///
    /// For binary reason clauses, returns a single-element vec with the other
    /// literal's variable. For longer clauses, returns all variables except the
    /// propagated variable itself.
    ///
    /// Part of the `ModelProvenance` explainability API.
    pub fn var_reason_variable_indices(&self, var: Variable) -> Option<Vec<u32>> {
        use super::var_data::{binary_reason_lit, is_binary_literal_reason, NO_REASON};

        if !self.var_is_assigned(var.index()) {
            return None;
        }
        let vd = &self.var_data[var.index()];
        let reason = vd.reason;
        if reason == NO_REASON {
            return None; // decision variable
        }
        // Lazy theory reason (#8467, #8490): the `reason` field stores an index
        // into the `lazy_theory_reasons` table, NOT an arena offset. These reasons
        // were not materialized into clauses (only ~10% are needed during conflict
        // analysis). Return None — provenance is unavailable for lazy reasons.
        if vd.is_lazy_theory_reason() {
            return None;
        }
        if is_binary_literal_reason(reason) {
            // Binary clause: the other literal's variable index
            let other_lit = Literal(binary_reason_lit(reason));
            return Some(vec![other_lit.variable().index() as u32]);
        }
        // Clause reason: read literals from the arena, excluding the propagated var.
        // Guard against stale arena offsets (#8490): between-solve arena compaction
        // or rebuild can leave var_data[].reason pointing beyond the current arena.
        // This is a provenance-only API (ModelProvenance explainability), so returning
        // None for an unresolvable reason is safe — it means "antecedents unknown".
        let offset = reason as usize;
        if !self.arena.is_active(offset) {
            return None;
        }
        let lits = self.arena.literals(offset);
        let var_idx = var.index() as u32;
        let antecedents: Vec<u32> = lits
            .iter()
            .map(|lit| lit.variable().index() as u32)
            .filter(|&v| v != var_idx)
            .collect();
        Some(antecedents)
    }

    /// Get all currently assigned literals (the trail)
    ///
    /// Returns literals in assignment order. Useful for incremental
    /// theory solving where the theory needs to see partial assignments.
    pub fn trail(&self) -> &[Literal] {
        &self.trail
    }

    /// Get the number of assigned literals
    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }

    /// Restrict decisions and BCP to the given set of variables (#8430, #8475).
    ///
    /// When a domain is active:
    /// - The CDCL decision heuristic only picks branching variables from the domain
    /// - At decision level > 0, BCP uses domain-restricted propagation that skips
    ///   clauses where watched literals have variables outside the domain, unless
    ///   the configured domain-BCP formula-size breakpoint selects full BCP
    /// - At decision level 0, full BCP is used for complete unit propagation
    ///
    /// Designed for IC3/PDR queries where a small cube (5-50 variables) is
    /// checked against a transition system with thousands of variables.
    /// Domain-restricted BCP skips ~25x fewer clauses by treating non-domain
    /// watched literals as trivially satisfiable. GipSAT rIC3 reports 2-10x
    /// speedup on typical IC3 workloads.
    ///
    /// Call `clear_domain()` to remove the restriction. The domain is also
    /// automatically cleared at the start of each `solve()` call if desired.
    ///
    /// # Panics
    /// Panics if any variable index in `vars` is >= `num_vars`.
    pub fn set_domain(&mut self, vars: &[Variable]) {
        // IC3 fast path (#8569 Gap 1): use persistent bitmap buffer with
        // sparse clearing to avoid per-query vec![false; num_vars] allocation.
        // The bitmap is lazily grown to num_vars and cleared by tracking which
        // indices were set in the previous call.
        if self.cold.ic3_mode {
            self.set_domain_ic3_fast(vars);
            return;
        }

        let mut bitmap = vec![false; self.num_vars];
        for &var in vars {
            let idx = var.index();
            assert!(
                idx < self.num_vars,
                "set_domain: variable {idx} out of bounds"
            );
            bitmap[idx] = true;
        }

        // Store original domain for decision heuristics (#8661).
        self.decision_domain = Some(bitmap.clone());

        // Domain expansion (#8661): expand the domain bitmap to include all
        // variables that are transitively connected to domain variables through
        // clauses. This is the GipSAT approach (DagCnf cone-of-influence):
        // domain BCP skips clauses with non-domain unassigned watchers, but
        // those non-domain variables may be transitively constrained by domain
        // decisions. Missing these transitive propagations causes false UNSAT
        // (33/50 HWMCC soundness errors).
        //
        // Algorithm: BFS expansion — for each newly-added domain variable,
        // scan all clauses containing it and add all co-occurring variables.
        // Repeat until fixpoint.
        //
        // Performance: O(domain_size * avg_clauses_per_var * clause_len) per
        // fixpoint round. For typical IC3 queries (5-50 domain vars in a
        // 100-1000 var system), this is <1ms even with 10K clauses.
        self.expand_domain_bcp(&mut bitmap);

        self.active_domain = Some(bitmap);

        // Activate bucket-queue VSIDS for small domains (#8476, #8569 Gap 4).
        // In IC3 mode, always use the bucket queue regardless of domain size:
        // IC3 queries are short, so the O(1) bucket path wins even on larger
        // domains. Outside IC3 mode, use a threshold to avoid bucket overhead.
        // NOTE: bucket queue uses the ORIGINAL vars (not expanded domain) so
        // decisions are still restricted to the caller's intended variables.
        self.domain_restarts = 0;
        if vars.len() <= BUCKET_QUEUE_MAX_DOMAIN_SIZE {
            self.vsids.rebuild_bucket_queue_with_domain(vars);
            self.bucket_queue_active = true;
        } else {
            self.vsids.bucket_queue_clear();
            self.bucket_queue_active = false;
        }
    }

    /// IC3-optimized set_domain using persistent buffers (#8569 Gap 1).
    ///
    /// Avoids per-query allocations:
    /// - Uses `cold.ic3_domain_bitmap_buf` with sparse clearing instead of
    ///   `vec![false; num_vars]`
    /// - Caches the expanded domain result in `cold.ic3_domain_cache_expanded`
    ///   and reuses it when the input domain hash and clause DB boundary match
    /// - Avoids `bitmap.clone()` for `decision_domain` by building it in-place
    ///
    /// Total allocation: zero (all buffers are persistent and lazily grown).
    fn set_domain_ic3_fast(&mut self, vars: &[Variable]) {
        let nv = self.num_vars;

        // Sparse-clear the bitmap from the previous call.
        for &idx in &self.cold.ic3_domain_set_indices {
            if idx < self.cold.ic3_domain_bitmap_buf.len() {
                self.cold.ic3_domain_bitmap_buf[idx] = false;
            }
        }
        self.cold.ic3_domain_set_indices.clear();

        // Lazily grow bitmap to num_vars.
        if self.cold.ic3_domain_bitmap_buf.len() < nv {
            self.cold.ic3_domain_bitmap_buf.resize(nv, false);
        }

        // Set domain variables in the persistent bitmap.
        for &var in vars {
            let idx = var.index();
            debug_assert!(idx < nv, "set_domain: variable {idx} out of bounds");
            self.cold.ic3_domain_bitmap_buf[idx] = true;
            self.cold.ic3_domain_set_indices.push(idx);
        }

        // Build decision_domain (original domain, not expanded) using the
        // same persistent bitmap pattern. decision_domain is an Option<Vec<bool>>
        // so we must produce a Vec, but we reuse the capacity across calls.
        let mut dd = self.decision_domain.take().unwrap_or_default();
        dd.clear();
        dd.resize(nv, false);
        for &var in vars {
            dd[var.index()] = true;
        }
        self.decision_domain = Some(dd);

        // Domain expansion: check if cached result is still valid.
        // Cache is valid when:
        // 1. The clause DB boundary hasn't changed (no new clauses added)
        // 2. The input domain hash matches (same variables requested)
        let domain_hash = Self::hash_domain_vars(vars);
        let current_boundary = self.cold.incremental_original_boundary;
        let cache_valid = !self.cold.ic3_domain_cache_expanded.is_empty()
            && self.cold.ic3_domain_cache_boundary == current_boundary
            && self.cold.ic3_domain_cache_hash == domain_hash
            && self.cold.ic3_domain_cache_expanded.len() >= nv;

        if cache_valid {
            // Reuse cached expanded domain. Move it to active_domain.
            self.stats.ic3_domain_cache_hits += 1;
            let cached = std::mem::take(&mut self.cold.ic3_domain_cache_expanded);
            self.active_domain = Some(cached);
        } else {
            self.stats.ic3_domain_cache_misses += 1;
            // Need to expand. Build a fresh bitmap for expand_domain_bcp.
            // Reuse the existing active_domain allocation if possible.
            let mut bitmap = self.active_domain.take().unwrap_or_default();
            bitmap.clear();
            bitmap.resize(nv, false);
            for &var in vars {
                bitmap[var.index()] = true;
            }
            self.expand_domain_bcp(&mut bitmap);

            // Cache the result for next time.
            self.cold.ic3_domain_cache_expanded = bitmap.clone();
            self.cold.ic3_domain_cache_boundary = current_boundary;
            self.cold.ic3_domain_cache_hash = domain_hash;

            self.active_domain = Some(bitmap);
        }

        // Activate bucket-queue VSIDS (always in IC3 mode).
        self.domain_restarts = 0;
        self.vsids.rebuild_bucket_queue_with_domain(vars);
        self.bucket_queue_active = true;
    }

    /// Fast hash of domain variable set for cache invalidation.
    /// Uses FxHash-style multiply-xor accumulation. Order-independent.
    #[inline]
    fn hash_domain_vars(vars: &[Variable]) -> u64 {
        let mut h: u64 = vars.len() as u64;
        for &var in vars {
            // FxHash-style: multiply by a large odd constant and XOR.
            h ^= (var.index() as u64).wrapping_mul(0x517cc1b727220a95);
        }
        h
    }

    /// Expand the domain bitmap to include all variables transitively
    /// connected to domain variables through active clauses (#8661).
    ///
    /// This is the ay-sat equivalent of GipSAT's DagCnf cone-of-influence
    /// computation. Without this expansion, domain BCP can miss transitive
    /// propagation chains through non-domain variables, causing false UNSAT
    /// in IC3 consecution queries.
    ///
    /// Example: clauses `(~d0 | nd0)` and `(~nd0 | d1)` with domain={d0,d1}.
    /// Without expansion, domain BCP skips clause 1 (nd0 is non-domain,
    /// unassigned) and misses the chain d0→nd0→d1. With expansion, nd0 is
    /// added to the domain because it shares a clause with d0.
    fn expand_domain_bcp(&self, bitmap: &mut [bool]) {
        // Worklist of variables newly added to the domain in each round.
        let mut worklist: Vec<usize> = Vec::new();

        // Seed the worklist with the initial domain variables.
        for (idx, &in_domain) in bitmap.iter().enumerate() {
            if in_domain {
                worklist.push(idx);
            }
        }

        // BFS expansion over clauses.
        //
        // #8806: A clause is marked `absorbed` only once ALL of its variables
        // are in the domain. Marking a clause absorbed on first scan (when it
        // may have zero domain variables) is unsound: a later round can add a
        // variable to the domain via a binary watch (or another long clause),
        // and that clause must then be revisited to propagate domain
        // membership to its co-occurring variables. The prior implementation
        // used a `visited_clauses` bitmap keyed on first scan, which
        // permanently skipped such clauses and caused cone-of-influence
        // expansion to miss transitively connected variables. Downstream,
        // domain BCP's "unassigned non-domain treated as satisfied"
        // optimization would silently skip unit-propagation opportunities on
        // those clauses, producing false UNSAT in IC3 consecution.
        let mut absorbed_clauses: Vec<bool> = Vec::new(); // lazy init

        while !worklist.is_empty() {
            let mut next_worklist: Vec<usize> = Vec::new();

            // Phase 1: Scan binary clauses via watch lists.
            // For each variable in the worklist, check its positive and
            // negative literal watch lists for binary clause partners.
            for &var_idx in &worklist {
                for polarity in 0..2u32 {
                    let lit = Literal(var_idx as u32 * 2 + polarity);
                    let wl_len = self.watches.len_of(lit);
                    for w in 0..wl_len {
                        if self.watches.is_binary(lit, w) {
                            let partner = Literal(self.watches.blocker_raw(lit, w));
                            let partner_var = partner.variable().index();
                            if partner_var < bitmap.len() && !bitmap[partner_var] {
                                bitmap[partner_var] = true;
                                next_worklist.push(partner_var);
                            }
                        }
                    }
                }
            }

            // Phase 2: Scan long clauses in the arena.
            // Lazy-init the clause absorbed bitmap on first use.
            if absorbed_clauses.is_empty() && !self.arena.is_empty() {
                // Estimate clause count from arena capacity.
                let arena_word_len = self.arena.len();
                absorbed_clauses.resize(arena_word_len, false);
            }

            for offset in self.arena.active_indices() {
                if offset < absorbed_clauses.len() && absorbed_clauses[offset] {
                    continue; // All variables already in-domain — nothing to add.
                }

                let clause_len = self.arena.len_of(offset);
                if clause_len == 0 {
                    // Empty clause (should not occur post-simplification, but
                    // guard anyway). Safe to mark absorbed.
                    if offset < absorbed_clauses.len() {
                        absorbed_clauses[offset] = true;
                    }
                    continue;
                }

                // Single pass: determine whether the clause touches the domain,
                // and whether every variable is already in the domain.
                let mut has_domain_var = false;
                let mut all_in_domain = true;
                for i in 0..clause_len {
                    let lit = self.arena.literal(offset, i);
                    let vi = lit.variable().index();
                    if vi < bitmap.len() && bitmap[vi] {
                        has_domain_var = true;
                    } else {
                        all_in_domain = false;
                    }
                }

                if has_domain_var {
                    // Pull every variable in the clause into the domain.
                    for i in 0..clause_len {
                        let lit = self.arena.literal(offset, i);
                        let vi = lit.variable().index();
                        if vi < bitmap.len() && !bitmap[vi] {
                            bitmap[vi] = true;
                            next_worklist.push(vi);
                        }
                    }
                    // After this step every variable in the clause is in the
                    // domain, so no future round can extract more from it.
                    if offset < absorbed_clauses.len() {
                        absorbed_clauses[offset] = true;
                    }
                } else if all_in_domain {
                    // No domain var seen AND no var missing — only possible on
                    // zero-length clauses (already handled above) or a
                    // clause whose literals all fall outside `bitmap.len()`;
                    // safe to mark absorbed in either case.
                    if offset < absorbed_clauses.len() {
                        absorbed_clauses[offset] = true;
                    }
                }
                // Otherwise: clause has no domain var yet AND has vars outside
                // the domain. Leave it unabsorbed so later rounds can pick it
                // up when another clause brings one of its variables in.
            }

            worklist = next_worklist;
        }
    }

    /// Clear the domain restriction, reverting to normal decision heuristics.
    ///
    /// After clearing, all unassigned non-eliminated variables are eligible
    /// for branching decisions. The bucket queue is cleared since it is only
    /// useful during domain-restricted queries; non-restricted queries use
    /// the standard heap or VMTF heuristic.
    pub fn clear_domain(&mut self) {
        // IC3 fast path (#8569 Gap 1): move the active_domain Vec back to
        // the cache so it can be reused by the next set_domain_ic3_fast call
        // without reallocation. The cache validity (hash + boundary) was
        // already set during set_domain_ic3_fast.
        if self.cold.ic3_mode {
            if let Some(domain) = self.active_domain.take() {
                self.cold.ic3_domain_cache_expanded = domain;
            }
        } else {
            self.active_domain = None;
        }
        self.decision_domain = None;
        self.bucket_queue_active = false;
        self.domain_restarts = 0;
        self.vsids.bucket_queue_clear();
    }

    /// Configure the solver for IC3/PDR workloads (#8569).
    ///
    /// IC3 makes thousands of short incremental SAT queries per second, each
    /// with 5-50 domain variables in a system with hundreds-to-thousands of
    /// variables. The queries are individually tiny (often 0-5 conflicts), so
    /// per-call fixed costs dominate.
    ///
    /// `set_ic3_mode()` is a single entry point that disables all features
    /// unnecessary for IC3 queries, reducing per-query overhead from ~200us
    /// to <20us:
    ///
    /// This is the supported production entry point for IC3/PDR frame
    /// solvers. Call it once while constructing the frame solver: either
    /// immediately after `Solver::new()` and before adding clauses, or after
    /// installing permanent transition/frame clauses but before the first IC3
    /// query. The mode persists for the solver lifetime; do not re-enable
    /// preprocessing, proof logging, chronological backtracking, or
    /// inprocessing after selecting this profile.
    ///
    /// - **Inprocessing**: All techniques disabled (vivify, subsume, probe,
    ///   BCE, transred, sweep, condition, decompose, factor, sbva, congruence,
    ///   HTR, backbone, CCE, reorder, gate). Only scoped BVE remains enabled
    ///   and can run after `push()` for variables introduced in the active
    ///   scope (#8503).
    /// - **Preprocessing**: Disabled. IC3 queries are too small to benefit.
    /// - **LRAT proofs**: Disabled. IC3 doesn't need proof certificates.
    /// - **Chronological backtracking**: Disabled. Non-chrono BT is optimal
    ///   for the shallow decision trees in IC3 queries.
    /// - **DIP-ERCL**: Disabled. Extension variables add overhead for tiny
    ///   learned clauses.
    /// - **Cold restarts**: Disabled. IC3 uses its own Luby restart scheme.
    /// - **Lucky phases / walk / rephase / flip search**: Disabled. IC3 uses
    ///   forced phases from the PDR cube polarity.
    /// - **Bucket queue**: Enabled at query start via `set_domain()`, falls
    ///   back to heap after 10 restarts within a query (#8662 Gap 5).
    ///   Re-enabled at next query start by `set_domain()`. In IC3 mode,
    ///   `set_domain()` enables the bucket queue even for domains above the
    ///   normal non-IC3 threshold; the 10-restart fallback is intentionally
    ///   fixed rather than exposed as a tuning knob.
    /// - **Domain BCP breakpoint**: Defaults to full BCP below
    ///   `IC3_DOMAIN_BCP_MIN_VARS_DEFAULT` formula variables because the
    ///   domain-filter overhead dominates on small IC3/PDR queries (#8802).
    ///   Override with `set_domain_bcp_min_vars()`.
    ///
    /// After calling `set_ic3_mode()`, use `solve_incremental_ic3()` for
    /// queries and refresh `set_domain()` before each domain-restricted cube.
    /// Calling `disable_all_inprocessing()` before this method is harmless but
    /// redundant; this method applies the full IC3 profile itself.
    ///
    /// Reference: GipSAT (rIC3) design — IC3 SAT solver with ~2,449 LOC
    /// achieves <10us per query by having no broad inprocessing, zero proofs,
    /// and minimal per-solve reset. AY keeps the scoped-BVE exception for
    /// push/pop IC3/PDR queries.
    pub fn set_ic3_mode(&mut self) {
        self.cold.ic3_mode = true;

        // Disable all inprocessing (Gap 7).
        self.disable_all_inprocessing();

        // Disable preprocessing (Gap 7 supplement).
        self.cold.preprocess_enabled = false;

        // Disable LRAT proof logging (Gap 5 supplement — simplifies conflict
        // analysis by removing resolution chain collection).
        self.cold.lrat_enabled = false;

        // Scoped BVE (#8503): keep only BVE enabled in the IC3 profile. The
        // IC3 solve loop still guards the call with `has_scoped_bve()`, so
        // ordinary IC3 queries pay no BVE work and push/pop queries may
        // eliminate variables introduced inside the active scope.
        self.set_bve_enabled(true);

        // Disable chronological backtracking (Gap 5 — simplifies conflict
        // analysis and backtrack path).
        self.chrono_enabled = false;
        self.chrono_reuse_trail = false;
        // Disabling chrono means ghost literals from chrono-BT can't occur.
        // Ghost guard may still be needed for push/pop, so only disable if
        // push has never been used.
        if !self.cold.has_ever_scoped {
            self.ghost_guard_needed = false;
        }

        // DIP-ERCL (Gap 5): already skipped by the IC3 CDCL loop
        // (analyze_and_backtrack_ic3 never calls try_dip_ercl).

        // Disable cold restarts (IC3 uses Luby restarts internally).
        self.cold.cold_restart_enabled = false;

        // Disable lucky phases, walk, rephase, flip search.
        // IC3 uses forced phases via set_phase() for cube polarity.
        self.cold.rephase_enabled = false;
        self.cold.flip_search_enabled = false;

        // Lock to stable mode for consistent VSIDS (GipSAT pattern).
        self.cold.mode_lock = cold::ModeLock::Stable;
        self.stable_mode = true;
        self.sync_active_branch_heuristic();

        // Capture arena baseline for memory pressure tracking (#8673).
        // If the arena is empty (no clauses added yet), the baseline will
        // be captured on the first memory pressure check after clauses are
        // added. This handles both patterns: set_ic3_mode() before or after
        // adding the transition relation clauses.
        let arena_words = self.arena.len();
        if arena_words > 0 {
            self.cold.ic3_baseline_arena_words = arena_words;
        }
    }

    /// Check whether IC3 mode is active (#8569).
    pub fn is_ic3_mode(&self) -> bool {
        self.cold.ic3_mode
    }

    /// #lra-inc-engine (S1): mark this solver as the incremental QF_LRA engine
    /// lane's session-persistent solver, which forces the state-preserving
    /// incremental reset on every check-sat. This makes `add_clause_unscoped_inner`
    /// DEFER new-clause arena/watch attachment to the incremental reset's
    /// `attach_new_clauses_incremental` (so the delta clauses are watched and
    /// visible to BCP) and makes the extension reset paths take the incremental
    /// reset. Must be set together with `set_ic3_mode()` + `set_bve_enabled(false)`.
    /// Leaves the CHC/PDR IC3 path (ic3_mode WITHOUT this flag) untouched.
    pub fn set_inc_engine_reset_mode(&mut self, on: bool) {
        self.cold.inc_engine_reset_mode = on;
    }

    /// Set the constraint activation variable for lightweight IC3 constraints (#8662).
    ///
    /// GipSAT pattern (rIC3 gipsat/mod.rs:192-223): a single Boolean variable
    /// gates temporary constraint clauses. Instead of push/pop scopes (which
    /// allocate scope variables and run `gc_scoped_clauses` on pop), constrained
    /// clauses are added with `!constrain_act` prepended. At query time,
    /// `constrain_act = true` is included in assumptions to activate them.
    /// Between queries, old constrained clauses are trivially satisfied because
    /// `constrain_act` is not assumed (free to be false).
    ///
    /// The variable must already be allocated via `new_var()`. Typically called
    /// once during IC3 solver setup, after `set_ic3_mode()`.
    ///
    /// After calling this, use `add_constrained_clause()` to add temporary
    /// clauses and `solve_incremental_ic3()` will automatically include the
    /// activation literal in assumptions.
    ///
    /// # Panics
    /// Panics if `var` is out of bounds (>= num_vars).
    pub fn set_constrain_activation(&mut self, var: Variable) {
        assert!(
            var.index() < self.num_vars,
            "set_constrain_activation: variable {} out of bounds (num_vars={})",
            var.index(),
            self.num_vars
        );
        self.cold.ic3_constrain_act = Some(var);
        // Freeze the activation variable to protect it from elimination.
        self.freeze(var);
    }

    /// Get the constraint activation variable, if set (#8662).
    pub fn constrain_activation(&self) -> Option<Variable> {
        self.cold.ic3_constrain_act
    }

    /// Add a clause guarded by the constraint activation variable (#8662).
    ///
    /// The clause `[l1, l2, ..., ln]` is stored as `[!constrain_act, l1, l2, ..., ln]`.
    /// When `constrain_act = true` is assumed (during `solve_incremental_ic3`),
    /// `!constrain_act` is false, so the clause behaves as `[l1, l2, ..., ln]`.
    /// When `constrain_act` is not assumed, `!constrain_act` can be true,
    /// trivially satisfying the clause.
    ///
    /// This is the lightweight alternative to push/pop for IC3 temporary
    /// constraints. Old constrained clauses accumulate in the database but
    /// do not affect correctness since they are trivially satisfied when the
    /// activation is not assumed.
    ///
    /// # Panics
    /// Panics if `set_constrain_activation()` has not been called.
    pub fn add_constrained_clause(&mut self, literals: Vec<Literal>) -> bool {
        let act_var = self
            .cold
            .ic3_constrain_act
            .expect("add_constrained_clause: set_constrain_activation() not called");
        let guard = Literal::negative(act_var);

        // Build the guarded clause: [!act, l1, l2, ..., ln].
        let mut guarded = Vec::with_capacity(literals.len() + 1);
        guarded.push(guard);
        guarded.extend(literals);

        // Normalize: sort, dedup, tautology check.
        guarded.sort_by_key(|l| l.0);
        guarded.dedup();
        for i in 1..guarded.len() {
            if guarded[i].variable() == guarded[i - 1].variable() {
                return true; // Tautology — always satisfied
            }
        }
        if guarded.is_empty() {
            self.mark_empty_clause();
            return false;
        }

        // Mark that new clauses have been added (for incremental reset).
        self.cold.ic3_new_clauses_pending = true;

        // Record in original_ledger for full-reset rebuild path, but do NOT
        // defer arena addition. Constrained clauses need immediate arena
        // placement so we can track their offset for O(constraint_count)
        // cleanup.
        self.cold.original_ledger.push_clause(&guarded);
        self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
        self.cold.uniform_formula_cache = None;

        // Add directly to arena (bypass deferred path).
        let arena_offset = self.add_clause_db(&guarded, false);

        // Track the offset for O(constraint_count) cleanup (#8687).
        self.cold.ic3_constrained_offsets.push(arena_offset);

        // Attach watches for multi-literal clauses so BCP can see them
        // immediately. Unit/binary handling follows the same pattern as
        // attach_new_clauses_incremental.
        let clause_len = guarded.len();
        if clause_len >= 2 {
            let clause_ref = ClauseRef(arena_offset as u32);
            let lit0 = self.arena.literal(arena_offset, 0);
            let lit1 = self.arena.literal(arena_offset, 1);
            let is_binary = clause_len == 2;
            if !self.watches_disconnected {
                self.watches.watch_clause(clause_ref, lit0, lit1, is_binary);
            }
        }

        true
    }

    /// Add an IC3 lemma (blocking clause) to the clause database (#8662 Gap 6).
    ///
    /// IC3/PDR engines add blocking clauses between incremental SAT queries
    /// to encode reachability facts. Unlike standard learned clauses from
    /// CDCL conflict analysis, these lemmas are critical for IC3 correctness:
    /// deleting them can cause false UNSAT on consecution queries.
    ///
    /// Clauses added via this method are:
    /// - Marked with `IC3_LEMMA_BIT` in the clause header
    /// - Protected from `reduce_db` deletion (both normal and flush paths)
    /// - Protected from `between_solve_reduce` aging
    /// - Treated as irredundant (not learned) so they persist permanently
    ///
    /// GipSAT equivalent: `ClauseKind::Lemma` in the clause arena.
    ///
    /// For temporary constraint clauses that should be cleaned up periodically,
    /// use `add_constrained_clause()` instead.
    pub fn add_ic3_lemma(&mut self, literals: Vec<Literal>) -> bool {
        if literals.is_empty() {
            self.mark_empty_clause();
            return false;
        }

        // IC3 lemmas are added as irredundant (learned=false) because they
        // encode externally-proven facts that the IC3 engine depends on.
        // They must persist across incremental queries.
        let result = self.add_clause(literals);

        // Mark the most recently added arena clause as an IC3 lemma.
        // The clause was just added, so it is the last active clause in
        // the arena. Walk backwards from the arena end to find it.
        // Note: add_clause may reduce a multi-literal clause to a unit or
        // binary, in which case no arena entry exists to mark. This is fine:
        // unit/binary clauses are never deleted by reduce_db.
        if result {
            // Find the last active clause offset in the arena.
            // We walk the arena from the end to avoid O(n) full scan.
            // In practice, the last clause in the arena is the one we just added.
            let arena_len = self.arena.len();
            if arena_len > 0 {
                // The add_clause_db call returns the offset, but add_clause
                // goes through add_clause_unscoped which doesn't expose it.
                // Instead, note the last clause added: it's at the highest
                // offset in the arena. We can find it by walking active_indices
                // in reverse, but the simpler approach is to track the arena
                // length before and after.
                //
                // For correctness, we mark the clause BEFORE the next solve.
                // Since add_clause may normalize (dedup, tautology check) and
                // may produce a unit clause that's immediately propagated,
                // we check if the arena grew (a multi-literal clause was added).
                //
                // Track via ic3_pending_lemma_mark: set the last-added offset.
                // This is handled in the mark_last_clause_as_ic3_lemma helper.
                self.mark_last_clause_as_ic3_lemma();
            }
        }
        result
    }

    /// Mark the most recently added clause as an IC3 lemma.
    ///
    /// Walks backwards from the arena end to find the last active clause
    /// and sets its `IC3_LEMMA_BIT` flag.
    fn mark_last_clause_as_ic3_lemma(&mut self) {
        // The arena stores clauses contiguously. The last clause starts at
        // the highest offset that is still active. Since we just added a
        // clause, iterate from the end to find it efficiently.
        let mut last_active = None;
        for offset in self.arena.active_indices() {
            last_active = Some(offset);
        }
        if let Some(offset) = last_active {
            self.arena.set_ic3_lemma(offset, true);
        }
    }

    /// Remove constrained clauses in O(constraint_count) time (#8687).
    ///
    /// In IC3/PDR, constrained clauses are added with `!constrain_act` as a
    /// guard literal (via `add_constrained_clause`). Old constrained clauses
    /// accumulate in the database across queries. While they are trivially
    /// satisfied when `constrain_act` is not assumed, they still occupy arena
    /// space and inflate watch lists.
    ///
    /// This method uses tracked arena offsets (populated by
    /// `add_constrained_clause`) to directly delete constrained clauses
    /// without scanning the full arena. Complexity: O(constraint_count)
    /// instead of the previous O(arena_size).
    ///
    /// Should be called periodically between IC3 queries when memory
    /// pressure is a concern. Automatically backtracks to level 0 if
    /// the solver is at a higher decision level.
    ///
    /// Returns the number of clauses cleaned up.
    pub fn cleanup_constrained_clauses(&mut self) -> u64 {
        if self.cold.ic3_constrain_act.is_none() {
            return 0;
        }

        // Backtrack to level 0 if needed. Between IC3 queries, the solver
        // may still have decision-level assignments from the previous solve.
        // Cleanup must operate at level 0 to safely remove clauses.
        if self.decision_level > 0 {
            self.backtrack(0);
        }

        // O(constraint_count) path (#8687): use tracked arena offsets instead
        // of scanning the entire arena. `ic3_constrained_offsets` records every
        // arena offset added via `add_constrained_clause`.
        let to_delete: Vec<usize> = std::mem::take(&mut self.cold.ic3_constrained_offsets);

        if to_delete.is_empty() {
            return 0;
        }

        let mut deleted = 0u64;
        for offset in to_delete {
            if !self.arena.is_active(offset) {
                continue;
            }

            // Clean up watch entries for long clauses.
            if !self.watches_disconnected {
                let clause_len = self.arena.len_of(offset);
                if clause_len > 2 {
                    let (w0, w1) = self.arena.watched_literals(offset);
                    if w0.index() < self.dirty_watches.len() {
                        self.dirty_watches[w0.index()] = true;
                    }
                    if w1.index() < self.dirty_watches.len() {
                        self.dirty_watches[w1.index()] = true;
                    }
                }
                self.delete_binary_clause_watches(offset);
            }

            // Occ list maintenance.
            if let Some(ref mut gc_occ) = self.gc_occ {
                let lits = self.arena.literals(offset);
                gc_occ.remove_clause(offset, lits);
            }

            self.stats.clear_bcp_learned_1963_blocker_cert(offset);
            self.arena.delete(offset);
            self.cold.clause_db_changes += 1;
            deleted += 1;
        }

        if deleted > 0 && !self.watches_disconnected {
            self.flush_watches();
            self.stats.watches_shrunk += self.watches.shrink_watch_lists();
        }

        deleted
    }

    /// Lazily mark a clause as garbage for eventual removal (#8662 Gap 7).
    ///
    /// This is the IC3 lazy lemma removal API. When IC3 learns a new lemma
    /// that subsumes an older one, the caller marks the old clause as
    /// pending-garbage via this method. The clause is skipped by BCP
    /// (via `is_garbage_any()` checks) but its literal data is preserved
    /// until the next `reduce_db()` or `collect_level0_garbage()` pass
    /// fully deletes it.
    ///
    /// This matches GipSAT's `simplify.lazy_remove` pattern: the IC3 engine
    /// decides which clauses are subsumed; the SAT solver just marks and
    /// eventually collects them.
    ///
    /// # Arguments
    /// * `clause_ref` - The arena offset of the clause to mark. Must be
    ///   a valid, active clause reference (e.g., returned by
    ///   `add_clause_prenormalized_returning_offset`).
    ///
    /// # Returns
    /// `true` if the clause was marked, `false` if it was already dead
    /// or the offset is out of bounds.
    ///
    /// # Safety contract
    /// The clause must not be a current reason for any propagation at the
    /// time of marking. Callers should only mark clauses between solve
    /// calls (at decision level 0) where no clause is an active reason.
    ///
    /// Once marked, the clause is a "husk": it no longer participates in the
    /// live formula and is rejected by `clause_subsumes` as a subsumer.
    /// Callers implementing subsumption chains must therefore always test
    /// candidate deletions against a LIVE subsuming clause, not against a
    /// previously marked one (husk adjudication — transitivity through husks
    /// is not guaranteed by this API).
    pub fn mark_clause_garbage_lazy(&mut self, clause_ref: usize) -> bool {
        // Bounds check.
        if clause_ref >= self.arena.len() {
            return false;
        }
        // Already dead (deleted, garbage, or pending-garbage).
        if self.arena.is_dead(clause_ref) {
            return false;
        }
        // Mark as pending-garbage. BCP will skip it; reduce_db will delete it.
        self.stats.clear_bcp_learned_1963_blocker_cert(clause_ref);
        self.arena.set_pending_garbage(clause_ref, true);
        self.pending_garbage_count += 1;
        self.stats.ic3_lazy_removed += 1;
        true
    }

    /// Check if clause A subsumes clause B (A is a subset of B).
    ///
    /// Returns `true` if every literal in clause A also appears in clause B.
    /// Uses a signature prefilter for efficiency: `sig_A & sig_B == sig_A`
    /// is a necessary condition for subsumption. If the prefilter passes,
    /// performs an O(|A| * |B|) literal comparison.
    ///
    /// Both clause offsets must be valid live clauses: garbage or
    /// pending-garbage clauses ("husks") are rejected as either subsumer or
    /// subsumee (husk adjudication). NOTE on transitivity: if husk A was
    /// itself lazily removed because some live clause N subsumes A, then
    /// A ⊆ B would still justify removing B (N ⊆ A ⊆ B). That chain is only
    /// sound while the subsume-only workflow is respected; rather than rely
    /// on it, callers must test against the live subsumer N directly.
    ///
    /// This is a read-only helper that IC3 callers can use to detect
    /// subsumption before calling `mark_clause_garbage_lazy`.
    pub fn clause_subsumes(&self, a_offset: usize, b_offset: usize) -> bool {
        if a_offset >= self.arena.len() || b_offset >= self.arena.len() {
            return false;
        }
        if self.arena.is_dead(a_offset) || self.arena.is_dead(b_offset) {
            return false;
        }
        let a_len = self.arena.len_of(a_offset);
        let b_len = self.arena.len_of(b_offset);
        // A can only subsume B if |A| <= |B|.
        if a_len > b_len {
            return false;
        }
        // Signature prefilter: sig_A must be a subset of sig_B's bits.
        let sig_a = self.arena.signature(a_offset);
        let sig_b = self.arena.signature(b_offset);
        if sig_a & sig_b != sig_a {
            return false;
        }
        // Full literal subset check: every literal in A must appear in B.
        // O(|A| * |B|), acceptable for IC3's typically small clauses (5-50 lits).
        for i in 0..a_len {
            let lit_a = self.arena.literal_at(a_offset, i);
            let mut found = false;
            for j in 0..b_len {
                if self.arena.literal_at(b_offset, j) == lit_a {
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }
        true
    }

    /// Check whether a domain restriction is active.
    pub fn has_domain(&self) -> bool {
        self.active_domain.is_some()
    }

    /// Reclaim clauses permanently satisfied by a popped scope selector (#1444).
    ///
    /// After pop() adds the unit clause `[+selector]`, all clauses containing
    /// `Literal::positive(selector)` will be permanently satisfied once BCP
    /// propagates. This method eagerly removes them from the arena and watch
    /// lists so that long incremental sessions (thousands of push/pop cycles)
    /// do not accumulate dead clauses that waste memory and slow BCP.
    ///
    /// Reference: Z3 `gc_vars(max_var)` in `sat_gc.cpp:403-462` performs an
    /// equivalent cleanup by removing all clauses mentioning vars >= max_var.
    /// AY uses scope-selector guards instead of variable-range partitioning,
    /// so we scan for the specific selector literal.
    ///
    /// Guard: only runs at decision level 0 (the normal state between solves).
    /// If pop() is called at a higher level (unusual), the cleanup is deferred
    /// to the next `collect_level0_garbage` pass during the subsequent solve.
    ///
    /// Proof handling: scoped clauses are permanently satisfied, so they cannot
    /// appear as antecedents in any future derivation. We skip LRAT/DRAT proof
    /// emission for these deletions. The forward checker also skips them since
    /// the clauses are trivially implied once the selector unit is asserted.
    fn gc_scoped_clauses(&mut self, selector: Variable) {
        // Only run at level 0 where clause deletion is safe.
        if self.decision_level != 0 {
            return;
        }

        // Skip when LRAT proofs are active. Eagerly deleting scoped clauses
        // from the arena changes BCP/conflict paths, which can expose stale
        // cached proof IDs (unit_proof_id, level0_proof_id) from the retracted
        // scope. The regular collect_level0_garbage path handles these clauses
        // safely with proper LRAT ID re-derivation. Memory savings from eager
        // GC are not worth proof chain corruption risk (#1444).
        if self.cold.lrat_enabled {
            return;
        }

        let scope_lit = Literal::positive(selector);

        // Collect arena offsets of clauses containing the scope selector literal.
        // Skip unit clauses: the unit clause [+selector] added by pop() itself
        // must survive — it's what permanently disables the scope. Only multi-
        // literal clauses (the actual scoped assertions like `a | b | +sel`)
        // are reclamation targets.
        // Two-pass: collect first, delete second — avoids borrowing issues since
        // arena mutation invalidates iterators.
        let mut to_delete: Vec<usize> = Vec::new();
        for clause_idx in self.arena.active_indices() {
            let lits = self.arena.literals(clause_idx);
            if lits.len() >= 2 && lits.contains(&scope_lit) {
                to_delete.push(clause_idx);
            }
        }

        if to_delete.is_empty() {
            return;
        }

        // Ensure reason clause marks are current before deletion.
        self.ensure_reason_clause_marks_current();

        let mut reclaimed = 0u64;
        for clause_idx in to_delete {
            if !self.arena.is_active(clause_idx) {
                continue;
            }

            // Reason-protected clauses: a scoped clause containing +selector
            // may still be an active reason for a level-0 propagation. Clear
            // the reason reference before deletion.
            if self.is_reason_clause_marked(clause_idx) {
                let cref = ClauseRef(clause_idx as u32);
                let clause_len = self.arena.len_of(clause_idx);
                let mut cleared_any = false;
                for i in 0..clause_len {
                    let lit = self.arena.literal(clause_idx, i);
                    let vi = lit.variable().index();
                    if vi < self.num_vars
                        && self.var_data[vi].reason == cref.0
                        && self.var_data[vi].level == 0
                    {
                        self.var_data[vi].reason = NO_REASON;
                        cleared_any = true;
                    }
                }
                if cleared_any {
                    self.bump_reason_graph_epoch();
                    self.ensure_reason_clause_marks_current();
                }
            }

            // Binary watcher cleanup: unlink binary watches eagerly so BCP
            // hot paths can skip clause liveness checks (#4924).
            if !self.watches_disconnected {
                self.delete_binary_clause_watches(clause_idx);
            }
            // Long-clause watchers: mark watched literals dirty for lazy
            // flush_watches cleanup (#8101).
            if !self.watches_disconnected {
                let clause_len = self.arena.len_of(clause_idx);
                if clause_len > 2 {
                    let (w0, w1) = self.arena.watched_literals(clause_idx);
                    let dw = &mut self.dirty_watches;
                    if w0.index() < dw.len() {
                        dw[w0.index()] = true;
                    }
                    if w1.index() < dw.len() {
                        dw[w1.index()] = true;
                    }
                }
            }

            // Occ list maintenance.
            if let Some(ref mut gc_occ) = self.gc_occ {
                let lits = self.arena.literals(clause_idx);
                gc_occ.remove_clause(clause_idx, lits);
            }

            // BVE occ list notification (#8363): scoped clause deletion must
            // update persistent BVE occ lists for irredundant clauses.
            // Without this, BVE occ lists retain stale entries for deleted
            // scoped clauses across incremental solve rounds.
            if !self.arena.is_learned(clause_idx) {
                let lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();
                self.note_irredundant_clause_removed_for_bve(clause_idx, &lits);
            }

            // JIT incremental cache (#8225): mark variables in deleted clause
            // as dirty so the next solve's delta recompilation regenerates
            // their functions.
            //
            // Scope-aware optimization (#8392): skip dirty marking when the
            // JIT formula contains only base (scope-0) clauses. Since scoped
            // clauses were excluded from compilation, deleting them during
            // pop() does not affect any compiled code — no recompilation needed.

            // Delete from arena WITHOUT proof emission. Scoped clauses are
            // permanently satisfied and cannot participate in future derivations.
            // Their LRAT IDs are intentionally retained in known_lrat_ids so
            // that derivation chains referencing them remain valid.
            self.stats.clear_bcp_learned_1963_blocker_cert(clause_idx);
            self.arena.delete(clause_idx);
            self.cold.clause_db_changes += 1;
            reclaimed += 1;
        }

        self.cold.scoped_clauses_reclaimed += reclaimed;
    }

    /// Delete learned clauses whose recorded learn-time scope depth exceeds
    /// the current (post-pop) scope depth (Z3 PR #9221).
    ///
    /// `add_clause_db_checked` stamps each learned clause with
    /// `self.cold.scope_selectors.len()` at creation, saturated at 3. After a
    /// `pop()`, any learned clause whose stamp is strictly greater than the
    /// new depth was derived inside the popped scope (or deeper) and may
    /// encode reasoning that no longer follows from the surviving clause set.
    /// Z3's postcondition: these clauses are detached and deleted.
    ///
    /// Saturation caveat: because `scope_lim` is stored in 2 bits, values
    /// 3, 4, 5, ... all map to 3. When the new scope depth is >= 3 we cannot
    /// distinguish clauses learned at the current level from those learned
    /// deeper, so the sweep is skipped. This matches the Z3 behavior (see
    /// the `old_sz < 3` guard in the PR #9221 diff) — the common 1–2 level
    /// nesting cases are handled precisely.
    ///
    /// Guard: only runs at decision level 0 and skipped under LRAT to avoid
    /// perturbing proof chains (matches `gc_scoped_clauses` policy).
    fn gc_leaked_learned_clauses(&mut self) {
        if self.decision_level != 0 {
            return;
        }
        // The IC3 mode uses domain-restricted queries and manages learned
        // clauses externally; skip to avoid interfering with its lemma store.
        if self.cold.ic3_mode {
            return;
        }
        let new_depth = self.cold.scope_selectors.len();
        // Saturation boundary: stamps 3+ are indistinguishable.
        if new_depth >= crate::clause_arena::SCOPE_LIM_MAX as usize {
            return;
        }
        // LRAT soundness: preserve proof chains for learned clauses that may
        // be referenced by later derivations.
        if self.cold.lrat_enabled {
            return;
        }

        // Collect offsets of learned clauses with scope_lim > new_depth.
        // Two-pass: collect first, delete second to avoid iterator invalidation.
        let new_depth_u16 = new_depth as u16;
        let mut to_delete: Vec<usize> = Vec::new();
        for clause_idx in self.arena.active_indices() {
            if !self.arena.is_learned(clause_idx) {
                continue;
            }
            // IC3 lemmas are protected — they encode externally-proven
            // reachability facts and must persist across queries.
            if self.arena.is_ic3_lemma(clause_idx) {
                continue;
            }
            if self.arena.scope_lim(clause_idx) > new_depth_u16 {
                to_delete.push(clause_idx);
            }
        }

        if to_delete.is_empty() {
            return;
        }

        // Ensure reason marks are current before deletion so we can safely
        // detach any clauses still referenced by level-0 propagations.
        self.ensure_reason_clause_marks_current();

        let mut reclaimed = 0u64;
        for clause_idx in to_delete {
            if !self.arena.is_active(clause_idx) {
                continue;
            }

            // Clear any stale reason references. A leaked learned clause
            // should not be a reason at level 0 (pop_to_base_level drops the
            // trail), but defensively clear to match the existing
            // gc_scoped_clauses contract.
            if self.is_reason_clause_marked(clause_idx) {
                let cref = ClauseRef(clause_idx as u32);
                let clause_len = self.arena.len_of(clause_idx);
                let mut cleared_any = false;
                for i in 0..clause_len {
                    let lit = self.arena.literal(clause_idx, i);
                    let vi = lit.variable().index();
                    if vi < self.num_vars
                        && self.var_data[vi].reason == cref.0
                        && self.var_data[vi].level == 0
                    {
                        self.var_data[vi].reason = NO_REASON;
                        cleared_any = true;
                    }
                }
                if cleared_any {
                    self.bump_reason_graph_epoch();
                    self.ensure_reason_clause_marks_current();
                }
            }

            // Detach watches so BCP hot paths don't trip on a deleted clause.
            if !self.watches_disconnected {
                self.delete_binary_clause_watches(clause_idx);
                let clause_len = self.arena.len_of(clause_idx);
                if clause_len > 2 {
                    let (w0, w1) = self.arena.watched_literals(clause_idx);
                    let dw = &mut self.dirty_watches;
                    if w0.index() < dw.len() {
                        dw[w0.index()] = true;
                    }
                    if w1.index() < dw.len() {
                        dw[w1.index()] = true;
                    }
                }
            }

            // Occ list maintenance.
            if let Some(ref mut gc_occ) = self.gc_occ {
                let lits = self.arena.literals(clause_idx);
                gc_occ.remove_clause(clause_idx, lits);
            }

            self.stats.clear_bcp_learned_1963_blocker_cert(clause_idx);
            self.arena.delete(clause_idx);
            self.cold.clause_db_changes += 1;
            reclaimed += 1;
        }

        if reclaimed > 0 {
            self.stats.leaked_learned_clauses_gc_removed += reclaimed;
        }
    }
}
