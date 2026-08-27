// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Eager DPLL(T) theory extension
//!
//! This module provides a wrapper that implements the SAT solver's `Extension`
//! trait using a `TheorySolver`. This enables eager theory propagation during
//! SAT search instead of waiting for a complete model.
//!
//! # Architecture
//!
//! The `TheoryExtension` wrapper:
//! 1. Tracks SAT assignments incrementally via `propagate()` callback
//! 2. Feeds new assignments to the theory solver
//! 3. Queries the theory for propagations
//! 4. Converts theory propagations to SAT clauses
//! 5. Handles backtracking incrementally via push/pop
//!
//! # Performance Benefit
//!
//! For benchmarks like eq_diamond where transitivity propagations are critical,
//! eager propagation can dramatically reduce the search space by pruning
//! branches early rather than waiting to discover conflicts on complete models.

use ay_core::TheorySolver;
use ay_sat::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};
use ay_sat::{Literal, Variable};

mod context_derivation;
mod types;
pub(crate) use types::CachedExtensionData;
pub(crate) use types::TheoryAxiomKey;
pub(crate) use types::TheoryExtension;
use types::{BoundRefinementHandoff, ProofContext, UNASSIGNED_NIL};

impl<T: TheorySolver> Extension for TheoryExtension<'_, T> {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.propagate_impl(ctx)
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.check_impl(ctx)
    }

    fn backtrack(&mut self, new_level: u32) {
        if self.debug {
            safe_eprintln!(
                "[EAGER] Backtracking from theory level {} to SAT level {}",
                self.theory_level,
                new_level
            );
        }

        // Pop theory scopes to match the new SAT decision level.
        // Restore last_trail_pos from the saved stack so propagate() only
        // re-processes genuinely new assignments (#5548).
        while self.theory_level > new_level {
            let from_level = self.theory_level;
            self.theory.pop();
            self.theory_level -= 1;
            self.last_trail_pos = self.level_trail_positions.pop().unwrap_or(0);
            if let Some(diag) = self.diagnostic_trace {
                diag.emit_pop(from_level, self.theory_level);
            }
            if self.debug {
                safe_eprintln!("[EAGER] Pop to theory level {}", self.theory_level);
            }
        }
        // Reset theory-aware branching scan index on backtrack.
        // Previously decided theory atoms may have been unassigned, so we
        // must re-scan from the start to find unassigned ones.
        self.theory_decision_idx.set(0);
        // #skip-assigned: the backjump may have unassigned theory vars, so the
        // free-list is stale — force a rebuild on the next suggest_decision.
        self.unassigned_dirty.set(true);
        self.pending_bound_refinements.clear();
        // #4919: Reset batching state on backtrack — theory state changed.
        // Preserving the streak caused false-UNSAT on sat benchmarks (sc-6,
        // sc-8, vpm2-30): the streak triggered batching that deferred theory
        // checks, allowing SAT to accept theory-inconsistent assignments.
        self.zero_propagation_streak = 0;
        self.deferred_atom_count = 0;
        // #8125 / #uflia-deferred-atom-loss: drop ONLY the ITE-deferred atoms
        // whose SAT assignment is being undone (level > new_level). Entries at
        // levels <= new_level are STILL ASSIGNED in the SAT trail after the
        // backjump; SAT never re-notifies surviving assignments, so clearing
        // them here permanently hid the atoms from the theory — the combined
        // final check then accepted models violating them (EufLaArithmetic
        // hard* false-model accepts that only the strict ite_uf_definition
        // gate caught). Retained entries are (re)flushed by `check_impl()`;
        // the flush re-checks each guard, so an inactive-branch entry is
        // never asserted prematurely, and re-asserting an already-seen atom
        // in a lower scope is sound (same literal, same polarity).
        self.ite_deferred_atoms.retain_mut(|entry| {
            if entry.2 <= new_level {
                // The theory scope holding a prior flush may have been popped;
                // clear the flag so the next check re-asserts.
                entry.3 = false;
                true
            } else {
                false
            }
        });
        // Reset can_propagate scan position — trail has shrunk.
        self.can_propagate_scan_pos.set(0);
        // Reset BCP atom batch counter on backtrack.
        self.pending_theory_atoms_for_batch.set(0);
        // #8255: Reset atoms-since-check counter on backtrack.
        self.atoms_since_last_check = 0;
    }

    fn init(&mut self) {
        // #2138: Use soft_reset() instead of reset() to preserve learned theory
        // state (HNF cuts, Diophantine analysis, cached atom parses) across SAT
        // solver restarts. The SAT solver calls init() on every restart, and a
        // full reset() discards valuable learned state that took many theory
        // checks to accumulate. soft_reset() clears only assertion state while
        // retaining learned artifacts.
        self.theory.soft_reset();
        // Re-register theory atoms after soft_reset so the theory solver can
        // rebuild its atom index for bound propagation (#4919 RC2).
        for &atom in self.theory_atoms {
            self.theory.register_atom(atom);
        }
        self.last_trail_pos = 0;
        self.theory_level = 0;
        self.pending_split = None;
        self.level_trail_positions.clear();
        self.theory_decision_idx.set(0);
        // #skip-assigned: restart clears the SAT trail — rebuild the free-list.
        self.unassigned_dirty.set(true);
        self.can_propagate_scan_pos.set(0);
        self.ite_deferred_atoms.clear();
        // #8008: Reset deferred mode counters on full restart.
        self.total_bcp_checks = 0;
        self.total_bcp_conflicts = 0;
        self.total_bcp_propagations = 0;
        self.total_bcp_productive_prop_calls = 0;
        // #9224: deferred_theory_mode removed — field kept for struct compat.
        self.full_trail_deferral_active = false;
        self.theory_decision_call_count.set(0);
        self.pending_theory_atoms_for_batch.set(0);
        // #8255: Reset atoms-since-check counter on init.
        self.atoms_since_last_check = 0;
    }

    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        // Fast gate: skip propagate_impl() entirely when there is provably
        // no theory-relevant work to do. This avoids the overhead of
        // entering propagate_impl(), incrementing stats, and running the
        // theory check on BCP rounds that only propagated boolean-only
        // literals.
        //
        // Must return true when:
        // - Pending axiom clauses need injection
        // - New trail assignments include at least one theory atom
        // - Theory scope needs synchronization (push needed)
        // - First call (has_checked == false) for initial state
        // - Pending split needs the stop signal
        if !self.pending_axiom_clauses.is_empty() {
            return true;
        }
        if !self.has_checked {
            return true;
        }
        let sat_level = ctx.decision_level();
        if self.theory_level < sat_level {
            return true;
        }
        // Pending split with high repeat count needs the stop signal.
        if self.pending_split.is_some() && self.expr_split_seen_count >= 50 {
            return true;
        }
        // #8255/#8452: Gate on whether there are ANY new theory atoms since
        // the last call. The real batching logic lives in propagate_impl()
        // (streak-based deferral). Here we gate on presence of theory atoms
        // to avoid entering propagate_impl() for boolean-only BCP rounds.
        let trail = ctx.trail();
        let scan_from = self.last_trail_pos.max(self.can_propagate_scan_pos.get());
        if scan_from < trail.len() {
            let mut has_theory_atom = false;
            for &lit in &trail[scan_from..] {
                let id = lit.variable().id() as usize;
                let word_idx = id / 64;
                if word_idx < self.theory_var_bitset.len()
                    && (self.theory_var_bitset[word_idx] >> (id % 64)) & 1 != 0
                {
                    has_theory_atom = true;
                    break;
                }
            }
            self.can_propagate_scan_pos.set(trail.len());
            if has_theory_atom {
                self.pending_theory_atoms_for_batch.set(0);
                return true;
            }
        }
        false
    }

    fn suggest_decision(&self, ctx: &dyn SolverContext) -> Option<Literal> {
        // Theory-aware branching (#4919): decide theory atoms before encoding
        // variables. This matches Z3's theory_aware_branching which ensures all
        // theory atoms are decided before Tseitin encoding variables, giving the
        // theory solver maximum information for propagation.
        // Reference: Z3 smt_case_split_queue.cpp:1170-1209.
        //
        // Only enable for theories that explicitly support it (LRA/LIA/LIRA).
        // Theories with incomplete axiom generation (Seq, String, etc.) can
        // return false SAT when search order changes (#6236).
        if !self.theory.supports_theory_aware_branching() {
            return None;
        }
        // #9505: Adaptive theory decision frequency based on decision/conflict
        // ratio. On BMC/induction benchmarks (sc-21, simple_startup_6+, uart-21),
        // AY makes 20K+ decisions with <600 conflicts — the SAT solver wanders
        // aimlessly because VSIDS alone cannot steer toward theory-consistent
        // assignments. Z3 solves these in ~1963 decisions because its LP model
        // guides every decision.
        //
        // Static 1-in-2 (#8093) is insufficient for large induction formulas but
        // 1-in-1 regresses conflict-driven formulas like sc-8 (#8452 TL88).
        //
        // Solution: adapt the fraction dynamically. When decisions/conflicts > 10
        // (many decisions, few conflicts = SAT is wandering), use 1-in-1 to give
        // the theory maximum control. Otherwise, use 1-in-2 to let VSIDS drive
        // conflict-driven learning. This detects the BMC/induction pattern
        // automatically without user configuration.
        //
        // The warm-up period (100 decisions) ensures the ratio is stable before
        // adaptation. With 0 conflicts (common early in BMC search), default to
        // 1-in-1 since the theory model is likely consistent and should guide.
        //
        // Reference: Z3's theory_aware_branching always decides theory atoms first
        // (smt_case_split_queue.cpp:1170-1209) with LP-consistent phases.
        let count = self.theory_decision_call_count.get();
        self.theory_decision_call_count.set(count + 1);

        let decisions = ctx.decisions();
        let conflicts = ctx.conflicts();
        // #euf-search-quality: theories that opt into `wander_hand_to_vsids`
        // get the OPPOSITE wander response — once decisions/conflicts blows
        // past the threshold, stop steering for the rest of the solve (sticky
        // latch) and let VSIDS + phase saving drive. For EUF the historical
        // every-decision intensification below is catastrophic (NEQ027:
        // 140k conflicts / 138s vs 8.5k / 16s under VSIDS). The thresholds
        // (500-decision warm-up, ratio > 5) are deliberate: conflict-rich
        // solves (QG gensys family: ratio < 2 from the start) and quick
        // solves (< 500 decisions total) never latch and keep the in-order
        // theory-atom walk that dominates those families.
        let theory_every_decision = if self.theory.wander_hand_to_vsids() {
            if self.wander_latched.get() {
                return None;
            }
            if decisions > 500
                && decisions
                    .checked_div(conflicts)
                    .is_none_or(|ratio| ratio > 5)
            {
                self.wander_latched.set(true);
                self.wander_phase_clear_pending.set(true);
                return None;
            }
            // Never intensify to every-decision for these theories.
            false
        } else {
            // After a warm-up period, check the decision/conflict ratio.
            // High ratio = SAT is wandering, theory should guide every decision.
            // Low ratio = conflict-driven learning is productive, let VSIDS
            // dominate.
            decisions > 100
                && decisions
                    .checked_div(conflicts)
                    .is_none_or(|ratio| ratio > 10)
        };
        if !theory_every_decision && !count.is_multiple_of(2) {
            return None;
        }
        // #8445: clauseSMT arithmetic propagation branching. If the theory
        // has a high-priority atom to decide (blocked/fixed variable from
        // feasible-set analysis), decide it immediately. This takes precedence
        // over ITE conditions and activity-based selection because blocked vars
        // force early conflict detection and fixed vars eliminate search branches.
        if let Some((atom, phase)) = self.theory.suggest_decision_atom() {
            if let Some(&sat_var) = self.term_to_var.get(&atom) {
                let var = Variable::new(sat_var);
                if ctx.value(var).is_none() {
                    let lit = if phase {
                        Literal::positive(var)
                    } else {
                        Literal::negative(var)
                    };
                    return Some(lit);
                }
            }
        }
        // #8003: ITE condition priority - decide conditions before other atoms.
        if count.is_multiple_of(2) && !self.ite_condition_bitset.is_empty() {
            for word_idx in 0..self.ite_condition_bitset.len() {
                let word = self.ite_condition_bitset[word_idx];
                if word == 0 {
                    continue;
                }
                for bit in 0..64u32 {
                    if (word >> bit) & 1 == 0 {
                        continue;
                    }
                    let var_id = (word_idx * 64 + bit as usize) as u32;
                    let var = Variable::new(var_id);
                    if ctx.value(var).is_none() {
                        return Some(Literal::positive(var));
                    }
                }
            }
        }
        // #8420/#8452 TL88: Dual-mode theory atom selection.
        //
        // Mode A (even calls): Activity-based. Scan all atoms and pick the
        // one with the highest VSIDS activity that has a phase hint. This
        // focuses on contentious atoms that the SAT solver is also
        // interested in (high activity from recent conflicts).
        //
        // Mode B (odd calls): Round-robin. Pick the NEXT unassigned theory
        // atom with a phase hint, starting from the last scan position.
        // This ensures fresh theory atoms (low activity, haven't been in
        // conflicts yet) also get decided. Without this, atoms that
        // haven't participated in conflicts have zero activity and are
        // never selected by Mode A, even though deciding them might
        // enable a cascade of theory propagations.
        //
        // Z3's theory_aware_branching uses a priority queue ordered by
        // theory-assigned priority (not VSIDS activity), which gives a
        // similar effect to Mode B: atoms are decided in theory-determined
        // order, not conflict-history order.
        //
        // Atoms with None phase are left to VSIDS (#6303).
        // #suggest-decision-precompute: iterate the precomputed dense
        // (sat_var, atom) index instead of theory_atoms + a per-atom
        // term_to_var HashMap lookup. seed_index preserves theory_atoms order
        // and contains exactly the atoms that HAVE a term_to_var entry — i.e.
        // exactly the atoms the old per-atom `if let Some(..) = get(&atom)`
        // guard let through. So Mode A's max/tie-break and Mode B's round-robin
        // selection sequence are byte-identical, only faster (kills the 8227
        // self-time hash + Variable::new-from-hash on the hot loop).
        let atoms = &self.seed_index;
        // #9505: When in adaptive theory-every-decision mode, prefer round-robin
        // (Z3-style) over activity-based selection. Round-robin ensures all theory
        // atoms are decided sequentially, matching Z3's priority-queue approach.
        // Activity-based selection can repeatedly pick the same high-activity atom
        // while low-activity atoms go undecided on BMC/induction benchmarks.
        let use_activity_mode = if theory_every_decision {
            false // Always round-robin in BMC/induction mode
        } else {
            count % 4 < 2 // 50% activity, 50% round-robin (default)
        };

        // #skip-assigned (`AY_LRA_UNASSIGNED_SKIP`): O(unassigned) selection via
        // the intrusive free-list of currently-unassigned seed positions. Picks
        // the byte-identical literal the full scan below would — the free-list
        // threads the SAME unassigned atoms in the SAME ascending seed order, so
        // Mode A's max/first-tie and Mode B's cyclic-first-from-cursor are
        // reproduced exactly, only skipping the assigned atoms the full scan
        // would have visited and rejected via `ctx.value(..).is_none()`.
        if self.unassigned_skip {
            // Bring the free-list in sync with the SAT trail before walking it.
            // A dirty flag (set by backtrack()/init(), the only paths that
            // unassign theory vars) forces a full rebuild from ctx.value();
            // otherwise the trail has only grown, so incrementally unlink the
            // positions that became assigned since the last maintenance.
            if self.unassigned_dirty.get() {
                self.rebuild_unassigned_list(ctx);
            } else {
                self.advance_unassigned_scan(ctx);
            }
            let next = self.unassigned_next.borrow();
            let len = self.seed_index.len();
            if use_activity_mode {
                // Mode A: activity-based, highest-activity first-max wins ties.
                let mut best_lit: Option<Literal> = None;
                let mut best_activity: f64 = -1.0;
                let mut node = self.unassigned_head.get();
                while node != UNASSIGNED_NIL {
                    let (sat_var, atom) = self.seed_index[node as usize];
                    let var = Variable::new(sat_var);
                    // Free-list entries are unassigned by construction; the guard
                    // matches the full-scan filter exactly and is defense in depth
                    // against a stale list.
                    if ctx.value(var).is_none() {
                        if let Some(phase) = self.theory.suggest_phase(atom) {
                            let act = ctx.activity(var);
                            if act > best_activity {
                                best_activity = act;
                                let lit = if phase {
                                    Literal::positive(var)
                                } else {
                                    Literal::negative(var)
                                };
                                best_lit = Some(lit);
                            }
                        }
                    }
                    node = next[node as usize];
                }
                if best_lit.is_some() {
                    return best_lit;
                }
            } else {
                // Mode B: round-robin from the seed-position cursor. The list is
                // ascending by position; the cyclic order start..len-1 then
                // 0..start-1 is the tail portion (pos >= start) followed by the
                // head portion (pos < start).
                let start = self.theory_decision_idx.get();
                // Phase 1: positions >= start (list tail), ascending.
                let mut node = self.unassigned_head.get();
                while node != UNASSIGNED_NIL && (node as usize) < start {
                    node = next[node as usize];
                }
                while node != UNASSIGNED_NIL {
                    let (sat_var, atom) = self.seed_index[node as usize];
                    let var = Variable::new(sat_var);
                    if ctx.value(var).is_none() {
                        if let Some(phase) = self.theory.suggest_phase(atom) {
                            self.theory_decision_idx.set((node as usize + 1) % len);
                            let lit = if phase {
                                Literal::positive(var)
                            } else {
                                Literal::negative(var)
                            };
                            return Some(lit);
                        }
                    }
                    node = next[node as usize];
                }
                // Phase 2: wrap — positions < start (list head), ascending.
                let mut node = self.unassigned_head.get();
                while node != UNASSIGNED_NIL && (node as usize) < start {
                    let (sat_var, atom) = self.seed_index[node as usize];
                    let var = Variable::new(sat_var);
                    if ctx.value(var).is_none() {
                        if let Some(phase) = self.theory.suggest_phase(atom) {
                            self.theory_decision_idx.set((node as usize + 1) % len);
                            let lit = if phase {
                                Literal::positive(var)
                            } else {
                                Literal::negative(var)
                            };
                            return Some(lit);
                        }
                    }
                    node = next[node as usize];
                }
                self.theory_decision_idx.set(0);
            }
            return None;
        }

        if use_activity_mode {
            // Mode A: activity-based selection (original #8420 behavior).
            let mut best_lit: Option<Literal> = None;
            let mut best_activity: f64 = -1.0;
            for &(sat_var, atom) in atoms.iter() {
                let var = Variable::new(sat_var);
                if ctx.value(var).is_none() {
                    if let Some(phase) = self.theory.suggest_phase(atom) {
                        let act = ctx.activity(var);
                        if act > best_activity {
                            best_activity = act;
                            let lit = if phase {
                                Literal::positive(var)
                            } else {
                                Literal::negative(var)
                            };
                            best_lit = Some(lit);
                        }
                    }
                }
            }
            if best_lit.is_some() {
                return best_lit;
            }
        } else {
            // Mode B: round-robin sequential scan (Z3-style).
            let start = self.theory_decision_idx.get();
            for offset in 0..atoms.len() {
                let i = (start + offset) % atoms.len();
                let (sat_var, atom) = atoms[i];
                let var = Variable::new(sat_var);
                if ctx.value(var).is_none() {
                    if let Some(phase) = self.theory.suggest_phase(atom) {
                        self.theory_decision_idx.set((i + 1) % atoms.len());
                        let lit = if phase {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        };
                        return Some(lit);
                    }
                }
            }
            self.theory_decision_idx.set(0);
        }
        None
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        // If this is a theory atom, ask the theory solver for its
        // LP-model-consistent polarity (Z3's get_phase).
        let term = self.var_to_term.get(&var.id())?;
        if self.wander_latched.get() {
            // Wander-latched VSIDS mode (#euf-search-quality): general phase
            // steering is off; only theory-IMPLIED polarities pass through
            // (deciding the opposite would be an immediate theory conflict).
            return self.theory.suggest_phase_implied(*term);
        }
        self.theory.suggest_phase(*term)
    }

    fn seed_phase_hints(&self, phases: &mut [i8], vals: &[i8]) {
        // Bulk-seed theory-model-consistent phases into the SAT phase array.
        // For each unassigned theory atom, query the theory solver's current
        // model value and write it into phases[]. This creates the Z3-style
        // feedback loop where the LP/simplex model guides SAT phase selection.
        //
        // Only runs when the theory supports theory-aware branching (LRA/LIA/LIRA).
        if !self.theory.supports_theory_aware_branching() {
            return;
        }
        // Wander-latched VSIDS mode: stop overwriting saved phases. The first
        // seed after latching clears the pre-latch steering residue instead
        // (see `wander_phase_clear_pending`).
        if self.wander_latched.get() {
            if self.wander_phase_clear_pending.replace(false) {
                for &(sat_var_id, _) in &self.seed_index {
                    let idx = sat_var_id as usize;
                    if idx < phases.len() {
                        phases[idx] = 0;
                    }
                }
            }
            return;
        }
        // Walk the precomputed dense (sat_var, atom) index — no per-atom
        // term_to_var hashing. Bit-identical to the previous per-atom loop:
        // atoms with no SAT var were skipped there and are simply absent here.
        for &(sat_var_id, atom) in &self.seed_index {
            let idx = sat_var_id as usize;
            // Skip variables outside the phase array bounds
            if idx >= phases.len() {
                continue;
            }
            // Only seed unassigned variables. CaDiCaL-style vals:
            // vals[var_index * 2] is 0 for unassigned.
            let val_idx = idx * 2;
            if val_idx < vals.len() && vals[val_idx] != 0 {
                continue;
            }
            // Query theory model for suggested polarity
            if let Some(phase) = self.theory.suggest_phase(atom) {
                phases[idx] = if phase { 1 } else { -1 };
            }
        }
    }

    fn seed_phase_hints_dual(&self, phase: &mut [i8], target_phase: &mut [i8], vals: &[i8]) {
        // Single-pass variant: seed BOTH the saved-phase and target-phase
        // arrays from one walk of the dense index, querying suggest_phase once
        // per atom. seed_theory_phases calls this after every BCP/theory-prop
        // quiescence, so collapsing the two scans (and halving suggest_phase
        // calls + atom-index lookups) removes the dominant in-solver cost on
        // LRA/induction benchmarks. The per-array bounds/assignment filtering
        // matches seed_phase_hints exactly, so both arrays receive the same
        // values the two-scan version produced.
        if !self.theory.supports_theory_aware_branching() {
            return;
        }
        // Wander-latched VSIDS mode: stop overwriting saved phases. The first
        // seed after latching clears the pre-latch steering residue instead
        // (see `wander_phase_clear_pending`).
        if self.wander_latched.get() {
            if self.wander_phase_clear_pending.replace(false) {
                for &(sat_var_id, _) in &self.seed_index {
                    let idx = sat_var_id as usize;
                    if idx < phase.len() {
                        phase[idx] = 0;
                    }
                    if idx < target_phase.len() {
                        target_phase[idx] = 0;
                    }
                }
            }
            return;
        }
        // Epoch-skip: when the theory reports a phase-hint epoch unchanged since
        // our last seed, every suggest_phase(atom) returns the same value, so a
        // re-seed writes identical values for the atoms it touches — skip the
        // whole O(atoms) scan. Phase hints are a heuristic (branch-order bias,
        // never the sat/unsat result), so leaving the phase arrays as-is across
        // a skip can only change search order, not correctness. The A/B arm is
        // `AY_DISABLE_PHASE_EPOCH_SKIP` (see
        // `phase_hint::phase_epoch_skip_disabled`): default off, and setting it
        // restores the unconditional re-seed byte-for-byte. It was deleted once;
        // an optimisation without a control cannot have its premise re-checked.
        if !phase_hint::phase_epoch_skip_disabled() {
            if let Some(epoch) = self.theory.phase_hint_epoch() {
                if self.last_seed_epoch.get() == Some(epoch) {
                    return;
                }
                self.last_seed_epoch.set(Some(epoch));
            }
        }
        for &(sat_var_id, atom) in &self.seed_index {
            let idx = sat_var_id as usize;
            let val_idx = idx * 2;
            if val_idx < vals.len() && vals[val_idx] != 0 {
                continue;
            }
            let in_phase = idx < phase.len();
            let in_target = idx < target_phase.len();
            if !in_phase && !in_target {
                continue;
            }
            if let Some(p) = self.theory.suggest_phase(atom) {
                let v = if p { 1 } else { -1 };
                if in_phase {
                    phase[idx] = v;
                }
                if in_target {
                    target_phase[idx] = v;
                }
            }
        }
    }

    fn explain_lazy_reason(
        &mut self,
        propagated: Literal,
        reason_data: u64,
    ) -> Option<Vec<Literal>> {
        // #8467: Materialize a lazy theory reason on demand during conflict
        // analysis. Called by the SAT solver when it encounters a
        // ReasonKind::LazyTheory during 1UIP resolution.

        // Map SAT literal back to theory TermId.
        let var_id = propagated.variable().id();
        let term = *self.var_to_term.get(&var_id)?;

        // Ask the theory to reconstruct the reason from reason_data.
        let theory_reasons = self.theory.explain_propagation(term, reason_data)?;
        if theory_reasons.is_empty() {
            return None;
        }

        // Convert TheoryLit -> SAT Literal.
        // Clause format: [propagated, ¬r₁, ¬r₂, ...].
        let mut clause: Vec<Literal> = Vec::with_capacity(theory_reasons.len() + 1);
        clause.push(propagated);
        let reason_count = theory_reasons.len();
        for r in &theory_reasons {
            if let Some(reason_lit) = self.term_to_literal(r.term, !r.value) {
                clause.push(reason_lit);
            }
        }
        // Soundness guard: all reason terms must map to SAT literals.
        if clause.len() - 1 < reason_count {
            return None;
        }
        Some(clause)
    }

    fn on_restart(&self) -> Vec<Variable> {
        // #7982: Return theory atom variables for VSIDS re-boosting at restart.
        // Theory atoms get one initial VSIDS bump at registration, but after
        // ~20 conflicts the bump is overwhelmed by conflict-driven activity.
        // Re-boosting at restart time keeps theory atoms competitive in the
        // VSIDS heap, combating the "bound starvation" problem where DPLL
        // stops deciding theory atoms and the theory gets no bounds to work
        // with. This matches Z3's approach of periodically re-prioritizing
        // theory variables (theory_var_init_value, mk_diseq).
        self.theory_atoms
            .iter()
            .filter_map(|term| self.term_to_var.get(term).map(|&v| Variable::new(v)))
            .collect()
    }
}

mod check;
mod construction;
mod helpers;
mod native_dispatch;
mod propagate;
mod unassigned;
pub(crate) use construction::infer_bound_axiom_arith_kind;
#[cfg(test)]
use native_dispatch::NativeTheoryPropagationControl;
use native_dispatch::NativeTheoryPropagationDispatch;
mod phase_hint;
pub(crate) use phase_hint::PhaseHintExtension;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
