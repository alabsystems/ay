// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory callback abstraction for the unified CDCL loop.
//!
//! Provides a common interface (`TheoryCallback`) that unifies closure-based
//! theory propagation and `Extension`-based theory integration into a single
//! dispatch mechanism consumed by `solve_no_assumptions_with_theory_backend`.

use super::super::*;

/// Final theory-side model verdict consumed by the unified CDCL loop.
pub(in crate::solver) enum TheoryModelCheck {
    Sat,
    Conflict(Vec<Literal>),
    Unknown(SatUnknownReason),
    /// Add clauses and continue solving (#6546).
    AddClauses(Vec<Vec<Literal>>),
}

/// Shared interface used by the unified theory/extension CDCL loop.
pub(in crate::solver) trait TheoryCallback {
    fn init_loop(&mut self, solver: &mut Solver) -> Option<SatResult> {
        solver.init_solve()
    }

    fn propagate(&mut self, solver: &mut Solver) -> TheoryPropResult;

    /// Propagate unconditionally, bypassing the can_propagate gate.
    ///
    /// Used inside the BCP-theory fixpoint loop (#8452) where the theory
    /// may have pending work from implied bounds cascading that does not
    /// manifest as new theory atoms on the SAT trail. The outer loop uses
    /// `propagate()` (which checks `can_propagate`); the fixpoint inner
    /// loop uses `propagate_force()` to ensure cascading effects are not
    /// stranded.
    fn propagate_force(&mut self, solver: &mut Solver) -> TheoryPropResult {
        self.propagate(solver)
    }

    fn backtrack(&mut self, _backtrack_level: u32) {}

    /// Pre-materialize lazy theory reasons at the current decision level (#8467).
    ///
    /// Called before conflict analysis so that 1UIP resolution never encounters
    /// unmaterialized lazy reasons. Only the Extension callback implements this;
    /// other callbacks are no-ops since they never produce lazy propagations.
    fn materialize_lazy_reasons(&mut self, _solver: &mut Solver) {}

    /// Materialize surviving lazy reasons before the callback pops theory scopes.
    ///
    /// Chronological backtracking and trail reuse can keep lower-level SAT
    /// assignments while the extension pops higher theory scopes. Lazy reason
    /// handles are theory-local, so extension callbacks must materialize any
    /// remaining lazy SAT-trail reasons before `backtrack()` can invalidate the
    /// theory state that owns them.
    fn backtrack_after_materializing_lazy_reasons(
        &mut self,
        solver: &mut Solver,
        backtrack_level: u32,
    ) {
        self.materialize_lazy_reasons(solver);
        self.backtrack(backtrack_level);
    }

    /// Materialize lazy reasons before an extension-level restart resets theory
    /// state. Default callbacks have no lazy extension reasons.
    fn materialize_lazy_reasons_before_restart(&mut self, solver: &mut Solver) {
        self.materialize_lazy_reasons(solver);
    }

    /// Called when the solver performs a restart. Returns variables whose VSIDS
    /// activity should be bumped to combat theory atom starvation (#7982).
    fn on_restart(&mut self) -> Vec<Variable> {
        Vec::new()
    }

    fn check_model(&mut self, _solver: &mut Solver) -> TheoryModelCheck {
        TheoryModelCheck::Sat
    }

    /// Ask the extension for a decision literal suggestion.
    fn suggest_decision(&self, _solver: &Solver) -> Option<Literal> {
        None
    }

    /// Ask the extension for a phase suggestion for a theory-relevant variable.
    fn suggest_phase(&self, _var: Variable) -> Option<bool> {
        None
    }

    /// Bulk-seed theory-model-consistent phases into the solver's phase array.
    ///
    /// Called after theory propagation reaches a fixpoint. For each unassigned
    /// theory atom, queries the theory model and writes the result into
    /// `solver.phase[]`. This creates the Z3-style feedback loop where the
    /// theory model guides SAT phase selection.
    fn seed_theory_phases(&self, _solver: &mut Solver) {
        // Default: no bulk seeding (pure SAT / closure-based callbacks)
    }

    fn conflict_context(&self) -> &'static str {
        "theory loop"
    }

    /// Minimum conflicts before restarts are allowed. Extension mode uses a
    /// warmup period so EMA can stabilize and the initial search trajectory
    /// is not disrupted by premature restarts.
    fn restart_warmup_conflicts(&self) -> u64 {
        0
    }

    /// Ask whether the current restart should be blocked. Called when the
    /// restart condition triggers. If the callback returns true, the restart
    /// is suppressed (the solver continues searching at the current level).
    /// Audemard & Simon 2012: block restarts when the solver is near a solution.
    fn should_block_restart(&self, _num_assigned: u32, _total_vars: u32) -> bool {
        false
    }

    fn handle_conflict_clause(
        &mut self,
        solver: &mut Solver,
        clause: Vec<Literal>,
    ) -> Option<SatResult> {
        if clause.is_empty() {
            return Some(solver.declare_unsat());
        }
        solver.add_theory_lemma(clause);
        None
    }
}

/// No-op callback for pure SAT solving (no theory integration).
///
/// All methods use defaults or return no-ops. With monomorphization,
/// The optimizer inlines and eliminates all callback dispatch in the CDCL loop.
pub(in crate::solver) struct NullCallback;

impl TheoryCallback for NullCallback {
    fn propagate(&mut self, _solver: &mut Solver) -> TheoryPropResult {
        TheoryPropResult::Continue
    }

    fn conflict_context(&self) -> &'static str {
        "main search loop"
    }
}

/// Adapter for closure-based theory propagation.
pub(in crate::solver) struct TheoryClosureCallback<'a, F> {
    pub(in crate::solver) theory_check: &'a mut F,
}

impl<F: FnMut(&mut Solver) -> TheoryPropResult> TheoryCallback for TheoryClosureCallback<'_, F> {
    fn propagate(&mut self, solver: &mut Solver) -> TheoryPropResult {
        (self.theory_check)(solver)
    }
}

/// Adapter for extension-based theory integration.
pub(in crate::solver) struct ExtensionCallback<'a> {
    pub(in crate::solver) ext: &'a mut dyn Extension,
}

impl TheoryCallback for ExtensionCallback<'_> {
    fn init_loop(&mut self, solver: &mut Solver) -> Option<SatResult> {
        solver.init_extension_loop(self.ext)
    }

    fn propagate(&mut self, solver: &mut Solver) -> TheoryPropResult {
        if !self.ext.can_propagate(solver) {
            return TheoryPropResult::Continue;
        }

        let mut result = self.ext.propagate(solver);

        // #8421: Bump VSIDS activity for theory-conflict-driven variables.
        // Theory atoms in conflicts/propagations should be prioritized in
        // the decision heuristic so the SAT solver focuses on contentious
        // theory atoms. Process bump_vars before returning any result so
        // the bumps apply even when the result is a conflict.
        if !result.bump_vars.is_empty() {
            solver.bump_theory_vars(&result.bump_vars);
        }

        // Chunked XOR ladders (task #20): the proof-only scaffolding must be
        // in the proof stream BEFORE any accompanying lemma, reason, or
        // conflict clause is emitted, or those clauses are not RUP and an
        // external checker rejects the whole certificate.
        if !result.proof_script.is_empty() {
            solver.apply_extension_proof_script(std::mem::take(&mut result.proof_script));
        }

        if let Some(conflict) = result.conflict {
            // Process any accompanying proof clauses BEFORE returning the
            // conflict (#4533). When the XOR extension detects a 0=1 conflict
            // at level 0, it includes intermediate proof clauses that must be
            // emitted to the DRAT proof stream before the conflict clause (or
            // empty clause). Without this, external DRAT checkers cannot verify
            // the derivation because the intermediate clauses are dropped.
            for clause in result.clauses {
                solver.add_theory_lemma(clause);
            }
            return TheoryPropResult::Conflict(conflict);
        }
        let has_work = !result.clauses.is_empty()
            || !result.propagations.is_empty()
            || !result.lazy_propagations.is_empty();

        if solver.cold.trace_ext_conflict && has_work {
            eprintln!(
                "[EXT_CB] propagate: {} clauses, {} propagations at dl={} trail_len={}",
                result.clauses.len(),
                result.propagations.len(),
                solver.current_decision_level(),
                solver.trail_len()
            );
            for (i, (clause, prop)) in result.propagations.iter().enumerate() {
                eprintln!(
                    "[EXT_CB]   prop[{}]: propagated=({},{}) clause={:?}",
                    i,
                    prop.variable().index(),
                    prop.is_positive(),
                    clause
                        .iter()
                        .map(|l| (l.variable().index(), l.is_positive()))
                        .collect::<Vec<_>>()
                );
            }
            for (i, clause) in result.clauses.iter().enumerate() {
                eprintln!(
                    "[EXT_CB]   clause[{}]: {:?}",
                    i,
                    clause
                        .iter()
                        .map(|l| (l.variable().index(), l.is_positive()))
                        .collect::<Vec<_>>()
                );
            }
        }

        // General theory lemma clauses (conflicts, multi-watch clauses).
        // If add_theory_lemma detects an immediate conflict (all literals
        // false at level > 0), it returns Some(clause_ref) without
        // enqueuing anything — BCP would never discover this conflict.
        // Detect this and return as a conflict for proper handling (#6262).
        for clause in result.clauses {
            let all_false = clause.iter().all(|lit| solver.lit_val(*lit) < 0);
            if all_false && solver.current_decision_level() > 0 {
                // Don't add to clause DB — return as a conflict for
                // handle_ext_conflict to process (backtrack + re-add).
                return TheoryPropResult::Conflict(clause);
            }
            solver.add_theory_lemma(clause);
        }
        // Lightweight theory propagations (#4919): directly enqueue on trail
        // without watch-list overhead. Matches Z3's ctx().assign() pattern.
        for (clause, propagated) in result.propagations {
            solver.add_theory_propagation_scoped(clause, propagated);
        }
        // Lazy theory propagations (#8467): enqueue on trail with deferred
        // reason materialization. The full reason clause is only constructed
        // during conflict analysis when the variable is actually resolved.
        for (propagated, reason_data) in result.lazy_propagations {
            solver.add_lazy_theory_propagation(propagated, reason_data);
        }
        // Theory requested immediate stop (split pending) — hand control
        // back to the outer split loop before SAT search can clear the
        // pending split on a subsequent propagation round (#4919).
        // Checked AFTER clauses/propagations are processed so they are
        // not dropped.
        if solver.has_empty_clause() {
            return TheoryPropResult::Conflict(vec![]);
        }
        if result.stop {
            return TheoryPropResult::Stop;
        }
        if !has_work {
            return TheoryPropResult::Continue;
        }
        TheoryPropResult::Propagate
    }

    fn propagate_force(&mut self, solver: &mut Solver) -> TheoryPropResult {
        // #8452: Bypass can_propagate gate for fixpoint re-entry.
        // Inside the BCP-theory fixpoint loop, the theory may have pending
        // implied bounds cascading work that doesn't manifest as new theory
        // atoms on the SAT trail. Calling propagate() unconditionally ensures
        // the theory's check_during_propagate runs even when BCP only
        // propagated boolean encoding variables.
        let mut result = self.ext.propagate(solver);

        if !result.bump_vars.is_empty() {
            solver.bump_theory_vars(&result.bump_vars);
        }

        // Chunked XOR ladders (task #20): scaffolding precedes dependent
        // clauses in the proof stream (see `propagate` above).
        if !result.proof_script.is_empty() {
            solver.apply_extension_proof_script(std::mem::take(&mut result.proof_script));
        }

        if let Some(conflict) = result.conflict {
            for clause in result.clauses {
                solver.add_theory_lemma(clause);
            }
            return TheoryPropResult::Conflict(conflict);
        }
        let has_work = !result.clauses.is_empty()
            || !result.propagations.is_empty()
            || !result.lazy_propagations.is_empty();

        for clause in result.clauses {
            let all_false = clause.iter().all(|lit| solver.lit_val(*lit) < 0);
            if all_false && solver.current_decision_level() > 0 {
                return TheoryPropResult::Conflict(clause);
            }
            solver.add_theory_lemma(clause);
        }
        for (clause, propagated) in result.propagations {
            solver.add_theory_propagation_scoped(clause, propagated);
        }
        for (propagated, reason_data) in result.lazy_propagations {
            solver.add_lazy_theory_propagation(propagated, reason_data);
        }
        if solver.has_empty_clause() {
            return TheoryPropResult::Conflict(vec![]);
        }
        if result.stop {
            return TheoryPropResult::Stop;
        }
        if !has_work {
            return TheoryPropResult::Continue;
        }
        TheoryPropResult::Propagate
    }

    fn backtrack(&mut self, backtrack_level: u32) {
        self.ext.backtrack(backtrack_level);
    }

    fn materialize_lazy_reasons(&mut self, solver: &mut Solver) {
        solver.materialize_current_level_lazy_reasons(self.ext);
    }

    fn backtrack_after_materializing_lazy_reasons(
        &mut self,
        solver: &mut Solver,
        backtrack_level: u32,
    ) {
        solver.materialize_lazy_reasons_through_level_for_backtrack(self.ext, backtrack_level);
        self.ext.backtrack(backtrack_level);
    }

    fn materialize_lazy_reasons_before_restart(&mut self, solver: &mut Solver) {
        solver.materialize_all_lazy_reasons_before_extension_restart(self.ext);
    }

    fn on_restart(&mut self) -> Vec<Variable> {
        self.ext.backtrack(0);
        self.ext.on_restart()
    }

    fn check_model(&mut self, solver: &mut Solver) -> TheoryModelCheck {
        match self.ext.check(solver) {
            ExtCheckResult::Sat => TheoryModelCheck::Sat,
            ExtCheckResult::Conflict(clause) => TheoryModelCheck::Conflict(clause),
            ExtCheckResult::Unknown => {
                TheoryModelCheck::Unknown(SatUnknownReason::ExtensionUnknown)
            }
            ExtCheckResult::AddClauses(clauses) => TheoryModelCheck::AddClauses(clauses),
        }
    }

    fn suggest_decision(&self, solver: &Solver) -> Option<Literal> {
        self.ext.suggest_decision(solver)
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        self.ext.suggest_phase(var)
    }

    fn seed_theory_phases(&self, solver: &mut Solver) {
        // Bulk-seed theory-model-consistent phases into the solver's phase
        // and target_phase arrays in a SINGLE pass. The extension writes
        // phases for all unassigned theory atoms so that pick_phase() returns
        // theory-consistent polarities.
        //
        // #8452: target_phase[] must be seeded too. In stable mode,
        // pick_phase() checks target_phase before the saved phase (priority 2
        // vs 3). Without this, target phases from the longest conflict-free
        // trail override theory guidance, causing the SAT solver to repeat
        // non-theory-consistent polarities even after the theory model has
        // changed. Z3's PS_THEORY mode calls get_phase() on every decision,
        // which always overrides cached phases; AY's CaDiCaL-based architecture
        // uses phase arrays, so seeding target_phase ensures theory guidance
        // dominates in stable mode.
        //
        // The two arrays receive identical values (same suggest_phase query per
        // atom), so seed_phase_hints_dual writes both in one scan instead of
        // two — eliminating the double full-scan over theory atoms that
        // dominated runtime on LRA/induction benchmarks. Split borrows:
        // &solver.vals for the assignment check, &mut solver.phase and
        // &mut solver.target_phase for writing. All three are separate Vec
        // fields so the borrows are disjoint.
        self.ext
            .seed_phase_hints_dual(&mut solver.phase, &mut solver.target_phase, &solver.vals);
    }

    fn conflict_context(&self) -> &'static str {
        "extension loop"
    }

    fn restart_warmup_conflicts(&self) -> u64 {
        EXTENSION_RESTART_WARMUP
    }

    fn should_block_restart(&self, num_assigned: u32, total_vars: u32) -> bool {
        self.ext.should_block_restart(num_assigned, total_vars)
    }

    fn handle_conflict_clause(
        &mut self,
        solver: &mut Solver,
        clause: Vec<Literal>,
    ) -> Option<SatResult> {
        if clause.is_empty() {
            // Empty conflict clause = derivation of the empty clause = UNSAT.
            // The extension proved a genuine contradiction (e.g., XOR: 0 = 1).
            return Some(solver.declare_unsat());
        }
        solver.tla_trace_step(
            CdclTraceState::Conflicting,
            Some(CdclTraceAction::DetectConflict),
        );
        solver.handle_ext_conflict(clause, self.ext);
        None
    }
}
