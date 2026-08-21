// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT solver extension trait for DPLL(T) integration
//!
//! This module provides the `Extension` trait which allows external theory
//! solvers to integrate with the SAT solver for DPLL(T) style solving.
//!
//! The extension is called at key points during SAT solving:
//! - After propagation (to check for theory propagations)
//! - When a literal is assigned (to update theory state)
//! - After finding a complete model (for final theory check)
//!
//! Based on Z3's sat_extension.h design.
//!
//! # Clause-Based vs Justification-Based Propagation
//!
//! This implementation uses clause-based propagation where theory lemmas are
//! converted to explicit SAT clauses. This is simpler than justification-based
//! propagation (like Z3 uses internally) but requires more clauses.
//!
//! For example, if the theory knows `a=b ∧ b=c → a=c`, it adds the clause
//! `(¬(a=b) ∨ ¬(b=c) ∨ (a=c))` to the SAT solver.

use crate::{Literal, Variable};

/// Result of extension's final check
#[derive(Debug)]
#[non_exhaustive]
pub enum ExtCheckResult {
    /// Theory accepts the model
    Sat,
    /// Theory found a conflict - the clause blocks the current assignment
    Conflict(Vec<Literal>),
    /// Theory could not determine (may need more propagation)
    Unknown,
    /// Theory needs these clauses added, then SAT should continue solving.
    ///
    /// Used for array theory lemmas (#6546): instead of returning to the
    /// outer split loop (which recreates the theory and re-solves from
    /// scratch), add the lemma clauses and continue within the same SAT
    /// invocation. This eliminates O(N) full SAT-solve round-trips.
    AddClauses(Vec<Vec<Literal>>),
}

/// Result of extension's unit propagation
#[derive(Debug, Default)]
#[non_exhaustive]
pub struct ExtPropagateResult {
    /// Clauses to add to the SAT solver (theory lemmas)
    ///
    /// Each clause is a disjunction. If the clause has one satisfied literal
    /// or one unassigned literal with all others false, SAT will propagate.
    pub clauses: Vec<Vec<Literal>>,

    /// Lightweight theory propagations (#4919).
    ///
    /// Each entry is `(reason_clause, propagated_literal)` where:
    /// - `reason_clause` contains the full clause `[propagated_lit, ¬r₁, ¬r₂, ...]`
    ///   with the propagated literal as the FIRST element
    /// - `propagated_literal` is the literal to enqueue on the trail
    ///
    /// Unlike `clauses`, these skip watch-list attachment and VSIDS bumping.
    /// The clause is stored in the arena only as a reason for conflict analysis.
    /// This matches Z3's `ctx().assign()` pattern where theory propagations
    /// go directly to the trail without creating watched clauses.
    pub propagations: Vec<(Vec<Literal>, Literal)>,

    /// Lazy theory propagations (#8467).
    ///
    /// Each entry is `(propagated_literal, reason_data)` where:
    /// - `propagated_literal` is the literal to enqueue on the trail
    /// - `reason_data` is a theory-opaque u64 handle that can be passed to
    ///   `Extension::explain_lazy_reason()` during conflict analysis to
    ///   reconstruct the full reason clause on demand
    ///
    /// ~90% of propagated variables are never resolved during conflict analysis,
    /// so their reasons never need to be materialized. This defers the
    /// O(reason_len) clause allocation from propagation time to conflict
    /// analysis time. Reference: Z3's `u_dependency` in `lp/lp_bound_propagator.h`.
    pub lazy_propagations: Vec<(Literal, u64)>,

    /// Conflict clause if theory detected a conflict
    ///
    /// If set, all literals in this clause must be false under the current
    /// assignment, indicating the assignment is theory-inconsistent.
    pub conflict: Option<Vec<Literal>>,

    /// Request the SAT solver to stop immediately and return Unknown.
    ///
    /// Used when the theory needs to hand control back to an outer split
    /// loop (e.g., for expression splits or disequality splits). Without
    /// this, the SAT solver continues searching and may clear the stored
    /// split request on a subsequent propagation round (#4919).
    pub stop: bool,

    /// Variables whose VSIDS activity should be bumped (#8421).
    ///
    /// Theory atoms that appear in conflicts or propagations should be bumped
    /// so the SAT solver prioritizes deciding on contentious theory atoms.
    /// This is the eager-path analog of Z3's `update_activity()` calls in
    /// `theory_var_init_value`. Without this, theory atoms only get VSIDS
    /// bumps at registration and restart, causing the SAT solver to stop
    /// focusing on theory-relevant variables after ~20 conflicts.
    pub bump_vars: Vec<Variable>,
}

impl ExtPropagateResult {
    /// Create an empty result (no propagation)
    pub fn none() -> Self {
        Self::default()
    }

    /// Create a result with a single clause to add
    pub fn clause(clause: Vec<Literal>) -> Self {
        Self {
            clauses: vec![clause],
            propagations: vec![],
            lazy_propagations: vec![],
            conflict: None,
            stop: false,
            bump_vars: Vec::new(),
        }
    }

    /// Create a result with multiple clauses
    pub fn clauses(clauses: Vec<Vec<Literal>>) -> Self {
        Self {
            clauses,
            propagations: vec![],
            lazy_propagations: vec![],
            conflict: None,
            stop: false,
            bump_vars: Vec::new(),
        }
    }

    /// Create a conflict result
    pub fn conflict(clause: Vec<Literal>) -> Self {
        Self {
            clauses: vec![],
            propagations: vec![],
            lazy_propagations: vec![],
            conflict: Some(clause),
            stop: false,
            bump_vars: Vec::new(),
        }
    }

    /// Create a result with all fields specified.
    pub fn new(
        clauses: Vec<Vec<Literal>>,
        propagations: Vec<(Vec<Literal>, Literal)>,
        conflict: Option<Vec<Literal>>,
        stop: bool,
    ) -> Self {
        Self {
            clauses,
            propagations,
            lazy_propagations: vec![],
            conflict,
            stop,
            bump_vars: Vec::new(),
        }
    }

    /// Set the `stop` flag on this result (builder pattern).
    pub fn with_stop(mut self, stop: bool) -> Self {
        self.stop = stop;
        self
    }

    /// Set the variables to bump in the VSIDS heap (builder pattern, #8421).
    pub fn with_bump_vars(mut self, vars: Vec<Variable>) -> Self {
        self.bump_vars = vars;
        self
    }
}

/// Extension instance prepared during the SAT solver's preprocessing phase.
///
/// This allows a downstream crate to:
/// 1. inspect a snapshot of the current irredundant clause set,
/// 2. decide which clauses are consumed by a theory-specific extractor, and
/// 3. freeze theory-tracked variables before SAT preprocessing continues.
///
/// The consumed clause positions refer to the exact clause snapshot passed to
/// the builder callback. The extension must enforce the exact conjunction of
/// those clauses over their shared variables, not merely an equisatisfiable
/// projection: SAT preprocessing may derive other constraints from the source
/// clauses before ownership is committed. Every variable occurring in a
/// consumed clause must therefore also appear in `frozen_variables`; the
/// solver rejects preparation when that interface is incomplete.
pub struct PreparedExtension<E> {
    /// The extension to activate once SAT preprocessing finishes.
    pub extension: E,
    /// Positions in the builder's clause snapshot that should be removed from
    /// the SAT clause database because the extension now owns them.
    pub consumed_clause_positions: Vec<usize>,
    /// Variables that must be frozen before destructive SAT preprocessing
    /// continues (for example, to keep BVE from eliminating XOR-tracked vars).
    pub frozen_variables: Vec<Variable>,
}

impl<E> PreparedExtension<E> {
    /// Create a prepared extension and canonicalize its metadata.
    pub fn new(
        extension: E,
        mut consumed_clause_positions: Vec<usize>,
        mut frozen_variables: Vec<Variable>,
    ) -> Self {
        consumed_clause_positions.sort_unstable();
        consumed_clause_positions.dedup();
        frozen_variables.sort_unstable_by_key(|var| var.index());
        frozen_variables.dedup_by_key(|var| var.index());
        Self {
            extension,
            consumed_clause_positions,
            frozen_variables,
        }
    }
}

/// Read-only context for observing solver state
pub trait SolverContext {
    /// Get the current value of a variable (None if unassigned)
    fn value(&self, var: Variable) -> Option<bool>;

    /// Get the current value of a literal (None if unassigned)
    fn lit_value(&self, lit: Literal) -> Option<bool> {
        self.value(lit.variable())
            .map(|v| if lit.is_positive() { v } else { !v })
    }

    /// Get the current decision level
    fn decision_level(&self) -> u32;

    /// Get the level at which a variable was assigned (None if unassigned)
    fn var_level(&self, var: Variable) -> Option<u32>;

    /// The reason-side literals of a PROPAGATED variable: the OTHER literals
    /// of the clause (or binary jump) that propagated it — each FALSE under
    /// the current assignment. `None` for decisions, unassigned variables,
    /// lazy theory reasons, stale arena offsets, and implementations without
    /// reason access (the default). Provenance-only: a `None` means
    /// "antecedents unknown", never an error.
    fn var_reason_side(&self, _var: Variable) -> Option<Vec<Literal>> {
        None
    }

    /// Get all currently assigned literals (the trail)
    fn trail(&self) -> &[Literal];

    /// Number of variables the solver currently has allocated.
    ///
    /// An extension that needs to MINT a fresh SAT variable mid-search (to name
    /// a theory term that was never encoded) must know where the solver's
    /// variable space currently ends, or it would alias its new term onto an
    /// existing variable. `add_theory_lemma` already grows the solver for
    /// out-of-range literals, so an extension may hand back a clause over ids
    /// `>= num_vars()`.
    ///
    /// The default of 0 means "unknown"; a minting extension must treat that as
    /// "cannot mint safely" and fall back to its previous behaviour rather than
    /// guess an id. Only the real solver overrides this.
    fn num_vars(&self) -> usize {
        0
    }

    /// Get the VSIDS activity score for a variable.
    ///
    /// Returns the current activity score used by the SAT solver's decision
    /// heuristic. Higher scores indicate variables involved in more recent
    /// conflicts. Theory extensions can use this to prioritize branching on
    /// high-activity theory atoms, aligning theory decisions with SAT search.
    ///
    /// Default returns 0.0 for contexts that don't track activity.
    fn activity(&self, _var: Variable) -> f64 {
        0.0
    }

    /// Get literals assigned since the last extension call
    ///
    /// Returns the slice of trail from `last_trail_pos` to current.
    fn new_assignments(&self, last_trail_pos: usize) -> &[Literal] {
        let trail = self.trail();
        if last_trail_pos < trail.len() {
            &trail[last_trail_pos..]
        } else {
            &[]
        }
    }

    /// Get the number of conflicts encountered during solving.
    ///
    /// Enables theory extensions to adapt behavior based on SAT solver
    /// conflict activity without maintaining duplicate counters.
    fn conflicts(&self) -> u64 {
        0
    }

    /// Get the number of decisions made during solving.
    ///
    /// Enables theory extensions to monitor search progress and adjust
    /// heuristics (e.g., theory-aware branching frequency).
    fn decisions(&self) -> u64 {
        0
    }

    /// Get the number of restarts performed during solving.
    ///
    /// Enables theory extensions to detect restart patterns for adaptive
    /// behavior (e.g., re-boosting theory variable activities).
    fn restarts(&self) -> u64 {
        0
    }

    /// Get the number of propagations performed during solving.
    ///
    /// Enables theory extensions to gauge BCP activity for adaptive
    /// batching and deferral thresholds.
    fn propagations(&self) -> u64 {
        0
    }
}

/// Extension trait for DPLL(T) theory integration
///
/// Implement this trait to add theory reasoning to the SAT solver.
/// The extension is called during key phases of CDCL solving.
///
/// # Implementation Guide
///
/// 1. Track assigned literals via `asserted()` or `new_assignments()`
/// 2. In `propagate()`, check for theory implications and conflicts
/// 3. Return clauses that encode the implications
/// 4. In `check()`, do final consistency check when SAT finds a model
/// 5. In `backtrack()`, undo state for assignments above the level
pub trait Extension {
    /// Called after unit propagation completes to check for theory propagations
    ///
    /// The extension should:
    /// 1. Update its internal state based on new assignments
    /// 2. Check for theory propagations
    /// 3. Return clauses to add to SAT (propagation lemmas)
    ///
    /// Theory lemmas should have the form:
    /// `(¬reason1 ∨ ¬reason2 ∨ ... ∨ conclusion)`
    ///
    /// If all reason literals are true, SAT will propagate the conclusion.
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult;

    /// Called when a literal is assigned
    ///
    /// The extension can use this to incrementally update its internal state.
    /// This is called for each literal added to the trail.
    fn asserted(&mut self, _lit: Literal) {
        // Default: do nothing (use propagate() to see new assignments)
    }

    /// Called after SAT finds a complete model for final theory check
    ///
    /// The extension should check if the complete assignment is consistent
    /// with the theory. If not, it returns a conflict clause.
    ///
    /// This is called when all variables are assigned and SAT has no conflict.
    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        // Default: accept any model
        ExtCheckResult::Sat
    }

    /// Called when the solver backtracks
    ///
    /// The extension should undo any state changes made above the given level.
    /// `new_level` is the level we're backtracking TO (will keep assignments
    /// at this level and below).
    fn backtrack(&mut self, _new_level: u32) {
        // Default: do nothing
    }

    /// Called at the start of solving
    fn init(&mut self) {
        // Default: do nothing
    }

    /// Check if the extension can make progress
    ///
    /// Returns true if `propagate()` might return new clauses.
    /// Used to avoid calling `propagate()` unnecessarily.
    ///
    /// The context is provided so extensions can check if there are new
    /// SAT assignments since the last `propagate()` call.
    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        // Default: always check (suboptimal but safe)
        true
    }

    /// Suggest the next decision literal for the SAT solver.
    ///
    /// Called before the SAT solver picks a decision variable via VSIDS.
    /// If this returns `Some(lit)`, the solver decides `lit` instead of
    /// using its internal heuristic. If `None`, the solver falls back to
    /// its normal decision procedure.
    ///
    /// This enables CP-level search heuristics like:
    /// - **First-fail**: choose the variable with smallest domain
    /// - **Domain/wdeg**: smallest domain weighted by constraint failures
    /// - **Impact**: choose the variable whose assignment most reduces search space
    ///
    /// The returned literal must be unassigned; otherwise the solver ignores it.
    fn suggest_decision(&self, _ctx: &dyn SolverContext) -> Option<Literal> {
        // Default: no suggestion (use SAT solver's VSIDS heuristic)
        None
    }

    /// Suggest the polarity for a theory-relevant variable.
    ///
    /// Called after VSIDS picks a decision variable. If the variable is a
    /// theory atom, the extension can suggest a polarity consistent with
    /// the current theory model (e.g., LP solution for LRA).
    ///
    /// Returns `Some(true)` for positive, `Some(false)` for negative,
    /// or `None` to let the SAT solver use its default phase heuristic.
    ///
    /// Reference: Z3 `theory_lra::get_phase()`, `arith_solver::get_phase()`
    fn suggest_phase(&self, _var: Variable) -> Option<bool> {
        // Default: no suggestion
        None
    }

    /// Bulk phase seeding: write theory-model-consistent phases for all
    /// unassigned theory atoms into the provided phase array.
    ///
    /// Called after theory propagation reaches a fixpoint in the CDCL loop.
    /// For each unassigned theory atom variable, the extension queries
    /// `suggest_phase(var)` and writes the result into `phases[var.index()]`.
    /// This seeds the SAT solver's phase-saving array so that `pick_phase()`
    /// returns theory-consistent polarities even when the per-decision
    /// `suggest_phase(var)` call is not reached (e.g., VSIDS picks a
    /// non-theory variable, or rephasing overwrites phases).
    ///
    /// This is the Z3-style feedback loop: the theory model guides SAT
    /// search by biasing phase selection toward assignments that are
    /// consistent with the current LP solution / theory model.
    ///
    /// The `vals` slice is the SAT solver's literal value array (CaDiCaL-style:
    /// `vals[var_index * 2]` is 0 for unassigned, >0 for true, <0 for false).
    /// Used to skip already-assigned variables without aliasing `phases`.
    ///
    /// Reference: Z3 `theory_var_init_value`, `theory_aware_branching`
    fn seed_phase_hints(&self, _phases: &mut [i8], _vals: &[i8]) {
        // Default: no bulk seeding
    }

    /// Single-pass bulk seeding of BOTH the saved-phase and target-phase arrays.
    ///
    /// `seed_theory_phases` previously called [`Extension::seed_phase_hints`]
    /// twice — once for `phase[]` and once for `target_phase[]` — which scans
    /// every theory atom and queries `suggest_phase` twice per atom on every
    /// BCP/theory-propagation quiescence. For LRA/induction benchmarks this
    /// double full scan dominated runtime (~20x the simplex cost per profiling).
    ///
    /// This method lets an extension write both arrays in ONE pass with a
    /// single `suggest_phase` query per atom. The default implementation simply
    /// preserves the prior behavior (two separate scans) so extensions that do
    /// not override it are bit-identical. Extensions with a fast atom index
    /// (e.g. `PhaseHintExtension`) override this for the single-pass win.
    ///
    /// Both arrays use identical indexing and filtering semantics as
    /// [`Extension::seed_phase_hints`]; see its docs for the `vals` layout.
    fn seed_phase_hints_dual(&self, phase: &mut [i8], target_phase: &mut [i8], vals: &[i8]) {
        self.seed_phase_hints(phase, vals);
        self.seed_phase_hints(target_phase, vals);
    }

    /// Materialize a lazy theory reason on demand during conflict analysis (#8467).
    ///
    /// Called when the SAT solver encounters a `ReasonKind::LazyTheory` during
    /// 1UIP conflict analysis. The `reason_data` is the opaque u64 handle that
    /// was stored at propagation time via `lazy_propagations`.
    ///
    /// Returns the full reason clause `[propagated_lit, ¬r₁, ¬r₂, ...]` with
    /// the propagated literal as the FIRST element, or `None` if the reason
    /// can no longer be reconstructed (bound was retracted).
    ///
    /// ~90% of propagated variables are never resolved during conflict analysis,
    /// so their reasons never need to be materialized. This is the core of the
    /// lazy justification optimization.
    ///
    /// Reference: Z3's `u_dependency` in `lp/lp_bound_propagator.h`.
    fn explain_lazy_reason(
        &mut self,
        _propagated: Literal,
        _reason_data: u64,
    ) -> Option<Vec<Literal>> {
        // Default: no lazy reasons supported
        None
    }

    /// Ask whether the current restart should be blocked.
    ///
    /// Called when the restart condition triggers. If the extension returns
    /// true, the restart is suppressed (the solver continues searching at
    /// the current decision level). This enables restart blocking strategies
    /// like Audemard & Simon 2012 that preserve near-solution assignments.
    fn should_block_restart(&self, _num_assigned: u32, _total_vars: u32) -> bool {
        false
    }

    /// Called after the solver performs a restart.
    ///
    /// The extension can use this to re-boost theory-relevant variable
    /// activities so they don't sink below conflict-bumped encoding variables
    /// in the VSIDS heap. Without periodic re-boosting, theory atoms get
    /// one initial bump at registration but are quickly overwhelmed by
    /// conflict-driven bumps after ~20 conflicts, causing "bound starvation"
    /// where the DPLL solver stops deciding theory atoms (#7982).
    ///
    /// Returns a list of variables whose VSIDS activity should be bumped.
    fn on_restart(&self) -> Vec<Variable> {
        Vec::new()
    }
}

#[cfg(test)]
#[path = "extension_tests.rs"]
mod tests;
