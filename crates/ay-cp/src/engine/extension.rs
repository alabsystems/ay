// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CP-SAT extension adapter for ay-sat's CDCL loop.
//!
//! `CpExtension` implements `ay_sat::Extension` so the SAT solver can call
//! into CP propagation during search. This is the core integration point
//! for Lazy Clause Generation (LCG).

use ay_sat::{ExtCheckResult, ExtPropagateResult, Extension, Literal, SolverContext, Variable};

use crate::encoder::IntegerEncoder;
use crate::propagator::{PropagationResult, Propagator};
use crate::search::SearchState;
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

use super::LazyNeq;

/// CP-SAT extension adapter for ay-sat.
///
/// Wraps the CP state and implements the Extension trait so the SAT solver
/// can call into CP propagation during its CDCL loop. This is the core
/// integration point for Lazy Clause Generation.
///
/// Ownership: during solving, the engine transfers its trail, encoder,
/// propagators, and dirty flags to this struct via `std::mem::take`.
/// After solving, state is transferred back.
pub struct CpExtension {
    /// Integer trail (backtrackable bound changes)
    pub trail: IntegerTrail,
    /// Encoder (immutable during solving — all literals pre-allocated)
    pub encoder: IntegerEncoder,
    /// Constraint propagators
    pub propagators: Vec<Box<dyn Propagator>>,
    /// Dirty flags per propagator
    pub dirty: Vec<bool>,
    /// Number of `true` entries in `dirty`. Maintained by `set_dirty` / `clear_dirty`
    /// so `can_propagate()` is O(1) instead of O(P).
    pub(crate) dirty_count: usize,
    /// Last SAT trail position seen (for incremental assignment processing)
    pub last_trail_pos: usize,
    /// Search heuristic state (weights, activities)
    pub(crate) search: SearchState,
    /// Lazily-checked neq constraints (verified in check() on full assignments)
    pub(crate) lazy_neqs: Vec<LazyNeq>,
    /// Optimization objective: (variable, minimize). When set, `suggest_phase`
    /// guides the SAT solver toward the optimal direction for objective literals.
    pub(crate) objective: Option<(IntVarId, bool)>,
    /// Variable-to-propagator index: var_to_props[var.0] = propagator indices
    /// watching this variable. Avoids O(P*V) linear scan in mark_propagators_dirty.
    pub(crate) var_to_props: Vec<Vec<usize>>,
    /// Propagator indices sorted by priority (cheap first). Computed once at
    /// solve start by `build_var_to_props`. `run_dirty_propagators` iterates
    /// this instead of `0..N` so Linear propagators run before Global ones.
    pub(crate) priority_order: Vec<usize>,
    /// SAT trail position at the start of each decision level.
    /// `level_trail_pos[L]` = the value of `last_trail_pos` when decision level
    /// L was first pushed. On backtrack to level L, we restore `last_trail_pos`
    /// from this so that new BCP entries at level L are correctly processed.
    pub(crate) level_trail_pos: Vec<usize>,
    /// Set by backtrack(), cleared by propagate(). When true, the next
    /// propagate() adjusts last_trail_pos based on the integer trail's level.
    pub(crate) needs_resync: bool,
    /// Workspace: reused across `run_dirty_propagators` calls to avoid
    /// per-cycle allocation of the output clause buffer.
    pub(crate) ws_all_clauses: Vec<Vec<Literal>>,
}

impl CpExtension {
    /// Build the variable-to-propagator index and priority order from current
    /// propagators. Called once at solve start.
    pub(crate) fn build_var_to_props(&mut self) {
        let num_vars = self.trail.num_vars();
        self.var_to_props = vec![Vec::new(); num_vars];
        for (i, prop) in self.propagators.iter().enumerate() {
            for &var in prop.variables() {
                let idx = var.index();
                if idx < num_vars {
                    self.var_to_props[idx].push(i);
                }
            }
        }

        // Sort propagator indices by priority (cheap first, expensive last).
        // Stable sort preserves registration order within the same priority tier.
        self.priority_order = (0..self.propagators.len()).collect();
        self.priority_order
            .sort_by_key(|&i| self.propagators[i].priority());
    }

    /// Mark propagators watching a given variable as dirty.
    fn mark_propagators_dirty(&mut self, var: IntVarId) {
        let idx = var.index();
        if idx < self.var_to_props.len() {
            for &prop_idx in &self.var_to_props[idx] {
                if !self.dirty[prop_idx] {
                    self.dirty[prop_idx] = true;
                    self.dirty_count += 1;
                }
            }
        }
    }

    /// Decode a SAT literal to an integer bound change and update the trail.
    /// Only marks propagators dirty when a bound actually changes.
    fn process_literal(&mut self, lit: Literal) {
        if let Some(bound_lit) = self.encoder.decode(lit.variable()) {
            let var = bound_lit.var;
            let value = bound_lit.value;

            let changed = if bound_lit.is_ge {
                if lit.is_positive() {
                    // [x >= v] became true → tighten lower bound
                    self.trail
                        .set_lb(var, value, lit, None)
                        .ok()
                        .flatten()
                        .is_some()
                } else {
                    // ¬[x >= v] became true → x < v → upper bound = v-1
                    self.trail
                        .set_ub(var, value - 1, lit, None)
                        .ok()
                        .flatten()
                        .is_some()
                }
            } else {
                false
            };

            if changed {
                self.mark_propagators_dirty(var);
            }
        }
    }

    /// Sync integer trail state with the SAT solver's current level and
    /// process new assignments. Called at the start of both `propagate()`
    /// and `check()` to handle lazy backtrack and incremental literal decoding.
    fn sync_from_sat(&mut self, ctx: &dyn SolverContext) {
        let trail_len = ctx.trail().len();
        let sat_level = ctx.decision_level();

        // Lazy backtrack: ext.backtrack() only sets needs_resync.
        // Here we perform the actual integer trail backtrack to the SAT
        // solver's current level. For restarts with trail reuse, this
        // backtracks to reuse_level (not 0), preserving integer trail
        // entries at surviving levels and avoiding full re-processing.
        if self.needs_resync {
            self.needs_resync = false;
            if self.trail.current_level() > sat_level {
                self.trail.backtrack_to(sat_level);
            }
            // Resume from the saved position for the next level after the
            // surviving one. level_trail_pos[L+1] captures the SAT trail
            // position after all level-L entries were processed, so resuming
            // there skips already-decoded entries and processes only new BCP
            // from the learned clause. Propagators are NOT mass-dirtied —
            // only genuinely new bound changes will dirty them via
            // process_literal below.
            let next_level = self.trail.current_level() as usize + 1;
            self.last_trail_pos = if next_level < self.level_trail_pos.len() {
                self.level_trail_pos[next_level].min(trail_len)
            } else {
                0 // Fallback: re-process everything (first backtrack, no level info)
            };
        }

        // Process any new SAT assignments since last call.
        // Record SAT trail positions at each level boundary (level-indexed).
        let boundary = self.last_trail_pos;
        let new_lits = ctx.new_assignments(self.last_trail_pos);
        self.last_trail_pos = trail_len;

        while self.trail.current_level() < sat_level {
            self.trail.push_level();
            let lvl = self.trail.current_level() as usize;
            if lvl >= self.level_trail_pos.len() {
                self.level_trail_pos.resize(lvl + 1, 0);
            }
            self.level_trail_pos[lvl] = boundary;
        }

        // Decode new assignments to integer bound changes
        for &lit in new_lits {
            self.process_literal(lit);
        }
    }

    /// Run dirty propagators once, returning clauses or conflict.
    ///
    /// Propagators produce explanation clauses based on current trail bounds.
    /// The clauses are returned to the SAT solver for BCP. The SAT solver
    /// then calls propagate() again via the CDCL loop if can_propagate()
    /// returns true. The outer CDCL loop drives the fixpoint, not this method.
    fn run_dirty_propagators(&mut self) -> ExtPropagateResult {
        self.ws_all_clauses.clear();

        for pos in 0..self.priority_order.len() {
            let i = self.priority_order[pos];
            if !self.dirty[i] {
                continue;
            }
            self.dirty[i] = false;
            self.dirty_count -= 1;

            let result = self.propagators[i].propagate(&self.trail, &self.encoder);

            match result {
                PropagationResult::NoChange => {}
                PropagationResult::Propagated(clauses) => {
                    self.ws_all_clauses.extend(clauses);
                }
                PropagationResult::Conflict(clause) => {
                    debug_assert!(
                        !clause.is_empty(),
                        "BUG: propagator {} ({}) returned empty conflict clause — \
                         this causes unconditional UNSAT (#5910)",
                        i,
                        self.propagators[i].name(),
                    );
                    // #5910: Guard against empty conflict clauses in release builds.
                    // An empty clause means unconditional UNSAT (no reasons), which
                    // is almost certainly a bug in explanation generation (missing
                    // encoder literals). Skip the conflict rather than poisoning
                    // the SAT solver with an unsound empty clause.
                    if clause.is_empty() {
                        continue;
                    }
                    // Track conflict for dom/wdeg and activity heuristics.
                    // Split borrow: propagators (immutable) and search (mutable)
                    // are disjoint fields, avoiding .to_vec() allocation.
                    let variables = self.propagators[i].variables();
                    self.search.on_conflict(i, variables);
                    return ExtPropagateResult::conflict(clause);
                }
            }
        }

        if self.ws_all_clauses.is_empty() {
            ExtPropagateResult::none()
        } else {
            // Drain workspace into owned Vec for the return value.
            // The inner Vecs are moved out (not cloned), so only the
            // outer Vec shell is allocated fresh. The workspace retains
            // its capacity for the next call.
            ExtPropagateResult::clauses(std::mem::take(&mut self.ws_all_clauses))
        }
    }

    /// Verify a complete SAT model against CP propagators using exact integer
    /// bounds from the model. `Extension::check()` sees the SAT assignment
    /// trail, but not every model bit necessarily became an integer-trail
    /// bound. This closes that gap before `CpSolveResult::Sat` is accepted.
    pub(crate) fn verify_complete_model(&mut self, model: &[bool]) -> ExtPropagateResult {
        self.trail.reset_all();
        self.last_trail_pos = 0;
        self.level_trail_pos.clear();
        self.needs_resync = false;

        for var_idx in 0..self.encoder.num_vars() {
            let var = IntVarId(var_idx as u32);
            let value = self.model_value(model, var);

            if let Some(lb_lit) = self.encoder.lookup_ge(var, value) {
                if self.trail.set_lb(var, value, lb_lit, None).is_err() {
                    return ExtPropagateResult::none();
                }
            }
            if let Some(ub_lit) = self.encoder.lookup_le(var, value) {
                if self.trail.set_ub(var, value, ub_lit, None).is_err() {
                    return ExtPropagateResult::none();
                }
            }
        }

        self.dirty.fill(true);
        self.dirty_count = self.dirty.len();
        let result = self.run_dirty_propagators();
        if result.conflict.is_some() || !result.clauses.is_empty() {
            return result;
        }

        if let Some(conflict) = self.check_lazy_neqs() {
            return ExtPropagateResult::conflict(conflict);
        }
        result
    }

    fn model_value(&self, model: &[bool], var: IntVarId) -> i64 {
        let (lb, ub) = self.encoder.var_bounds(var);
        if lb == ub {
            return lb;
        }

        let mut lo = lb + 1;
        let mut hi = ub;
        let mut value = lb;

        while lo <= hi {
            let mid = lo + (hi - lo) / 2;
            let is_true = self
                .encoder
                .lookup_ge(var, mid)
                .map(|lit| model_lit_is_true(model, lit))
                .unwrap_or(false);

            if is_true {
                value = mid;
                match mid.checked_add(1) {
                    Some(next) => lo = next,
                    None => break,
                }
            } else {
                match mid.checked_sub(1) {
                    Some(prev) => hi = prev,
                    None => break,
                }
            }
        }

        value
    }

    fn check_lazy_neqs(&self) -> Option<Vec<Literal>> {
        // Check lazy neq constraints on the complete assignment.
        // For each violated x - y != offset, generate a blocking clause:
        // ¬[x >= vx] ∨ [x >= vx+1] ∨ ¬[y >= vy] ∨ [y >= vy+1]
        for neq in &self.lazy_neqs {
            let vx = self.trail.lb(neq.x);
            let vy = self.trail.lb(neq.y);
            if vx - vy == neq.offset {
                // Violation: x - y == offset. Generate blocking clause.
                // All 4 literals must be present; a partial clause is unsound
                // because it learns a stronger-than-justified constraint (#5986).
                // The only allowed omission is a [x >= ub+1] style literal at
                // i64::MAX, which is semantically false and safely simplifies.
                let clause = (|| -> Option<Vec<Literal>> {
                    let mut clause = Vec::with_capacity(4);
                    clause.push(self.encoder.lookup_ge(neq.x, vx)?.negated());
                    if let Some(next_vx) = vx.checked_add(1) {
                        clause.push(self.encoder.lookup_ge(neq.x, next_vx)?);
                    }
                    clause.push(self.encoder.lookup_ge(neq.y, vy)?.negated());
                    if let Some(next_vy) = vy.checked_add(1) {
                        clause.push(self.encoder.lookup_ge(neq.y, next_vy)?);
                    }
                    Some(clause)
                })();
                if let Some(clause) = clause {
                    return Some(clause);
                }
                // Explanation incomplete — skip this neq violation.
                // The SAT solver will discover it via BCP.
            }
        }

        None
    }
}

fn model_lit_is_true(model: &[bool], lit: Literal) -> bool {
    let idx = lit.variable().index();
    idx < model.len() && model[idx] == lit.is_positive()
}

impl Extension for CpExtension {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.sync_from_sat(ctx);
        self.run_dirty_propagators()
    }

    fn asserted(&mut self, lit: Literal) {
        // Eager notification: decode literal to bound change immediately.
        // Note: ay-sat does NOT call this method — use propagate() instead.
        self.process_literal(lit);
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.sync_from_sat(ctx);

        // Run all propagators one more time to detect any missed conflicts
        self.dirty.fill(true);
        self.dirty_count = self.dirty.len();
        let result = self.run_dirty_propagators();
        if let Some(conflict) = result.conflict {
            return ExtCheckResult::Conflict(conflict);
        }

        // If propagators generated clauses (bounds on auxiliary variables
        // like Big-M indicators that the SAT solver never assigned), return
        // them so the SAT solver incorporates them and continues searching.
        // Without this, these clauses are silently discarded and check()
        // returns Sat, accepting models that violate CP constraints.
        if !result.clauses.is_empty() {
            return ExtCheckResult::AddClauses(result.clauses);
        }

        if let Some(conflict) = self.check_lazy_neqs() {
            return ExtCheckResult::Conflict(conflict);
        }

        ExtCheckResult::Sat
    }

    fn backtrack(&mut self, _new_level: u32) {
        // Lazy backtrack: defer the actual integer trail backtrack to the
        // next propagate() call, which has access to the SAT context and
        // can determine the actual target level (important for restarts
        // with trail reuse where SAT backtracks to reuse_level, not 0).
        self.needs_resync = true;
        self.search.notify_backtrack();
    }

    fn init(&mut self) {
        // #5910: Fully reset the integer trail to original registered bounds.
        // `backtrack_to(0)` leaves level-0 entries from a previous solve
        // intact, causing stale bounds to persist across incremental solves.
        self.trail.reset_all();
        self.dirty.fill(true);
        self.dirty_count = self.dirty.len();
        self.last_trail_pos = 0;
        self.level_trail_pos.clear();
        self.needs_resync = false;
    }

    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        if self.needs_resync {
            return true;
        }
        let trail_len = ctx.trail().len();
        if trail_len != self.last_trail_pos {
            return true;
        }
        self.dirty_count > 0
    }

    fn suggest_decision(&self, ctx: &dyn SolverContext) -> Option<Literal> {
        // Use the configured search heuristic to select a variable
        let var = self
            .search
            .select_variable(&self.trail, &self.encoder, ctx)?;

        // Create a decision literal (lower-bound first)
        self.search
            .make_decision(var, &self.trail, &self.encoder, ctx)
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        // For optimization: guide objective variable literals toward the
        // optimal direction. Only fires for SAT variables that encode the
        // objective's order-encoding literals; returns None for all others
        // (letting the SAT solver use its default phase heuristic).
        let (obj_var, minimize) = self.objective?;
        let bound_lit = self.encoder.decode(var)?;
        if bound_lit.var != obj_var {
            return None;
        }
        // For [obj >= v] (is_ge = true, positive literal):
        //   minimize → prefer false (obj < v, small objective)
        //   maximize → prefer true (obj >= v, large objective)
        Some(!minimize)
    }
}
