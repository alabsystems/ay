// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve-loop internals: root propagation, extension assembly, and assignment
//! extraction. Split from `mod.rs` to keep the public API surface separate
//! from the inner solve mechanics.

use crate::propagator::PropagationResult;
use crate::search::SearchState;
use crate::variable::IntVarId;

use super::{CpExtension, CpSatEngine, CpSolveResult};

impl CpSatEngine {
    /// Run propagators at root level and feed resulting clauses to SAT.
    /// Returns `Some(CpSolveResult)` on root conflict, `None` to continue.
    pub(super) fn apply_root_propagation(&mut self) -> Option<CpSolveResult> {
        match self.propagate_all() {
            PropagationResult::Conflict(clause) => {
                if clause.is_empty() {
                    return Some(CpSolveResult::Unsat);
                }
                // Non-empty conflict clause: add to SAT and let SAT resolve it.
                // Do NOT return Unsat — a non-empty conflict means the clause is
                // falsified under current trail bounds, not that the problem is
                // unsatisfiable. The SAT solver's CDCL can resolve it.
                self.sat.add_clause(clause);
                None
            }
            PropagationResult::Propagated(clauses) => {
                for clause in clauses {
                    debug_assert!(
                        !clause.is_empty(),
                        "BUG: propagator produced empty propagation clause (#5910)"
                    );
                    if clause.is_empty() {
                        continue; // Skip empty clauses in release to avoid mark_empty_clause
                    }
                    self.sat.add_clause(clause);
                }
                None
            }
            PropagationResult::NoChange => None,
        }
    }

    /// Pure SAT solving (no propagators — eager encoding only).
    pub(super) fn solve_pure_sat(&mut self) -> CpSolveResult {
        let result = self.sat.solve();
        if let Some(model) = result.model() {
            let assignment = self.extract_assignment(model);
            #[cfg(debug_assertions)]
            self.debug_validate_assignment(&assignment);
            CpSolveResult::Sat(assignment)
        } else if result.is_unsat() {
            CpSolveResult::Unsat
        } else {
            CpSolveResult::Unknown
        }
    }

    /// Move CP state into a CpExtension for SAT solving.
    /// After calling, `self` fields are empty (taken by the extension).
    /// Single source of truth for the field set — both `solve_with_cp_extension`
    /// and `probe_bound_feasible_cp` use this to avoid duplicated assembly.
    pub(super) fn assemble_extension(&mut self) -> CpExtension {
        let num_vars = self.trail.num_vars();
        let search = self.search_state.take().unwrap_or_else(|| {
            SearchState::new(
                self.search_strategy,
                self.value_choice,
                std::mem::take(&mut self.search_vars),
                &self.propagators,
                num_vars,
            )
        });
        let dirty = std::mem::take(&mut self.dirty);
        let dirty_count = dirty.iter().filter(|&&d| d).count();
        let needs_build = self.var_to_props_lb.is_empty();
        let mut ext = CpExtension {
            trail: std::mem::take(&mut self.trail),
            encoder: std::mem::take(&mut self.encoder),
            propagators: std::mem::take(&mut self.propagators),
            dirty_count,
            dirty,
            last_trail_pos: 0,
            search,
            lazy_neqs: std::mem::take(&mut self.lazy_neqs),
            objective: self.objective,
            var_to_props_lb: std::mem::take(&mut self.var_to_props_lb),
            var_to_props_ub: std::mem::take(&mut self.var_to_props_ub),
            priority_order: std::mem::take(&mut self.priority_order),
            prop_to_priority_pos: std::mem::take(&mut self.prop_to_priority_pos),
            next_dirty_hint: 0,
            level_trail_pos: std::mem::take(&mut self.level_trail_pos),
            needs_resync: false,
            ws_all_clauses: std::mem::take(&mut self.ws_all_clauses),
            restart_count: 0,
            found_solution: self.found_solution,
            proof_mode: self.proof_mode,
            best_solution: std::mem::take(&mut self.best_solution),
            pending_wipeout: None,
        };
        if needs_build {
            ext.build_var_to_props();
        }
        ext
    }

    /// Move CP state back from a CpExtension after SAT solving.
    pub(super) fn restore_from_extension(&mut self, ext: CpExtension) {
        self.trail = ext.trail;
        self.encoder = ext.encoder;
        self.propagators = ext.propagators;
        self.dirty = ext.dirty;
        self.search_state = Some(ext.search);
        self.lazy_neqs = ext.lazy_neqs;
        self.var_to_props_lb = ext.var_to_props_lb;
        self.var_to_props_ub = ext.var_to_props_ub;
        self.priority_order = ext.priority_order;
        self.prop_to_priority_pos = ext.prop_to_priority_pos;
        self.level_trail_pos = ext.level_trail_pos;
        self.ws_all_clauses = ext.ws_all_clauses;
        self.best_solution = ext.best_solution;
    }

    /// SAT solving with CP extension (LCG propagation during search).
    ///
    /// Includes post-solve model verification: after the SAT solver returns
    /// a model, all CP propagators are re-run to catch violations that the
    /// CDCL check() may have missed. This happens OUTSIDE the CDCL loop
    /// to avoid changing learned clause quality or search dynamics (#7670).
    pub(super) fn solve_with_cp_extension(&mut self) -> CpSolveResult {
        loop {
            let mut ext = self.assemble_extension();
            let sat_result = self.sat.solve_with_extension(&mut ext);

            if let Some(model) = sat_result.model() {
                // Post-solve verification: tighten CP trail to exact model
                // values, then re-run ALL propagators. Catches violations
                // that the CDCL check() guard missed (#7670).
                if let Some(conflict) = ext.verify_complete_model(model) {
                    self.sat.add_clause(conflict);
                    self.restore_from_extension(ext);
                    continue;
                }

                self.restore_from_extension(ext);
                let assignment = self.extract_assignment(model);
                #[cfg(debug_assertions)]
                self.debug_validate_assignment(&assignment);
                return CpSolveResult::Sat(assignment);
            } else {
                self.restore_from_extension(ext);
                return if sat_result.is_unsat() {
                    CpSolveResult::Unsat
                } else {
                    CpSolveResult::Unknown
                };
            }
        }
    }

    /// Run all propagators once at root level (no fixpoint — that happens
    /// inside the CDCL loop via the Extension). This is just to detect
    /// immediate conflicts and generate initial propagation clauses.
    fn propagate_all(&mut self) -> PropagationResult {
        let mut all_clauses = Vec::new();

        for i in 0..self.propagators.len() {
            let result = self.propagators[i].propagate(&self.trail, &self.encoder);

            match result {
                PropagationResult::NoChange => {}
                PropagationResult::Propagated(clauses) => {
                    all_clauses.extend(clauses);
                }
                PropagationResult::Conflict(clause) => {
                    return PropagationResult::Conflict(clause);
                }
            }
        }

        self.dirty.fill(false);

        if all_clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(all_clauses)
        }
    }

    /// Extract integer assignment from SAT model.
    ///
    /// Uses binary search on the order encoding: `[x >= v]` is true for all
    /// v <= value and false for v > value. O(V * log D) instead of O(V * D).
    pub(super) fn extract_assignment(&self, model: &[bool]) -> Vec<(IntVarId, i64)> {
        let mut assignment = Vec::new();

        for var_idx in 0..self.encoder.num_vars() {
            let var = IntVarId(var_idx as u32);
            let (lb, ub) = self.encoder.var_bounds(var);

            if lb == ub {
                assignment.push((var, lb));
                continue;
            }

            // Binary search for the largest v in [lb+1, ub] where [x >= v] is true.
            // Invariant: lo-1 is true, hi+1 is false (or out of range).
            let mut lo = lb + 1;
            let mut hi = ub;
            let mut value = lb;

            while lo <= hi {
                let mid = lo + (hi - lo) / 2;
                let is_true = self
                    .encoder
                    .lookup_ge(var, mid)
                    .map(|lit| {
                        let sv = lit.variable();
                        sv.index() < model.len() && model[sv.index()] == lit.is_positive()
                    })
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

            assignment.push((var, value));
        }

        assignment
    }
}
