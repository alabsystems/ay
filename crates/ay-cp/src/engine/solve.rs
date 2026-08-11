// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve loop and propagation orchestration for the CP-SAT engine.
//!
//! Contains `solve()`, root propagation, pure SAT path, CP extension
//! path, and assignment extraction. Extracted from `mod.rs` to keep
//! each file under 500 lines.

use std::time::Instant;

use crate::propagator::{PropagationResult, Propagator};
use crate::variable::IntVarId;

pub(super) use super::extension::CpExtension;
use super::{CpSatEngine, CpSolveResult};

impl CpSatEngine {
    /// Solve the constraint model.
    ///
    /// Compiles constraints into SAT clauses and propagators, pre-allocates
    /// all order-encoding literals, then runs the SAT solver with the CP
    /// extension for LCG propagation during search.
    ///
    /// Supports incremental solving: call `solve()` multiple times after adding
    /// constraints or tightening bounds via `add_upper_bound`/`add_lower_bound`.
    /// Search state (learned clauses, heuristic weights) is preserved.
    pub fn solve(&mut self) -> CpSolveResult {
        if self.permanently_inconsistent {
            return CpSolveResult::Unsat;
        }
        if self.prepare_domain_holes().is_err() {
            return CpSolveResult::Unknown;
        }
        // #5910: Reset state for incremental solving. trail.reset_all() restores
        // original bounds (backtrack_to(0) leaves stale level-0 entries).
        // clear_empty_clause() prevents a previous UNSAT from poisoning all
        // subsequent solves — root cause of false UNSAT in optimization.
        //
        // Learned clauses (including theory lemmas from CP propagators) are
        // preserved across incremental solves. They are valid consequences of
        // the permanent constraint database and remain sound when new bound
        // constraints are added. This is standard practice in incremental SAT
        // solvers (CaDiCaL, MiniSat, Z3) and avoids re-deriving expensive
        // learned knowledge on each optimization iteration.
        self.trail.reset_all();
        self.sat.clear_empty_clause();

        // Detect AllDifferent patterns from pairwise neq decompositions
        // before compiling — enables bounds propagation instead of O(n²d) encoding.
        self.detect_alldifferent();
        self.detect_shifted_alldifferent();
        #[cfg(debug_assertions)]
        self.debug_constraints
            .extend(self.constraints.iter().cloned());
        self.compile_constraints();
        if self.prepare_domain_holes().is_err() {
            return CpSolveResult::Unknown;
        }
        if self.encoder.try_pre_allocate_all(&mut self.sat).is_err() {
            return CpSolveResult::Unknown;
        }

        // Start the SAT interrupt timer AFTER encoding completes (#5683).
        // This ensures encoding time does not consume the solving budget.
        if let Some(dl) = self.deadline {
            let remaining = dl.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return CpSolveResult::Unknown;
            }
            self.clear_interrupt();
            self.set_timeout(remaining);
        }

        if let Some(conflict) = self.apply_root_propagation() {
            return conflict;
        }

        if self.propagators.is_empty() && self.lazy_neqs.is_empty() {
            return self.solve_pure_sat();
        }

        self.solve_with_cp_extension(&[])
    }

    /// Solve with a subset of integer variables temporarily fixed to given
    /// values (via retractable SAT assumptions), without rebuilding the model.
    ///
    /// Each `(x, v)` is asserted as `[x >= v] ∧ [x <= v]` (i.e. `x = v`) for the
    /// duration of this solve only; the assumptions are automatically retracted
    /// on return, so repeated calls with different fix-sets reuse the compiled
    /// model, learned clauses, and heuristic state. This is the rebuild-free
    /// primitive for Large Neighborhood Search (freeze the incumbent outside a
    /// neighborhood, re-optimize inside it).
    pub fn solve_under_assumptions(&mut self, fixings: &[(IntVarId, i64)]) -> CpSolveResult {
        if self.permanently_inconsistent {
            return CpSolveResult::Unsat;
        }
        if self.prepare_domain_holes().is_err() {
            return CpSolveResult::Unknown;
        }
        self.trail.reset_all();
        self.sat.clear_empty_clause();
        self.detect_alldifferent();
        self.detect_shifted_alldifferent();
        self.compile_constraints();
        if self.prepare_domain_holes().is_err() {
            return CpSolveResult::Unknown;
        }
        if self.encoder.try_pre_allocate_all(&mut self.sat).is_err() {
            return CpSolveResult::Unknown;
        }

        if let Some(dl) = self.deadline {
            let remaining = dl.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return CpSolveResult::Unknown;
            }
            self.clear_interrupt();
            self.set_timeout(remaining);
        }

        if let Some(conflict) = self.apply_root_propagation() {
            return conflict;
        }

        // Build assumption literals for each fixing: [x >= v] AND [x <= v].
        let mut assumptions = Vec::with_capacity(fixings.len() * 2);
        for &(var, val) in fixings {
            // `get_or_create_le` returns the negation of the corresponding
            // `is_ge` literal, so the CP extension still decodes it as an upper
            // bound. It also handles `i64::MAX` without overflowing `val + 1`.
            assumptions.push(self.encoder.get_or_create_ge(&mut self.sat, var, val));
            assumptions.push(self.encoder.get_or_create_le(&mut self.sat, var, val));
        }

        if self.propagators.is_empty() && self.lazy_neqs.is_empty() {
            // No CP propagators: a pure SAT assumption solve suffices.
            let result = self.sat.solve_with_assumptions(&assumptions);
            return if let Some(model) = result.model() {
                CpSolveResult::Sat(self.extract_assignment(model))
            } else if result.is_unsat() {
                CpSolveResult::Unsat
            } else {
                CpSolveResult::Unknown
            };
        }

        self.solve_with_cp_extension(&assumptions)
    }

    /// Run propagators at root level and feed resulting clauses to SAT.
    /// Returns `Some(CpSolveResult)` on root conflict, `None` to continue.
    fn apply_root_propagation(&mut self) -> Option<CpSolveResult> {
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

    /// SAT solving with CP extension (LCG propagation during search).
    fn solve_with_cp_extension(&mut self, assumptions: &[ay_sat::Literal]) -> CpSolveResult {
        loop {
            let num_vars = self.trail.num_vars();
            // Reuse search state from previous solve if available (preserves
            // dom/wdeg weights and activity scores for incremental optimization).
            let search = self.search_state.take().unwrap_or_else(|| {
                crate::search::SearchState::new(
                    self.search_strategy,
                    self.value_choice,
                    std::mem::take(&mut self.search_vars),
                    &self.propagators,
                    num_vars,
                )
            });
            let dirty = std::mem::take(&mut self.dirty);
            let dirty_count = dirty.iter().filter(|&&d| d).count();
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
                var_to_props: Vec::new(),
                priority_order: Vec::new(),
                level_trail_pos: Vec::new(),
                needs_resync: false,
                ws_all_clauses: Vec::new(),
            };
            ext.build_var_to_props();

            let sat_result = if assumptions.is_empty() {
                self.sat.solve_with_extension(&mut ext)
            } else {
                self.sat
                    .solve_with_extension_and_assumptions(&mut ext, assumptions)
            };

            if let Some(model) = sat_result.model() {
                let verification = ext.verify_complete_model(model);
                if let Some(conflict) = verification.conflict {
                    self.sat.add_clause(conflict);
                    self.restore_cp_extension(ext);
                    continue;
                }
                if !verification.clauses.is_empty() {
                    for clause in verification.clauses {
                        self.sat.add_clause(clause);
                    }
                    self.restore_cp_extension(ext);
                    continue;
                }

                self.restore_cp_extension(ext);
                let assignment = self.extract_assignment(model);
                #[cfg(debug_assertions)]
                self.debug_validate_assignment(&assignment);
                return CpSolveResult::Sat(assignment);
            }

            self.restore_cp_extension(ext);
            return if sat_result.is_unsat() {
                CpSolveResult::Unsat
            } else {
                CpSolveResult::Unknown
            };
        }
    }

    fn restore_cp_extension(&mut self, ext: CpExtension) {
        self.trail = ext.trail;
        self.encoder = ext.encoder;
        self.propagators = ext.propagators;
        self.dirty = ext.dirty;
        self.search_state = Some(ext.search);
        self.lazy_neqs = ext.lazy_neqs;
    }

    /// Register a propagator and mark it dirty.
    pub(crate) fn add_propagator(&mut self, prop: impl Propagator + 'static) {
        self.dirty.push(true);
        self.propagators.push(Box::new(prop));
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
    fn extract_assignment(&self, model: &[bool]) -> Vec<(IntVarId, i64)> {
        let mut assignment = Vec::new();

        for var_idx in 0..self.encoder.num_vars() {
            let var = IntVarId(var_idx as u32);
            let (lb, ub) = self.encoder.var_bounds(var);

            // Find the highest v such that [x >= v] is true in the model.
            let mut value = lb;
            let Some(mut v) = lb.checked_add(1) else {
                assignment.push((var, value));
                continue;
            };
            while v <= ub {
                if let Some(lit) = self.encoder.lookup_ge(var, v) {
                    let sat_var = lit.variable();
                    if sat_var.index() < model.len() && model[sat_var.index()] == lit.is_positive()
                    {
                        value = v;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
                let Some(next_v) = v.checked_add(1) else {
                    break;
                };
                v = next_v;
            }

            assignment.push((var, value));
        }

        assignment
    }

    /// Solve using pure SAT (no CP extension propagators during search).
    ///
    /// Compiles constraints into SAT clauses and propagators, but then
    /// drops all propagators and lazy neqs before solving. This is useful
    /// for diagnosing whether bugs are in the SAT encoding vs CP propagation.
    pub fn solve_pure_sat_only(&mut self) -> CpSolveResult {
        if self.permanently_inconsistent {
            return CpSolveResult::Unsat;
        }
        if self.prepare_domain_holes().is_err() {
            return CpSolveResult::Unknown;
        }
        self.trail.backtrack_to(0);
        self.detect_alldifferent();
        self.detect_shifted_alldifferent();
        self.compile_constraints();
        if self.prepare_domain_holes().is_err() {
            return CpSolveResult::Unknown;
        }
        if self.encoder.try_pre_allocate_all(&mut self.sat).is_err() {
            return CpSolveResult::Unknown;
        }
        // Drop all propagators — solve with SAT clauses only
        self.propagators.clear();
        self.dirty.clear();
        self.lazy_neqs.clear();
        self.solve_pure_sat()
    }
}
