// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! XOR theory extension for SAT solver integration.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_sat::{ExtCheckResult, ExtPropagateResult, Extension, Literal, SolverContext, Variable};

use crate::component::split_components;
use crate::constraint::XorConstraint;
use crate::gaussian::chunked_proof::{ChunkedComponentState, MAX_XOR_CHUNKED_PROOF_TOTAL_CLAUSES};
use crate::gaussian::{GaussResult, GaussianSolver};
use crate::preprocess::{component_within_limits, MAX_NUM_MATRICES};
use crate::VarId;
use ay_sat::ExtProofStep;

/// An assignment record for backtracking.
#[derive(Debug, Clone)]
struct AssignmentRecord {
    /// The variable that was assigned.
    var: VarId,
    /// The decision level at which the assignment was made.
    level: u32,
}

/// A pending propagation with its source RREF row and component.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PendingPropagation {
    /// The literal to propagate.
    lit: Literal,
    /// The RREF row index (local to the component) that caused this propagation.
    source_row: usize,
    /// The component index that produced this propagation.
    component: usize,
}

/// Chunked proof emission state (see `gaussian::chunked_proof`).
#[derive(Debug)]
struct ChunkedProofState {
    /// Per accepted component, aligned with `XorExtension::components`.
    comps: Vec<ChunkedComponentState>,
    /// Next fresh DRAT extension variable. Starts at the DIMACS variable
    /// count (all fresh variables live ABOVE the input range and are
    /// proof-only — they never reach the solver or a model).
    next_fresh: VarId,
}

/// Per-component solver state.
#[derive(Debug)]
struct ComponentSolver {
    /// The Gaussian elimination solver for this component.
    solver: GaussianSolver,
    /// Global row offset: the first row of this component in the
    /// flattened constraint list. Used to translate component-local
    /// row indices back to global indices for `PendingPropagation`.
    row_offset: usize,
}

/// XOR theory extension for SAT solver integration.
///
/// This implements the `Extension` trait to integrate Gauss-Jordan XOR solving
/// with the SAT solver. It tracks assignments, detects conflicts and unit
/// propagations, and supports backtracking.
///
/// When the XOR constraint system decomposes into independent connected
/// components (constraints that share no variables), each component gets
/// its own `GaussianSolver` instance. This reduces per-row evaluation cost
/// because Gauss-Jordan elimination is O(n*m*k) and splitting into smaller
/// matrices reduces all three dimensions per component.
///
/// Reference: CryptoMiniSat `matrixfinder.cpp` (MIT license).
///
/// # Usage
///
/// ```rust
/// use ay_xor::{XorConstraint, XorExtension};
///
/// // Create XOR constraints
/// let constraints = vec![
///     XorConstraint::new(vec![0, 1], true),  // x0 XOR x1 = 1
///     XorConstraint::new(vec![1, 2], false), // x1 XOR x2 = 0
/// ];
///
/// // Create extension
/// let ext = XorExtension::new(constraints);
///
/// // Add to SAT solver (solver.set_extension(ext))
/// ```
#[derive(Debug)]
pub struct XorExtension {
    /// Per-component Gaussian solvers. When the constraint system is fully
    /// connected, this has exactly one entry (no splitting overhead).
    components: Vec<ComponentSolver>,
    /// Per-component count of elimination-trace rows already emitted as DRAT
    /// helper clauses (task #20): derived-row conflict/reason clauses are only
    /// RUP once their row encodings are in the proof stream, and each row must
    /// be emitted at most once or the proof bloats per conflict.
    emitted_proof_rows: Vec<usize>,
    /// Cached whole-extension proof-ladder feasibility. Elimination traces are
    /// immutable after construction, so recomputing the width/count walk on
    /// every propagation would be pure hot-path overhead.
    proof_ladders_complete: bool,
    /// Chunked (Tseitin-chain) proof emission state, built on demand by
    /// [`Self::set_proof_fresh_var_base`] when the monolithic ladder envelope
    /// is exceeded but the trace fits the chunked budget. `Some` switches the
    /// proof drains from monolithic DB lemmas to lazy proof-only cone
    /// emission over fresh DRAT extension variables.
    chunked: Option<ChunkedProofState>,
    /// Map from variable ID to component index for O(1) routing.
    var_to_component: HashMap<VarId, usize>,
    /// Original constraints (flat, needed for final soundness check).
    constraints: Vec<XorConstraint>,
    /// Trail of assignments with their levels (for backtracking).
    trail: Vec<AssignmentRecord>,
    /// Last trail position we processed.
    last_trail_pos: usize,
    /// Pending propagations (unit literals found by Gauss) with source row.
    pub(crate) pending_propagations: Vec<PendingPropagation>,
    /// Current conflict (if any) with source row index.
    pub(crate) conflict: Option<(Vec<Literal>, Option<usize>)>,
    /// Whether we need to propagate.
    pub(crate) needs_propagate: bool,
    /// Whether the tracked assignment state must be rebuilt from the SAT trail.
    needs_resync: bool,
    /// Set by `backtrack()` to indicate it already handled state cleanup.
    /// When true, `sync_with_context()` skips the expensive rebuild and
    /// just updates `last_trail_pos` to match the SAT trail length.
    backtrack_handled: bool,
    /// Debug counter: propagate calls.
    #[cfg(debug_assertions)]
    debug_propagate_calls: std::cell::Cell<u64>,
    /// Debug counter: backtrack calls.
    #[cfg(debug_assertions)]
    debug_backtrack_calls: std::cell::Cell<u64>,
}

impl XorExtension {
    /// Create a new XOR extension with the given constraints.
    ///
    /// Automatically splits the constraint system into independent connected
    /// components, each with its own `GaussianSolver`. If all constraints
    /// share variables (single component), there is no extra overhead.
    pub fn new(constraints: Vec<XorConstraint>) -> Self {
        let xor_components = split_components(&constraints);

        let mut components = Vec::with_capacity(xor_components.len());
        let mut var_to_component: HashMap<VarId, usize> = HashMap::default();
        let mut initial_props = Vec::new();
        let mut conflict = None;
        let mut row_offset = 0usize;

        // Filter and limit components per CMS heuristics:
        // 1. Skip components outside matrix size bounds (too small or too large)
        // 2. Keep at most MAX_NUM_MATRICES components (largest first by sum_xor_sizes,
        //    already sorted by split_components)
        // Reference: cryptominisat/src/matrixfinder.cpp:235-286
        let mut accepted = 0usize;
        for comp in xor_components {
            // Use pre-computed stats from split_components to avoid
            // redundant row/col counting.
            let num_rows = comp.stats.rows;
            let num_cols = comp.stats.cols;
            let comp_constraints = comp.constraints;

            // Skip components outside size bounds
            if !component_within_limits(num_rows, num_cols) {
                row_offset += num_rows;
                continue;
            }

            // Limit total number of matrices
            if accepted >= MAX_NUM_MATRICES {
                row_offset += num_rows;
                continue;
            }
            accepted += 1;

            let comp_idx = components.len();
            let mut solver = GaussianSolver::new(&comp_constraints);
            let result = solver.eliminate();

            // Build var -> component map
            for c in &comp_constraints {
                for &var in &c.vars {
                    var_to_component.insert(var, comp_idx);
                }
            }

            // Check for initial conflict
            if conflict.is_none() {
                if let GaussResult::Conflict(local_row) = result {
                    let clause: Vec<Literal> = solver
                        .get_row_variables(local_row)
                        .into_iter()
                        .map(|(var_id, _col)| Literal::positive(Variable::new(var_id)))
                        .collect();
                    let global_row = row_offset + local_row;
                    conflict = Some((clause, Some(global_row)));
                }
            }

            // Collect initial propagations
            for (lit, local_row) in solver.get_all_propagations() {
                initial_props.push(PendingPropagation {
                    lit,
                    source_row: local_row,
                    component: comp_idx,
                });
            }

            let comp_len = comp_constraints.len();
            components.push(ComponentSolver { solver, row_offset });
            row_offset += comp_len;
        }

        let needs_propagate = !initial_props.is_empty() || conflict.is_some();
        let proof_ladders_complete = Self::components_have_complete_proof_ladders(&components);

        Self {
            emitted_proof_rows: vec![0; components.len()],
            proof_ladders_complete,
            chunked: None,
            components,
            var_to_component,
            constraints,
            trail: Vec::new(),
            last_trail_pos: 0,
            pending_propagations: initial_props,
            conflict,
            needs_propagate,
            needs_resync: false,
            backtrack_handled: false,
            #[cfg(debug_assertions)]
            debug_propagate_calls: std::cell::Cell::new(0),
            #[cfg(debug_assertions)]
            debug_backtrack_calls: std::cell::Cell::new(0),
        }
    }

    /// Get the number of XOR constraints.
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Get the number of variables in XOR constraints.
    pub fn num_variables(&self) -> usize {
        self.var_to_component.len()
    }

    /// Get the number of independent XOR components.
    pub fn num_components(&self) -> usize {
        self.components.len()
    }

    /// Check if a variable is in any XOR constraint.
    pub fn contains_var(&self, var: VarId) -> bool {
        self.var_to_component.contains_key(&var)
    }

    /// Get the original XOR constraints.
    pub fn constraints(&self) -> &[XorConstraint] {
        &self.constraints
    }

    /// Build a conflict clause from a specific RREF row in a specific component.
    fn build_conflict_clause_from_row(&self, comp_idx: usize, local_row: usize) -> Vec<Literal> {
        let comp = &self.components[comp_idx];
        comp.solver
            .get_row_variables(local_row)
            .into_iter()
            .filter_map(|(var_id, col)| {
                if let Some(value) = comp.solver.assignment_at(col) {
                    let var = Variable::new(var_id);
                    Some(if value {
                        Literal::negative(var)
                    } else {
                        Literal::positive(var)
                    })
                } else {
                    None
                }
            })
            .collect()
    }

    /// Build a reason clause for a propagated literal from a specific RREF row.
    fn build_propagation_clause_from_row(
        &self,
        propagated: Literal,
        comp_idx: usize,
        local_row: usize,
    ) -> Option<Vec<Literal>> {
        let comp = &self.components[comp_idx];
        let row_vars = comp.solver.get_row_variables(local_row);
        let mut clause = Vec::with_capacity(row_vars.len());
        clause.push(propagated);

        for (var_id, col) in row_vars {
            if var_id == propagated.variable().id() {
                continue;
            }

            let value = comp.solver.assignment_at(col)?;
            let var = Variable::new(var_id);
            clause.push(if value {
                Literal::negative(var)
            } else {
                Literal::positive(var)
            });
        }

        Some(clause)
    }

    /// Record propagation/conflict from a component's Gaussian solver.
    ///
    /// Returns `true` if a conflict was found.
    fn record_gauss_result(
        &mut self,
        result: GaussResult,
        comp_idx: usize,
        ctx: &dyn SolverContext,
    ) -> bool {
        match result {
            GaussResult::Conflict(local_row) => {
                let conflict = self.build_conflict_clause_from_row(comp_idx, local_row);
                let global_row = self.components[comp_idx].row_offset + local_row;
                self.conflict = Some((conflict, Some(global_row)));
                self.needs_propagate = true;
                self.last_trail_pos = ctx.trail().len();
                true
            }
            GaussResult::Propagate(prop_lit, local_row) => {
                if ctx.value(prop_lit.variable()).is_none() {
                    self.pending_propagations.push(PendingPropagation {
                        lit: prop_lit,
                        source_row: local_row,
                        component: comp_idx,
                    });
                }
                false
            }
            GaussResult::MultiPropagate(props) => {
                for (prop_lit, local_row) in props {
                    if ctx.value(prop_lit.variable()).is_none() {
                        self.pending_propagations.push(PendingPropagation {
                            lit: prop_lit,
                            source_row: local_row,
                            component: comp_idx,
                        });
                    }
                }
                false
            }
            GaussResult::Nothing => false,
        }
    }

    /// Rebuild tracked assignments and pending state from the SAT trail.
    fn rebuild_from_context(&mut self, ctx: &dyn SolverContext) {
        for comp in &mut self.components {
            comp.solver.clear_assignments();
        }
        self.trail.clear();
        self.pending_propagations.clear();
        self.conflict = None;
        self.last_trail_pos = 0;

        let current_level = ctx.decision_level();
        for &lit in ctx.trail() {
            let var = lit.variable();
            let var_id = var.id();
            if let Some(&comp_idx) = self.var_to_component.get(&var_id) {
                let level = ctx.var_level(var).unwrap_or(current_level);
                self.trail.push(AssignmentRecord { var: var_id, level });
                let _ = self.components[comp_idx]
                    .solver
                    .assign(var_id, lit.is_positive());
            }
        }

        // Collect propagations and conflicts from all components
        for (comp_idx, comp) in self.components.iter().enumerate() {
            for (lit, local_row) in comp.solver.get_all_propagations() {
                if ctx.value(lit.variable()).is_none() {
                    self.pending_propagations.push(PendingPropagation {
                        lit,
                        source_row: local_row,
                        component: comp_idx,
                    });
                }
            }
            if self.conflict.is_none() {
                if let Some(local_row) = comp.solver.find_conflict_row() {
                    let clause = self.build_conflict_clause_from_row(comp_idx, local_row);
                    let global_row = comp.row_offset + local_row;
                    self.conflict = Some((clause, Some(global_row)));
                }
            }
        }

        self.last_trail_pos = ctx.trail().len();
        self.needs_resync = false;
        self.backtrack_handled = false;
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }

    /// Synchronize the XOR solver with the SAT trail.
    fn sync_with_context(&mut self, ctx: &dyn SolverContext) {
        if self.backtrack_handled {
            // backtrack() correctly maintained Gaussian state via unassign().
            // Trail compaction invalidates last_trail_pos. Resync efficiently
            // without clearing assignments (O(1) per surviving variable).
            self.backtrack_handled = false;
            self.resync_after_backtrack(ctx);
            return;
        }
        if self.needs_resync || self.last_trail_pos > ctx.trail().len() {
            self.rebuild_from_context(ctx);
        } else {
            self.process_assignments(ctx);
        }
    }

    /// Efficient resync after backtrack without clearing assignments.
    ///
    /// The Gaussian solver state is correct (maintained by backtrack()).
    /// We rebuild the XOR trail and process new assignments using
    /// assign() idempotency to skip already-assigned variables in O(1).
    fn resync_after_backtrack(&mut self, ctx: &dyn SolverContext) {
        self.trail.clear();
        self.pending_propagations.clear();
        self.conflict = None;
        let current_level = ctx.decision_level();
        for &lit in ctx.trail() {
            let var = lit.variable();
            let var_id = var.id();
            let Some(&comp_idx) = self.var_to_component.get(&var_id) else {
                continue;
            };
            let level = ctx.var_level(var).unwrap_or(current_level);
            self.trail.push(AssignmentRecord { var: var_id, level });
            let value = lit.is_positive();
            let result = self.components[comp_idx].solver.assign(var_id, value);
            if self.record_gauss_result(result, comp_idx, ctx) {
                self.needs_resync = false;
                return;
            }
        }
        for (comp_idx, comp) in self.components.iter().enumerate() {
            for (lit, local_row) in comp.solver.get_all_propagations() {
                if ctx.value(lit.variable()).is_none() {
                    self.pending_propagations.push(PendingPropagation {
                        lit,
                        source_row: local_row,
                        component: comp_idx,
                    });
                }
            }
            if self.conflict.is_none() {
                if let Some(local_row) = comp.solver.find_conflict_row() {
                    let clause = self.build_conflict_clause_from_row(comp_idx, local_row);
                    let global_row = comp.row_offset + local_row;
                    self.conflict = Some((clause, Some(global_row)));
                }
            }
        }
        self.last_trail_pos = ctx.trail().len();
        self.needs_resync = false;
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }

    /// Process new assignments and route to the correct component solver.
    fn process_assignments(&mut self, ctx: &dyn SolverContext) {
        let new_lits = ctx.new_assignments(self.last_trail_pos);
        let current_level = ctx.decision_level();

        for &lit in new_lits {
            let var = lit.variable();
            let var_id = var.id();

            let Some(&comp_idx) = self.var_to_component.get(&var_id) else {
                continue;
            };

            let level = ctx.var_level(var).unwrap_or(current_level);
            self.trail.push(AssignmentRecord { var: var_id, level });

            let value = lit.is_positive();
            let result = self.components[comp_idx].solver.assign(var_id, value);
            if self.record_gauss_result(result, comp_idx, ctx) {
                return;
            }
        }

        self.last_trail_pos = ctx.trail().len();
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }
}

include!("extension/proof.rs");

impl Extension for XorExtension {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        #[cfg(debug_assertions)]
        self.debug_propagate_calls
            .set(self.debug_propagate_calls.get() + 1);

        self.sync_with_context(ctx);

        // Conflicts take priority over unit propagations.
        if let Some((conflict, row_idx)) = self.conflict.take() {
            self.needs_propagate = self.needs_resync || !self.pending_propagations.is_empty();
            // Chunked proof mode: emit the conflict row's derivation cone as
            // proof-only chain scaffolding (empty and non-empty conflicts
            // alike — the conflict clause is RUP through the row's chain).
            if self.chunked.is_some() {
                let script = row_idx
                    .and_then(|global| self.global_row_to_target(global))
                    .map(|target| self.drain_chunked_targets(&[target]))
                    .unwrap_or_default();
                let mut result = ExtPropagateResult::conflict(conflict);
                result.proof_script = script;
                return result;
            }
            // When the conflict is empty (0=1 row with no assigned variables),
            // generate intermediate proof clauses from the RREF rows (#4533).
            // These clauses are CNF encodings of derived XOR constraints that
            // are RUP-derivable from the original XOR-encoding clauses. Without
            // them, external DRAT checkers cannot verify the empty clause.
            if conflict.is_empty() {
                if !self.proof_ladders_complete {
                    return ExtPropagateResult::conflict(conflict);
                }
                let mut proof_clauses = Vec::new();
                for comp in &self.components {
                    let Some(clauses) = comp.solver.try_generate_complete_proof_clauses() else {
                        // The certified DIMACS route preflights this condition.
                        // Other direct extension users retain semantic solving,
                        // while their external checker rejects the deliberately
                        // incomplete proof instead of accepting an unsound one.
                        return ExtPropagateResult::conflict(conflict);
                    };
                    proof_clauses.extend(clauses);
                }
                return ExtPropagateResult::new(proof_clauses, vec![], Some(conflict), false);
            }
            // Task #20: the non-empty conflict clause is the CNF image of a
            // DERIVED row under the current assignment — emit the pending row
            // encodings first or the clause is not RUP and an external
            // checker rejects the whole certificate.
            let proof_clauses = self.drain_new_proof_clauses().unwrap_or_default();
            return ExtPropagateResult::new(proof_clauses, vec![], Some(conflict), false);
        }

        if !self.pending_propagations.is_empty() {
            let mut propagations = Vec::new();
            let mut reason_targets: Vec<(usize, usize)> = Vec::new();
            let mut malformed_reason = false;
            let pending = std::mem::take(&mut self.pending_propagations);

            for prop in pending {
                if ctx.value(prop.lit.variable()).is_some() {
                    continue;
                }

                if let Some(clause) = self.build_propagation_clause_from_row(
                    prop.lit,
                    prop.component,
                    prop.source_row,
                ) {
                    propagations.push((clause, prop.lit));
                    reason_targets.push((prop.component, prop.source_row));
                } else {
                    malformed_reason = true;
                    debug_assert!(
                        false,
                        "pending XOR propagation for component {} row {} was not unit under current assignments",
                        prop.component, prop.source_row
                    );
                }
            }

            self.needs_resync = malformed_reason;
            self.needs_propagate = malformed_reason;
            if !propagations.is_empty() {
                // Task #20: reason clauses also come from derived rows — same
                // RUP requirement as the non-empty conflict path.
                if self.chunked.is_some() {
                    let script = self.drain_chunked_targets(&reason_targets);
                    let mut result = ExtPropagateResult::new(vec![], propagations, None, false);
                    result.proof_script = script;
                    return result;
                }
                let proof_clauses = self.drain_new_proof_clauses().unwrap_or_default();
                return ExtPropagateResult::new(proof_clauses, propagations, None, false);
            }
        }

        self.needs_propagate = self.needs_resync;
        ExtPropagateResult::none()
    }

    fn asserted(&mut self, _lit: Literal) {
        // We handle assignments in propagate() via new_assignments()
        // Mark that we need to check for propagations
        self.needs_propagate = true;
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.sync_with_context(ctx);

        if let Some((conflict, _row_idx)) = &self.conflict {
            return ExtCheckResult::Conflict(conflict.clone());
        }

        // Final soundness check: verify the original XOR constraints directly
        // against the SAT solver's model.
        for constraint in &self.constraints {
            let mut parity = false;
            for &var in &constraint.vars {
                let value = ctx.value(Variable::new(var)).unwrap_or(false);
                parity ^= value;
            }
            if parity != constraint.rhs {
                // Constraint violated - build conflict clause
                let conflict: Vec<Literal> = constraint
                    .vars
                    .iter()
                    .map(|&var| {
                        let value = ctx.value(Variable::new(var)).unwrap_or(false);
                        if value {
                            Literal::negative(Variable::new(var))
                        } else {
                            Literal::positive(Variable::new(var))
                        }
                    })
                    .collect();
                return ExtCheckResult::Conflict(conflict);
            }
        }

        ExtCheckResult::Sat
    }

    fn backtrack(&mut self, new_level: u32) {
        #[cfg(debug_assertions)]
        self.debug_backtrack_calls
            .set(self.debug_backtrack_calls.get() + 1);

        // Track which components had variables unassigned and which columns
        // were freed, so we can use targeted watch-based propagation lookup
        // instead of scanning all rows.
        let mut affected_columns: Vec<Vec<usize>> = vec![Vec::new(); self.components.len()];
        let mut affected_components = Vec::new();

        // Scan the entire trail and unassign ALL entries with level > new_level.
        // We cannot use stack-style popping from the end because chronological
        // backtracking causes out-of-order levels on the trail: a variable at
        // level 3 can appear AFTER a variable at level 7 if it was propagated
        // after a chrono-BT compaction. Stack popping would stop at the first
        // low-level entry, leaving high-level entries assigned in the Gaussian
        // solver (#8078).
        self.trail.retain(|rec| {
            if rec.level > new_level {
                if let Some(&comp_idx) = self.var_to_component.get(&rec.var) {
                    if let Some(col) = self.components[comp_idx].solver.get_column(rec.var) {
                        affected_columns[comp_idx].push(col);
                    }
                    self.components[comp_idx].solver.unassign(rec.var);
                    if !affected_components.contains(&comp_idx) {
                        affected_components.push(comp_idx);
                    }
                }
                false // remove from trail
            } else {
                true // keep on trail
            }
        });

        self.pending_propagations.clear();
        self.conflict = None;

        // Reset satisfied_rows only on affected components.
        // Unaffected components retain their satisfied_rows state since
        // their assignment state did not change.
        for &comp_idx in &affected_components {
            self.components[comp_idx].solver.reset_satisfied();
        }

        // Re-collect propagations using targeted watch-based lookup for
        // affected components, and full scan for non-affected ones.
        //
        // Affected components: use `get_propagations_for_columns()` which is
        // O(k * avg_watchers) where k = freed columns -- much faster than
        // O(n * m) full scan.
        //
        // Non-affected components: use `get_all_propagations()` to recover
        // any outstanding unit propagations that were previously consumed
        // by `propagate()` but whose literals were unassigned by the SAT
        // solver during backtrack (e.g., propagated literal was at a higher
        // decision level than the backtrack target).
        for (comp_idx, comp) in self.components.iter().enumerate() {
            if affected_components.contains(&comp_idx) {
                let cols = &affected_columns[comp_idx];
                let (props, conflict_row) = comp.solver.get_propagations_for_columns(cols);
                for (lit, local_row) in props {
                    self.pending_propagations.push(PendingPropagation {
                        lit,
                        source_row: local_row,
                        component: comp_idx,
                    });
                }
                if self.conflict.is_none() {
                    if let Some(local_row) = conflict_row {
                        let clause = self.build_conflict_clause_from_row(comp_idx, local_row);
                        let global_row = comp.row_offset + local_row;
                        self.conflict = Some((clause, Some(global_row)));
                    }
                }
            } else {
                // Non-affected component: no variables were unassigned, but
                // pending_propagations was cleared. Re-discover any unit rows.
                for (lit, local_row) in comp.solver.get_all_propagations() {
                    self.pending_propagations.push(PendingPropagation {
                        lit,
                        source_row: local_row,
                        component: comp_idx,
                    });
                }
                if self.conflict.is_none() {
                    if let Some(local_row) = comp.solver.find_conflict_row() {
                        let clause = self.build_conflict_clause_from_row(comp_idx, local_row);
                        let global_row = comp.row_offset + local_row;
                        self.conflict = Some((clause, Some(global_row)));
                    }
                }
            }
        }

        // Signal that backtrack already handled state cleanup.
        // sync_with_context() will skip the expensive rebuild_from_context()
        // and just update last_trail_pos from the SAT context.
        self.backtrack_handled = true;
        self.needs_resync = false;
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }

    fn init(&mut self) {
        for comp in &mut self.components {
            comp.solver.clear_assignments();
        }
        self.trail.clear();
        self.last_trail_pos = 0;

        // Get initial propagations from all components
        self.pending_propagations.clear();
        for (comp_idx, comp) in self.components.iter().enumerate() {
            for (lit, local_row) in comp.solver.get_all_propagations() {
                self.pending_propagations.push(PendingPropagation {
                    lit,
                    source_row: local_row,
                    component: comp_idx,
                });
            }
        }

        // Check for initial conflict across all components
        self.conflict = None;
        for (comp_idx, comp) in self.components.iter().enumerate() {
            if let Some(local_row) = comp.solver.find_conflict_row() {
                let clause = self.build_conflict_clause_from_row(comp_idx, local_row);
                let global_row = comp.row_offset + local_row;
                self.conflict = Some((clause, Some(global_row)));
                break;
            }
        }

        self.needs_resync = false;
        self.backtrack_handled = false;
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }

    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        self.backtrack_handled
            || self.needs_resync
            || self.needs_propagate
            || ctx.trail().len() != self.last_trail_pos
    }
}
