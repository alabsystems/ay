// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Gauss-Jordan elimination solver for XOR constraints.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_sat::{Literal, Variable};

use crate::constraint::XorConstraint;
use crate::packed_row::{PackedRow, RowState};
use crate::VarId;

/// Maximum number of variables in an RREF row for which the proof-clause
/// helper emits the `2^(k-1)`-clause truth-table CNF encoding
/// (`encode_xor_row_to_cnf`).
///
/// Two reasons for the cap:
/// 1. **Correctness:** the encoding computes `1usize << k`, which is undefined
///    for `k >= usize::BITS` (= 64) — a debug-build panic and a release-build
///    shift-amount mask that silently emits a *wrong* clause set into the DRAT
///    certificate. Gaussian elimination densifies rows, and the matrix may have
///    up to `MAX_MATRIX_COLUMNS` (1000) columns, so a row with `k >= 64` set
///    bits is reachable in production (#4533 conflict path).
/// 2. **Memory:** `2^(k-1)` clauses blow up exponentially; beyond this cap the
///    truth-table encoding is infeasible regardless of the shift bug.
///
/// Rows wider than this simply SKIP helper-clause emission. This is sound: the
/// helper clauses only *assist* an external DRAT checker in deriving the empty
/// clause; omitting them can make that proof unverifiable (the checker fails
/// CLOSED — it rejects, it does not accept a wrong proof) but never unsound.
/// A future enhancement could emit a compact Tseitin/parity-chain encoding with
/// fresh auxiliary variables for wide rows instead of skipping.
const MAX_XOR_PROOF_ROW_VARS: usize = 24;

/// Result of a Gaussian elimination step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GaussResult {
    /// No propagation or conflict.
    Nothing,
    /// A variable can be propagated (unit constraint found).
    /// Contains the propagated literal and the source RREF row index.
    Propagate(Literal, usize),
    /// Multiple variables can be propagated (multiple unit constraints found).
    /// Contains all propagated literals with their source RREF row indices.
    /// This is more efficient than returning one at a time.
    MultiPropagate(Vec<(Literal, usize)>),
    /// A conflict was detected (0 = 1).
    /// Contains the source RREF row index.
    Conflict(usize),
}

/// Gauss-Jordan elimination solver for XOR constraints.
///
/// Maintains a matrix in reduced row echelon form and supports incremental
/// updates when variables are assigned.
///
/// # Lazy Backtracking (O(1))
///
/// The RREF matrix is immutable after `eliminate()`. Assignments are tracked
/// separately in packed bit vectors (`assigned_true_cols`, `unassigned_cols`).
/// On backtrack, only the assignment state is rolled back -- no matrix copy
/// is needed. This gives O(k) backtrack cost where k is the number of
/// unassigned variables, compared to the previous O(n*m) row-copy approach.
///
/// This mirrors CryptoMiniSat's `canceling()` flag-based backtrack
/// (`reference/cryptominisat/src/gaussian.h:208-213`).
#[derive(Debug)]
pub struct GaussianSolver {
    /// RREF matrix rows -- immutable after `eliminate()`.
    ///
    /// Assignments are evaluated against these rows without modifying them.
    /// There is no separate "working copy"; the RREF structure encodes fixed
    /// relationships between variables that do not change during search.
    pub(crate) rows: Vec<PackedRow>,
    /// Variable to column mapping.
    pub(crate) var_to_col: HashMap<VarId, usize>,
    /// Column to variable mapping.
    col_to_var: Vec<VarId>,
    /// Which row is responsible for each column (pivot row).
    /// None means no row has this column as pivot.
    col_to_pivot_row: Vec<Option<usize>>,
    /// Number of variables/columns.
    num_cols: usize,
    /// Current variable assignments (None = unassigned).
    pub(crate) assignments: Vec<Option<bool>>,
    /// Packed columns assigned to true.
    assigned_true_cols: PackedRow,
    /// Packed columns that are currently unassigned.
    unassigned_cols: PackedRow,
    /// Watched constraints: for each column, list of rows watching it.
    /// A row watches columns with non-zero coefficients where we expect propagations.
    watches: Vec<Vec<usize>>,
    /// For each row: indices of the two watched columns [watch0, watch1].
    /// None means no watch (row may be all-zero or satisfied).
    row_watches: Vec<[Option<usize>; 2]>,
    /// Rows that are currently satisfied (all variables assigned, parity matches).
    satisfied_rows: Vec<bool>,
    /// Intermediate derived rows from Gauss-Jordan elimination, recorded for
    /// DRAT proof generation (#4533). Each entry is a snapshot of a row after
    /// an XOR operation during elimination. These rows are linear combinations
    /// of the original constraints, and their CNF encodings are RUP-derivable
    /// from the original XOR-encoding clauses.
    elimination_trace: Vec<PackedRow>,
}

impl GaussianSolver {
    /// Create a new solver with the given XOR constraints.
    pub fn new(constraints: &[XorConstraint]) -> Self {
        // Collect all variables
        let mut all_vars: Vec<VarId> = constraints
            .iter()
            .flat_map(|c| c.vars.iter().copied())
            .collect();
        all_vars.sort_unstable();
        all_vars.dedup();

        let num_cols = all_vars.len();
        let num_rows = constraints.len();

        // Build mappings
        let var_to_col: HashMap<VarId, usize> = all_vars
            .iter()
            .enumerate()
            .map(|(col, &var)| (var, col))
            .collect();
        let col_to_var = all_vars;

        // Build matrix rows
        let rows: Vec<PackedRow> = constraints
            .iter()
            .map(|c| PackedRow::from_xor(c, &var_to_col, num_cols))
            .collect();
        let assigned_true_cols = PackedRow::new(num_cols);
        let mut unassigned_cols = PackedRow::new(num_cols);
        unassigned_cols.fill_ones();

        Self {
            rows,
            var_to_col,
            col_to_var,
            col_to_pivot_row: vec![None; num_cols],
            num_cols,
            assignments: vec![None; num_cols],
            assigned_true_cols,
            unassigned_cols,
            // Watch structures initialized empty, filled by init_watches() after eliminate()
            watches: vec![Vec::new(); num_cols],
            row_watches: vec![[None, None]; num_rows],
            satisfied_rows: vec![false; num_rows],
            elimination_trace: Vec::new(),
        }
    }

    /// Perform full Gauss-Jordan elimination.
    ///
    /// After this, the matrix is in reduced row echelon form and is treated
    /// as immutable for the lifetime of the solver. All subsequent operations
    /// evaluate rows against the assignment state without modifying them.
    ///
    /// Returns `GaussResult::Conflict` if a conflict is found.
    pub fn eliminate(&mut self) -> GaussResult {
        let num_rows = self.rows.len();
        let mut pivot_row_idx = 0;
        self.elimination_trace.clear();

        for col in 0..self.num_cols {
            // Find pivot: first row with "1" in this column (at or below pivot_row_idx)
            let mut found_pivot = None;
            for row_idx in pivot_row_idx..num_rows {
                if self.rows[row_idx].get(col) {
                    found_pivot = Some(row_idx);
                    break;
                }
            }

            if let Some(pivot_idx) = found_pivot {
                // Swap pivot row to current position
                if pivot_idx != pivot_row_idx {
                    self.rows.swap(pivot_idx, pivot_row_idx);
                }

                // Record that this column has a pivot
                self.col_to_pivot_row[col] = Some(pivot_row_idx);

                // XOR pivot into ALL other rows with "1" in this column
                // This is Gauss-Jordan (eliminates above AND below)
                for row_idx in 0..num_rows {
                    if row_idx != pivot_row_idx && self.rows[row_idx].get(col) {
                        // Need to clone to satisfy borrow checker
                        let pivot_row = self.rows[pivot_row_idx].clone();
                        self.rows[row_idx].xor_in(&pivot_row);
                        // Record the intermediate derived row for DRAT proof
                        // generation (#4533). Each derived row is the XOR of two
                        // existing rows and its CNF is RUP from the parent rows.
                        self.elimination_trace.push(self.rows[row_idx].clone());
                    }
                }

                pivot_row_idx += 1;
            }
        }

        // After elimination, `self.rows` is the immutable RREF matrix.
        // No separate copy is needed -- backtracking only resets assignments.

        // Initialize watched constraints for efficient propagation
        self.init_watches();

        // Check for conflicts (all-zero row with non-zero RHS)
        for (row_idx, row) in self.rows.iter().enumerate() {
            if row.is_zero() && row.rhs {
                return GaussResult::Conflict(row_idx);
            }
        }

        GaussResult::Nothing
    }

    /// Evaluate a row against the current packed assignment state.
    #[inline]
    fn evaluate_row(&self, row: &PackedRow) -> RowState {
        row.evaluate_with_column_state(&self.assigned_true_cols, &self.unassigned_cols)
    }

    /// Update the packed column state for a single assignment change.
    #[inline]
    fn set_assignment_state(&mut self, col: usize, value: Option<bool>) {
        self.unassigned_cols.set(col, value.is_none());
        self.assigned_true_cols.set(col, value == Some(true));
    }

    /// Initialize watched constraints after elimination.
    ///
    /// Each non-trivial row watches exactly 2 columns (variables). When a watched
    /// variable is assigned, we check if the row becomes unit or conflict. This
    /// gives O(watching_rows * num_cols) worst-case per assignment instead of
    /// O(n*m) per assignment. Amortized cost depends on watch movement frequency.
    fn init_watches(&mut self) {
        // Clear any existing watches
        for watches in &mut self.watches {
            watches.clear();
        }
        for row_watch in &mut self.row_watches {
            *row_watch = [None, None];
        }
        for sat in &mut self.satisfied_rows {
            *sat = false;
        }

        // For each row, find first 2 non-zero columns and watch them
        for (row_idx, row) in self.rows.iter().enumerate() {
            let mut watch_count = 0;
            for col in 0..self.num_cols {
                if row.get(col) {
                    // This column has a 1 in this row - watch it
                    self.watches[col].push(row_idx);
                    self.row_watches[row_idx][watch_count] = Some(col);
                    watch_count += 1;
                    if watch_count == 2 {
                        break;
                    }
                }
            }
        }
    }

    /// Assign a variable and propagate using watched constraints.
    ///
    /// Returns propagation or conflict information. Uses watched constraints
    /// to avoid scanning all rows. Per-assignment cost is O(watching_rows * num_cols)
    /// worst-case when watches need replacement; O(watching_rows) when they don't.
    pub fn assign(&mut self, var: VarId, value: bool) -> GaussResult {
        let Some(&col) = self.var_to_col.get(&var) else {
            return GaussResult::Nothing; // Variable not in any XOR
        };

        if self.assignments[col] == Some(value) {
            return GaussResult::Nothing;
        }
        debug_assert!(
            self.assignments[col].is_none(),
            "reassigning XOR variable {} from {:?} to {}",
            var,
            self.assignments[col],
            value,
        );
        self.assignments[col] = Some(value);
        self.set_assignment_state(col, Some(value));

        // Use watched propagation for efficiency
        self.propagate_watched(col)
    }

    /// Propagate using watched constraints.
    ///
    /// When a watched variable is assigned, we examine only the rows watching
    /// that variable. For each row:
    /// - If satisfied, skip
    /// - If conflict (0 unassigned, parity mismatch), return conflict
    /// - If unit (1 unassigned), collect propagation (continue to find more)
    /// - If 2+ unassigned, try to find a new watch
    ///
    /// Returns all propagations found in a single pass. This is more efficient
    /// than returning one at a time because it reduces solver round-trips.
    fn propagate_watched(&mut self, assigned_col: usize) -> GaussResult {
        // Take the watch list for this column (we'll rebuild it)
        let watching_rows = std::mem::take(&mut self.watches[assigned_col]);

        // Collect updates to apply after the immutable borrow phase
        struct WatchUpdate {
            row_idx: usize,
            new_col: usize,
            watch_slot: usize,
        }
        let mut keep_watching: Vec<usize> = Vec::with_capacity(watching_rows.len());
        let mut watch_updates: Vec<WatchUpdate> = Vec::new();
        let mut satisfied_updates: Vec<usize> = Vec::new();
        let mut propagations: Vec<(Literal, usize)> = Vec::new();
        let mut conflict_row: Option<usize> = None;

        // Immutable borrow phase: examine rows and collect updates
        {
            let rows = &self.rows;

            for row_idx in watching_rows {
                // Skip satisfied rows
                if self.satisfied_rows[row_idx] {
                    keep_watching.push(row_idx);
                    continue;
                }

                let row = &rows[row_idx];

                // Evaluate the row under current assignments
                match self.evaluate_row(row) {
                    RowState::Conflict => {
                        // Conflict - put back watch and stop processing
                        keep_watching.push(row_idx);
                        conflict_row = Some(row_idx);
                        break;
                    }
                    RowState::Satisfied => {
                        // Row satisfied - mark it and keep watching
                        satisfied_updates.push(row_idx);
                        keep_watching.push(row_idx);
                    }
                    RowState::Unit(unit_col, val) => {
                        // Unit propagation - keep watching and collect
                        // Continue processing to find all propagations
                        keep_watching.push(row_idx);
                        let var = Variable::new(self.col_to_var[unit_col]);
                        let lit = if val {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        };
                        propagations.push((lit, row_idx));
                    }
                    RowState::Unknown => {
                        // 2+ unassigned - try to find a new watch
                        let row_watch = self.row_watches[row_idx];
                        let watch_slot = usize::from(row_watch[0] != Some(assigned_col));

                        // Find a new unassigned column to watch
                        let mut found_new = false;
                        for new_col in 0..self.num_cols {
                            // Must be: in this row, unassigned, and not already watched
                            if row.get(new_col)
                                && self.assignments[new_col].is_none()
                                && row_watch[0] != Some(new_col)
                                && row_watch[1] != Some(new_col)
                            {
                                // Found a new watch
                                watch_updates.push(WatchUpdate {
                                    row_idx,
                                    new_col,
                                    watch_slot,
                                });
                                found_new = true;
                                break;
                            }
                        }

                        if !found_new {
                            // No new watch found - keep watching assigned column
                            keep_watching.push(row_idx);
                        }
                    }
                }
            }
        }

        // Mutable phase: apply all updates
        self.watches[assigned_col] = keep_watching;

        for row_idx in satisfied_updates {
            self.satisfied_rows[row_idx] = true;
        }

        for update in watch_updates {
            // Update row_watches
            self.row_watches[update.row_idx][update.watch_slot] = Some(update.new_col);
            // Add to new column's watch list
            self.watches[update.new_col].push(update.row_idx);
        }

        // Return result in priority order: conflict > propagations > nothing
        if let Some(row_idx) = conflict_row {
            GaussResult::Conflict(row_idx)
        } else if propagations.is_empty() {
            GaussResult::Nothing
        } else if propagations.len() == 1 {
            let (lit, row_idx) = propagations[0];
            GaussResult::Propagate(lit, row_idx)
        } else {
            GaussResult::MultiPropagate(propagations)
        }
    }

    /// Get all current unit propagations with their source row indices.
    pub fn get_all_propagations(&self) -> Vec<(Literal, usize)> {
        let mut props = Vec::new();

        for (row_idx, row) in self.rows.iter().enumerate() {
            if let RowState::Unit(col, val) = self.evaluate_row(row) {
                let var = Variable::new(self.col_to_var[col]);
                let lit = if val {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                };
                props.push((lit, row_idx));
            }
        }
        props
    }

    /// Backtrack: unassign a variable.
    pub fn unassign(&mut self, var: VarId) {
        if let Some(&col) = self.var_to_col.get(&var) {
            self.assignments[col] = None;
            self.set_assignment_state(col, None);
        }
    }

    /// Find the first conflicting row, if any.
    ///
    /// Returns the row index of the first row that evaluates to Conflict.
    /// Used to build minimal conflict clauses from the specific row.
    pub fn find_conflict_row(&self) -> Option<usize> {
        self.rows
            .iter()
            .position(|row| matches!(self.evaluate_row(row), RowState::Conflict))
    }

    /// Get propagations for rows watching specific columns.
    ///
    /// This is O(k * avg_watchers) where k = number of columns, much faster than
    /// get_all_propagations() which is O(n * m) for n rows and m columns.
    ///
    /// Returns (propagations, conflict_row) tuple where conflict_row is the index
    /// of the first conflicting row found, if any.
    pub fn get_propagations_for_columns(
        &self,
        columns: &[usize],
    ) -> (Vec<(Literal, usize)>, Option<usize>) {
        let mut props = Vec::new();
        let mut conflict_row = None;
        let mut checked_rows = vec![false; self.rows.len()];
        let rows = &self.rows;

        for &col in columns {
            if col >= self.watches.len() {
                continue;
            }
            for &row_idx in &self.watches[col] {
                if row_idx >= rows.len() || checked_rows[row_idx] {
                    continue;
                }
                checked_rows[row_idx] = true;

                match self.evaluate_row(&rows[row_idx]) {
                    RowState::Unit(unit_col, val) => {
                        let var = Variable::new(self.col_to_var[unit_col]);
                        let lit = if val {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        };
                        props.push((lit, row_idx));
                    }
                    RowState::Conflict if conflict_row.is_none() => {
                        conflict_row = Some(row_idx);
                    }
                    _ => {}
                }
            }
        }
        (props, conflict_row)
    }

    /// Get the column index for a variable, if it exists.
    #[inline]
    pub fn get_column(&self, var: VarId) -> Option<usize> {
        self.var_to_col.get(&var).copied()
    }

    /// Check if a variable is tracked by this solver.
    #[inline]
    pub fn has_variable(&self, var: VarId) -> bool {
        self.var_to_col.contains_key(&var)
    }

    /// Get the current assignment for a column.
    #[inline]
    pub fn assignment_at(&self, col: usize) -> Option<bool> {
        self.assignments.get(col).copied().flatten()
    }

    /// Get the number of XOR constraints.
    pub fn num_constraints(&self) -> usize {
        self.rows.len()
    }

    /// Get the number of variables.
    pub fn num_variables(&self) -> usize {
        self.num_cols
    }

    /// Clear all variable assignments and reset satisfied row tracking.
    pub fn clear_assignments(&mut self) {
        self.assignments.fill(None);
        self.assigned_true_cols.clear_all();
        self.unassigned_cols.fill_ones();
        self.init_watches();
    }

    /// Reset satisfied_rows for backtracking.
    ///
    /// Called during incremental backtracking. Watches remain valid
    /// for surviving assignments.
    pub fn reset_satisfied(&mut self) {
        self.satisfied_rows.fill(false);
    }

    /// Get the variables in a specific RREF row.
    ///
    /// Used to build minimal reason clauses for propagations. Only variables
    /// that are set in the RREF row are included, which is typically much smaller
    /// than the entire trail.
    ///
    /// Returns a vector of (variable_id, column_index) pairs for variables
    /// in the specified row. Uses efficient bit iteration (O(popcount) not O(num_cols)).
    pub fn get_row_variables(&self, row_idx: usize) -> Vec<(VarId, usize)> {
        let row = &self.rows[row_idx];

        // Use efficient set bits iterator - O(popcount) instead of O(num_cols)
        row.iter_set_bits()
            .map(|col| (self.col_to_var[col], col))
            .collect()
    }

    // NOTE: `restore_rref()` has been removed. The RREF matrix is immutable
    // after `eliminate()` and never needs restoration. Backtracking is handled
    // by `unassign()` (per variable, O(1)) or `clear_assignments()` (all, O(n)).
    // This is the lazy backtrack optimization from issue #8167, porting CMS's
    // `canceling()` pattern.

    /// Generate intermediate proof clauses for DRAT verification (#4533).
    ///
    /// During Gauss-Jordan elimination, each XOR operation on two rows produces
    /// a derived row whose CNF encoding is RUP-derivable from the CNF of its
    /// parent rows. This method returns the CNF encodings of all intermediate
    /// derived rows recorded during `eliminate()`, in elimination order.
    ///
    /// After emitting the intermediate row CNF, this method also emits a unit
    /// clause for one variable in the system. This unit clause is RUP from the
    /// combination of original clauses and intermediate clauses (because the
    /// system is contradictory, both polarities of any variable are implied).
    /// The unit clause enables the DRAT checker to derive the empty clause
    /// via unit propagation.
    ///
    /// For a 2-variable row `xi XOR xj = rhs`, the CNF encoding is:
    ///   rhs=0: {xi, -xj}, {-xi, xj}  (equivalence)
    ///   rhs=1: {xi, xj}, {-xi, -xj}  (XOR)
    pub fn generate_proof_clauses(&self) -> Vec<Vec<Literal>> {
        let mut proof_clauses = Vec::new();

        for row in &self.elimination_trace {
            if row.is_zero() {
                // Zero row with rhs=true means 0=1 conflict. We cannot encode
                // this as CNF (no variables), but the empty clause will be
                // emitted separately by the solver.
                continue;
            }
            Self::encode_xor_row_to_cnf(row, &self.col_to_var, &mut proof_clauses);
        }

        // After adding intermediate CNF, the empty clause is not directly
        // RUP-derivable because the clause set has no unit clauses to start
        // unit propagation. We emit a unit clause for one variable to bridge
        // the gap. This unit clause IS RUP because:
        //   1. The system is contradictory (0=1 row exists)
        //   2. Negating the unit literal forces unit propagation that reaches
        //      contradiction through the intermediate + original clauses
        //
        // After the unit clause, the empty clause becomes RUP because the
        // unit literal propagates through the clause set to contradiction.
        if !proof_clauses.is_empty() {
            // Pick the first variable from any non-zero RREF row.
            if let Some(first_var) = self.col_to_var.first().copied() {
                let var = Variable::new(first_var);
                proof_clauses.push(vec![Literal::positive(var)]);
            }
        }

        proof_clauses
    }

    /// Encode a single XOR row as CNF clauses, appending to `out`.
    ///
    /// For k variables, generates 2^(k-1) clauses that forbid all assignments
    /// violating the XOR parity constraint.
    fn encode_xor_row_to_cnf(row: &PackedRow, col_to_var: &[VarId], out: &mut Vec<Vec<Literal>>) {
        let vars: Vec<(VarId, usize)> = row
            .iter_set_bits()
            .map(|col| (col_to_var[col], col))
            .collect();
        let k = vars.len();

        if k == 0 {
            return;
        }

        if k == 1 {
            // Unit XOR: xi = rhs -> unit clause {xi} or {-xi}
            let var = Variable::new(vars[0].0);
            let lit = if row.rhs {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            out.push(vec![lit]);
            return;
        }

        if k == 2 {
            // Binary XOR: xi XOR xj = rhs
            let var0 = Variable::new(vars[0].0);
            let var1 = Variable::new(vars[1].0);
            if row.rhs {
                // xi XOR xj = 1: {xi, xj}, {-xi, -xj}
                out.push(vec![Literal::positive(var0), Literal::positive(var1)]);
                out.push(vec![Literal::negative(var0), Literal::negative(var1)]);
            } else {
                // xi XOR xj = 0: {xi, -xj}, {-xi, xj}
                out.push(vec![Literal::positive(var0), Literal::negative(var1)]);
                out.push(vec![Literal::negative(var0), Literal::positive(var1)]);
            }
            return;
        }

        // k-variable XOR (k >= 3): generate 2^(k-1) clauses.
        //
        // Guard `1usize << k` against shift overflow (UB for k >= 64: debug
        // panic, release shift-amount mask -> wrong certificate clauses) and the
        // `2^(k-1)` memory blow-up. Wide rows skip helper emission, which is
        // sound (the external DRAT checker fails closed). See
        // `MAX_XOR_PROOF_ROW_VARS`.
        if k > MAX_XOR_PROOF_ROW_VARS {
            return;
        }
        let total = 1usize << k;
        for mask in 0..total {
            // Each mask represents an assignment. If the parity of set bits
            // does NOT match rhs, it's a forbidden assignment -> generate clause.
            let ones = mask.count_ones();
            let parity_matches = (ones % 2 == 1) == row.rhs;
            if parity_matches {
                // This assignment satisfies the XOR -- skip it.
                continue;
            }
            // Generate a clause that blocks this forbidden assignment.
            let clause: Vec<Literal> = vars
                .iter()
                .enumerate()
                .map(|(i, &(var_id, _))| {
                    let var = Variable::new(var_id);
                    if (mask >> i) & 1 == 1 {
                        Literal::negative(var)
                    } else {
                        Literal::positive(var)
                    }
                })
                .collect();
            out.push(clause);
        }
    }
}

#[cfg(test)]
mod proof_clause_encoding_tests {
    use super::*;
    use crate::packed_row::PackedRow;

    /// `col_to_var[col] = col + 1` (1-indexed VarIds, length `n`).
    fn col_to_var(n: usize) -> Vec<VarId> {
        (1..=n as VarId).collect()
    }

    fn row_with_first_k_set(n: usize, k: usize) -> PackedRow {
        let mut row = PackedRow::new(n);
        for col in 0..k {
            row.set(col, true);
        }
        row.rhs = true;
        row
    }

    /// Small rows are unaffected by the cap: a `k = 3` XOR row still emits
    /// exactly `2^(k-1) = 4` clauses, each with `k = 3` literals.
    #[test]
    fn test_small_row_encoding_unchanged() {
        let n = 8;
        let row = row_with_first_k_set(n, 3);
        let mut out = Vec::new();
        GaussianSolver::encode_xor_row_to_cnf(&row, &col_to_var(n), &mut out);
        assert_eq!(out.len(), 4, "k=3 must still emit 2^(k-1)=4 clauses");
        assert!(
            out.iter().all(|c| c.len() == 3),
            "each clause has k=3 literals"
        );
    }

    /// A moderate `k = 10` row still emits the full `2^9 = 512` clauses — the
    /// general encoding path is preserved below the cap.
    #[test]
    fn test_moderate_row_encoding_unchanged() {
        let n = 16;
        let row = row_with_first_k_set(n, 10);
        let mut out = Vec::new();
        GaussianSolver::encode_xor_row_to_cnf(&row, &col_to_var(n), &mut out);
        assert_eq!(out.len(), 1 << 9, "k=10 must emit 2^(k-1)=512 clauses");
    }

    /// Regression for the `1usize << k` shift-overflow (#4533): a `k = 70` row
    /// (k >= usize::BITS = 64) must NOT panic and must skip helper emission
    /// rather than mask the shift and emit a wrong certificate clause set.
    #[test]
    fn test_wide_row_skips_without_shift_overflow() {
        let n = 80;
        let row = row_with_first_k_set(n, 70);
        let mut out = Vec::new();
        // Before the fix this either panicked (debug) or emitted bogus clauses
        // from `1usize << (70 % 64) = 1usize << 6` (release).
        GaussianSolver::encode_xor_row_to_cnf(&row, &col_to_var(n), &mut out);
        assert!(
            out.is_empty(),
            "wide row (k=70) must skip helper emission, got {} clauses",
            out.len()
        );
    }

    /// The cap boundary: `k = MAX_XOR_PROOF_ROW_VARS + 1` skips emission.
    #[test]
    fn test_just_over_cap_skips() {
        let n = MAX_XOR_PROOF_ROW_VARS + 4;
        let row = row_with_first_k_set(n, MAX_XOR_PROOF_ROW_VARS + 1);
        let mut out = Vec::new();
        GaussianSolver::encode_xor_row_to_cnf(&row, &col_to_var(n), &mut out);
        assert!(out.is_empty(), "k = cap+1 must skip helper emission");
    }
}
