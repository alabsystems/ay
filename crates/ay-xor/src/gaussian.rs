// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Gauss-Jordan elimination solver for XOR constraints.

pub(crate) mod chunked_proof;

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

/// Total helper clauses the XOR proof encoder may emit across ALL rows of one
/// elimination trace.
///
/// `encode_xor_row_to_cnf` emits `2^(k-1)` clauses for a width-`k` row, so the
/// per-row cap alone bounds nothing useful once Gaussian fill-in produces many
/// wide rows: at the cap, `k = 24` is 8.4 M clauses — roughly 1 GB of
/// `Vec<Literal>` — for a SINGLE row, and the trace has one row per pivot.
///
/// Measured on `lightsout_sat_23_unbounded_direct_random50_2_unsat` from the
/// SAT-COMP 2026 Main set — **529 variables, 7744 clauses, a 180 KB file**,
/// detected as one XOR component of 529 constraints: AY reached **71.7 GB**,
/// and 11.3 GB within six seconds against a `--memory 2000` limit that never
/// took effect. 26 of the 31 official solvers solve that instance.
///
/// Skipping emission is sound — it only means fewer helper clauses for the
/// external checker, which fails closed — so the aggregate budget is a pure
/// safety bound. Sized so the whole trace stays around 100 MB of clause data.
pub(crate) const MAX_XOR_PROOF_TOTAL_CLAUSES: usize = 1 << 20;

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

/// One Gauss-Jordan elimination step recorded for DRAT emission (task #20).
///
/// `result = parent_a ^ parent_b`. The parents are SNAPSHOTS taken at the
/// moment of the row operation; the ladder derivation in
/// `emit_trace_step_ladder` needs them because a derived row's CNF encoding
/// is NOT single-step RUP — the cancelled variables (vars(parent_a) n
/// vars(parent_b)) stay unassigned when one encoding clause is negated, so
/// the checker must be walked down a resolution ladder instead.
#[derive(Debug, Clone)]
struct TraceStep {
    result: PackedRow,
    parent_a: PackedRow,
    parent_b: PackedRow,
    /// Matrix position of the pivot row (`parent_a`) at the moment of the
    /// row operation, AFTER any pivot swap. Together with the recorded swap
    /// events this gives exact row provenance for the chunked proof plan
    /// (which trace step or original constraint produced each parent) with
    /// no content matching.
    pivot_pos: u32,
    /// Matrix position of the target row (`parent_b` before, `result` after).
    target_pos: u32,
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
/// unassigned variables, compared to the previous O(n*m) matrix-copy cost.
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
    elimination_trace: Vec<TraceStep>,
    /// Pivot swaps performed by `eliminate()`, as `(pos_a, pos_b, watermark)`
    /// where `watermark` is `elimination_trace.len()` at swap time. Replayed
    /// by the chunked proof planner to recover exact row provenance.
    elimination_swaps: Vec<(u32, u32, u32)>,
    /// Snapshot of the constraint rows as built by `new()`, captured on the
    /// first `eliminate()` call before any row operation. Original-row widths
    /// and contents feed the chunked proof plan (rotation conversion of an
    /// original row's input CNF encoding into its parity chain).
    initial_rows: Vec<PackedRow>,
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
            elimination_swaps: Vec::new(),
            initial_rows: Vec::new(),
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
        self.elimination_swaps.clear();
        // First call only: `rows` still holds the constraint rows built by
        // `new()`. A repeated `eliminate()` re-runs on the RREF matrix, so
        // overwriting the snapshot then would lose original-row identity.
        if self.initial_rows.is_empty() {
            self.initial_rows = self.rows.clone();
        }

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
                    self.elimination_swaps.push((
                        pivot_idx as u32,
                        pivot_row_idx as u32,
                        self.elimination_trace.len() as u32,
                    ));
                }

                // Record that this column has a pivot
                self.col_to_pivot_row[col] = Some(pivot_row_idx);

                // XOR pivot into ALL other rows with "1" in this column
                // This is Gauss-Jordan (eliminates above AND below)
                for row_idx in 0..num_rows {
                    if row_idx != pivot_row_idx && self.rows[row_idx].get(col) {
                        // Need to clone to satisfy borrow checker
                        let pivot_row = self.rows[pivot_row_idx].clone();
                        let old_target = self.rows[row_idx].clone();
                        self.rows[row_idx].xor_in(&pivot_row);
                        // Record the derived row WITH its parents for DRAT
                        // ladder emission (task #20): enc(result) alone is not
                        // RUP; the ladder over the cancelled pivot column is.
                        self.elimination_trace.push(TraceStep {
                            result: self.rows[row_idx].clone(),
                            parent_a: pivot_row,
                            parent_b: old_target,
                            pivot_pos: pivot_row_idx as u32,
                            target_pos: row_idx as u32,
                        });
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
        self.row_watches.fill([None, None]);
        self.satisfied_rows.fill(false);

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

    /// Emit the DRAT resolution ladder for elimination-trace steps from
    /// `start` onward; returns the clauses and the new trace length for the
    /// caller's latch (task #20).
    ///
    /// A derived row `C = A ^ B` cannot be emitted as a bare CNF encoding:
    /// negating one clause of `enc(C)` leaves the CANCELLED variables
    /// (`vars(A) n vars(B)`) unassigned, so unit propagation through the
    /// parent encodings never closes and every external checker rejects the
    /// addition (measured 2026-08-19: dsr-trim "No UP contradiction for RAT
    /// clause" on BOTH the empty- and non-empty-conflict paths). Instead each
    /// step emits a ladder over its cancelled variables `x1..xm`:
    ///
    ///   level m: for every wrong-parity assignment over `vars(C)` and EVERY
    ///            assignment over `x1..xm`, the blocking clause — each is a
    ///            weakening (superset) of a present `enc(A)`/`enc(B)` clause,
    ///            so negating it falsifies that clause outright (RUP);
    ///   level j-1: resolvents of level-j pairs on `x_j` (RUP against level j);
    ///   level 0: exactly `enc(C)`.
    ///
    /// Parent encodings are always present when a step is emitted: original
    /// rows are encoded in the input CNF itself (the consumed clause groups),
    /// and derived parents were emitted by their own earlier ladder (trace
    /// order). A zero result row with rhs=1 ladders down to the EMPTY clause,
    /// which is why the empty-conflict path needs no bridging-unit hack.
    ///
    /// Returns `None` instead of emitting a partial trace when any remaining
    /// step exceeds the width or aggregate-clause budget. Callers that remove
    /// the original XOR clauses must fall back to ordinary SAT solving on
    /// `None`; silently publishing a predictably rejected certificate is not
    /// a certified proof route.
    pub fn generate_proof_clauses_from(&self, start: usize) -> Option<(Vec<Vec<Literal>>, usize)> {
        let mut proof_clauses = Vec::new();
        for step in self.elimination_trace.iter().skip(start) {
            if !self.emit_trace_step_ladder(step, &mut proof_clauses) {
                return None;
            }
        }
        Some((proof_clauses, self.elimination_trace.len()))
    }

    /// Whether the complete elimination trace fits the certified DRAT ladder
    /// envelope without allocating the clauses.
    pub fn has_complete_proof_ladder(&self) -> bool {
        self.complete_proof_ladder_clause_count().is_some()
    }

    /// Exact aggregate clause count for a complete certified ladder, or
    /// `None` when a width, arithmetic, or aggregate budget is exceeded.
    pub(crate) fn complete_proof_ladder_clause_count(&self) -> Option<usize> {
        let mut total = 0usize;
        for step in &self.elimination_trace {
            let step_clauses = self.proof_ladder_clause_count(step)?;
            let next_total = total.checked_add(step_clauses)?;
            if next_total > MAX_XOR_PROOF_TOTAL_CLAUSES {
                return None;
            }
            total = next_total;
        }
        Some(total)
    }

    /// Try whole-trace ladder emission for a certified proof route.
    pub fn try_generate_complete_proof_clauses(&self) -> Option<Vec<Vec<Literal>>> {
        self.generate_proof_clauses_from(0)
            .map(|(clauses, _)| clauses)
    }

    /// Whole-trace ladder emission (the empty-conflict path).
    ///
    /// This retains the pre-task-#20 public return type for source
    /// compatibility. Certified callers should first use
    /// [`Self::has_complete_proof_ladder`] or call
    /// [`Self::try_generate_complete_proof_clauses`]; an over-budget trace
    /// preserves the historical behavior of returning no helper clauses.
    pub fn generate_proof_clauses(&self) -> Vec<Vec<Literal>> {
        self.try_generate_complete_proof_clauses()
            .unwrap_or_default()
    }

    /// Emit one elimination step's resolution ladder (see
    /// `generate_proof_clauses_from`). Returns false without modifying `out`
    /// when a budget would be exceeded.
    fn emit_trace_step_ladder(&self, step: &TraceStep, out: &mut Vec<Vec<Literal>>) -> bool {
        let Some(ladder_total) = self.proof_ladder_clause_count(step) else {
            return false;
        };
        if out.len().saturating_add(ladder_total) > MAX_XOR_PROOF_TOTAL_CLAUSES {
            return false;
        }

        // Columns of the result and the cancelled columns (in both parents).
        let result_cols: Vec<usize> = (0..self.num_cols).filter(|&c| step.result.get(c)).collect();
        let cancelled_cols: Vec<usize> = (0..self.num_cols)
            .filter(|&c| step.parent_a.get(c) && step.parent_b.get(c))
            .collect();
        let rhs = step.result.rhs;
        if ladder_total == 0 {
            return true;
        }
        // Wrong-parity assignments over the result columns: parity != rhs.
        // Represent an assignment as a bitmask over result_cols indices.
        let n = result_cols.len();
        for level in (0..=cancelled_cols.len()).rev() {
            for assign in 0..(1u64 << n) {
                if ((assign.count_ones() as usize) % 2 == usize::from(rhs)) && n > 0 {
                    continue; // right parity: not blocked
                }
                if n == 0 && !rhs {
                    continue;
                }
                for xassign in 0..(1u64 << level) {
                    let mut clause = Vec::with_capacity(n + level);
                    for (bit, &col) in result_cols.iter().enumerate() {
                        let var = Variable::new(self.col_to_var[col]);
                        // Block value TRUE with a negative literal.
                        clause.push(if (assign >> bit) & 1 == 1 {
                            Literal::negative(var)
                        } else {
                            Literal::positive(var)
                        });
                    }
                    for (bit, &col) in cancelled_cols.iter().take(level).enumerate() {
                        let var = Variable::new(self.col_to_var[col]);
                        clause.push(if (xassign >> bit) & 1 == 1 {
                            Literal::negative(var)
                        } else {
                            Literal::positive(var)
                        });
                    }
                    out.push(clause);
                }
            }
        }
        true
    }

    /// Exact number of clauses for one resolution ladder, or `None` when its
    /// widest clause/shift arithmetic is outside the certified envelope.
    fn proof_ladder_clause_count(&self, step: &TraceStep) -> Option<usize> {
        let result_len = (0..self.num_cols).filter(|&c| step.result.get(c)).count();
        let cancelled_len = (0..self.num_cols)
            .filter(|&c| step.parent_a.get(c) && step.parent_b.get(c))
            .count();
        if result_len.checked_add(cancelled_len)? > MAX_XOR_PROOF_ROW_VARS {
            return None;
        }
        let wrong_parity_count = if result_len == 0 {
            usize::from(step.result.rhs)
        } else {
            1usize.checked_shl(u32::try_from(result_len - 1).ok()?)?
        };
        let levels = 1usize
            .checked_shl(u32::try_from(cancelled_len.checked_add(1)?).ok()?)?
            .checked_sub(1)?;
        wrong_parity_count.checked_mul(levels)
    }
}

#[cfg(test)]
mod proof_clause_encoding_tests {
    use super::*;

    /// One real elimination step with two result and two cancelled variables
    /// emits 2 * (2^3 - 1) ladder clauses and terminates in enc(x0 = x3).
    #[test]
    fn test_actual_elimination_ladder_count_and_terminal_encoding() {
        let constraints = vec![
            XorConstraint::new(vec![0, 1, 2], false),
            XorConstraint::new(vec![1, 2, 3], false),
        ];
        let mut solver = GaussianSolver::new(&constraints);
        let _ = solver.eliminate();
        let clauses = solver
            .try_generate_complete_proof_clauses()
            .expect("small ladder must fit");
        assert_eq!(clauses.len(), 14);
        let x0 = Variable::new(0);
        let x3 = Variable::new(3);
        assert_eq!(
            &clauses[12..],
            &[
                vec![Literal::negative(x0), Literal::positive(x3)],
                vec![Literal::positive(x0), Literal::negative(x3)],
            ]
        );
    }

    /// A proof route must reject the whole trace before consuming input XOR
    /// clauses when even one ladder exceeds the certified width envelope.
    #[test]
    fn test_complete_ladder_preflight_rejects_wide_elimination_step() {
        let vars: Vec<VarId> = (0..=MAX_XOR_PROOF_ROW_VARS as VarId).collect();
        let constraints = vec![
            XorConstraint::new(vars.clone(), false),
            XorConstraint::new(vars, true),
        ];
        let mut solver = GaussianSolver::new(&constraints);
        assert!(matches!(solver.eliminate(), GaussResult::Conflict(_)));
        assert!(!solver.has_complete_proof_ladder());
        assert!(solver.try_generate_complete_proof_clauses().is_none());
        assert!(solver.generate_proof_clauses().is_empty());
    }
}
