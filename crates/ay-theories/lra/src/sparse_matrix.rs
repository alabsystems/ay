// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-linked sparse matrix for simplex tableau storage.
//!
//! Ported from Z3's `sparse_matrix.h` / `sparse_matrix_def.h` (MIT license,
//! Nikolaj Bjorner 2014). The key design is unsorted row/column entry arrays
//! with dead-slot free lists and cross-references between row entries and
//! column entries. A per-matrix "work vector" enables O(1) coefficient lookup
//! during the `add_scaled_row` operation (Z3's `add` method).
//!
//! Reference: `reference/z3/src/math/simplex/sparse_matrix_def.h`
//!
//! # Performance characteristics
//!
//! | Operation               | Old (sorted Vec) | New (sparse matrix) |
//! |-------------------------|-------------------|---------------------|
//! | Coefficient lookup      | O(log w)          | O(1) via work vec   |
//! | Row iteration           | O(w)              | O(w + dead)         |
//! | Column iteration        | O(col_size)       | O(col_size + dead)  |
//! | add_scaled_row (pivot)  | O(w log w)        | O(w)                |
//! | Insert entry            | O(w) shift        | O(1) amortized      |
//! | Remove entry            | O(w) shift        | O(1)                |

#![allow(dead_code)]

use num_traits::{One, Zero};

use crate::rational::Rational;

/// Sentinel value indicating "no entry" in linked list indices.
const NONE: u32 = u32::MAX;

/// A row entry in the sparse matrix, matching Z3's `_row_entry`.
///
/// Stores the coefficient value, the column (variable) it belongs to,
/// and a cross-reference to the position in the column's entry array.
#[derive(Debug, Clone)]
pub(crate) struct RowEntry {
    /// Variable (column) index.
    pub(crate) var: u32,
    /// Coefficient value.
    pub(crate) coeff: Rational,
    /// Index into `SparseMatrix::columns[var].entries` for the corresponding
    /// column entry. Enables O(1) deletion from both row and column.
    /// Z3: `_row_entry::m_col_idx`.
    /// When the entry is dead, this field is repurposed as the next-free
    /// pointer in the row's free list.
    col_idx: i32,
}

impl RowEntry {
    #[inline]
    fn is_dead(&self) -> bool {
        self.var == NONE
    }
}

/// A column entry in the sparse matrix, matching Z3's `col_entry`.
///
/// Points back to the row and the position within the row's entry array.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ColEntry {
    /// Row ID that this entry belongs to.
    pub(crate) row_id: u32,
    /// Index into `SparseMatrix::rows[row_id].entries` for the corresponding
    /// row entry. Enables O(1) coefficient access from a column traversal.
    /// When dead, repurposed as next-free pointer in the column's free list.
    /// Z3: `col_entry::m_row_idx`.
    row_idx: i32,
}

impl ColEntry {
    #[inline]
    fn is_dead(&self) -> bool {
        self.row_id == NONE
    }
}

/// A row in the sparse matrix. Contains an entry array with possible dead slots
/// and a free list for recycling. Z3: `_row`.
#[derive(Debug, Clone)]
pub(crate) struct Row {
    /// Row entries (may contain dead slots marked with `var == NONE`).
    entries: Vec<RowEntry>,
    /// Number of live (non-dead) entries.
    size: u32,
    /// Head of free list within `entries` (-1 = empty).
    /// Dead entries chain through `col_idx` as next-free pointer.
    first_free_idx: i32,
}

impl Row {
    fn new() -> Self {
        Self {
            entries: Vec::new(),
            size: 0,
            first_free_idx: -1,
        }
    }

    /// Number of live entries.
    #[inline]
    pub(crate) fn size(&self) -> u32 {
        self.size
    }

    /// Total slots (live + dead).
    #[inline]
    fn num_entries(&self) -> usize {
        self.entries.len()
    }

    /// Allocate a new row entry slot, returning its index. Reuses dead slots.
    fn add_entry(&mut self) -> u32 {
        self.size += 1;
        if self.first_free_idx == -1 {
            let idx = self.entries.len() as u32;
            self.entries.push(RowEntry {
                var: NONE,
                coeff: Rational::zero(),
                col_idx: 0,
            });
            idx
        } else {
            let idx = self.first_free_idx as u32;
            let entry = &self.entries[idx as usize];
            debug_assert!(entry.is_dead());
            self.first_free_idx = entry.col_idx; // next in free chain
            idx
        }
    }

    /// Mark entry at `idx` as dead and add to free list.
    fn del_entry(&mut self, idx: u32) {
        let entry = &mut self.entries[idx as usize];
        debug_assert!(!entry.is_dead(), "double-delete of row entry");
        entry.col_idx = self.first_free_idx;
        entry.var = NONE;
        self.size -= 1;
        self.first_free_idx = idx as i32;
    }

    /// Compress: remove dead entries, update column cross-references.
    /// Z3: `_row::compress`.
    fn compress(&mut self, columns: &mut [Column]) {
        let mut j = 0usize;
        for i in 0..self.entries.len() {
            if !self.entries[i].is_dead() {
                if i != j {
                    // Move entry from i to j, update column cross-ref
                    let var = self.entries[i].var;
                    let col_idx = self.entries[i].col_idx;
                    let coeff = self.entries[i].coeff.clone();

                    self.entries[j].var = var;
                    self.entries[j].coeff = coeff;
                    self.entries[j].col_idx = col_idx;

                    // Update column's back-pointer to new position
                    if (var as usize) < columns.len() {
                        columns[var as usize].entries[col_idx as usize].row_idx = j as i32;
                    }
                }
                j += 1;
            }
        }
        debug_assert_eq!(j, self.size as usize);
        self.entries.truncate(j);
        self.first_free_idx = -1;
    }

    /// Compress if more than half the entries are dead.
    fn compress_if_needed(&mut self, columns: &mut [Column]) {
        if self.size > 0 && (self.size as usize) * 2 < self.num_entries() {
            self.compress(columns);
        }
    }

    /// Populate the work vector with (var -> entry_idx) mappings for this row.
    /// Z3: `_row::save_var_pos`.
    #[inline]
    fn save_var_pos(&self, work_vec: &mut [i32], dirty: &mut Vec<u32>) {
        for (idx, entry) in self.entries.iter().enumerate() {
            if !entry.is_dead() {
                work_vec[entry.var as usize] = idx as i32;
                dirty.push(entry.var);
            }
        }
    }
}

/// A column in the sparse matrix. Stores which rows contain a non-zero entry
/// for this variable. Z3: `column`.
#[derive(Debug, Clone)]
pub(crate) struct Column {
    /// Column entries (may contain dead slots marked with `row_id == NONE`).
    entries: Vec<ColEntry>,
    /// Number of live entries.
    size: u32,
    /// Head of free list (-1 = empty).
    first_free_idx: i32,
    /// Reference count: incremented while iterating, blocks compression.
    /// Z3: `m_refs`.
    refs: u32,
}

impl Column {
    fn new() -> Self {
        Self {
            entries: Vec::new(),
            size: 0,
            first_free_idx: -1,
            refs: 0,
        }
    }

    /// Number of live entries (rows containing this variable).
    #[inline]
    pub(crate) fn size(&self) -> u32 {
        self.size
    }

    /// Allocate a new column entry slot, returning its index.
    fn add_entry(&mut self) -> i32 {
        self.size += 1;
        if self.first_free_idx == -1 {
            let idx = self.entries.len() as i32;
            self.entries.push(ColEntry {
                row_id: NONE,
                row_idx: 0,
            });
            idx
        } else {
            let idx = self.first_free_idx;
            let entry = &self.entries[idx as usize];
            debug_assert!(entry.is_dead());
            self.first_free_idx = entry.row_idx; // next in free chain
            idx
        }
    }

    /// Mark entry at `idx` as dead and add to free list.
    fn del_entry(&mut self, idx: u32) {
        let entry = &mut self.entries[idx as usize];
        debug_assert!(!entry.is_dead(), "double-delete of column entry");
        entry.row_id = NONE;
        entry.row_idx = self.first_free_idx;
        self.first_free_idx = idx as i32;
        self.size -= 1;
    }

    /// Compress: remove dead entries, update row cross-references.
    fn compress(&mut self, rows: &mut [Row]) {
        if self.refs > 0 {
            return; // active iterator, defer compression
        }
        let mut j = 0usize;
        for i in 0..self.entries.len() {
            if !self.entries[i].is_dead() {
                if i != j {
                    let row_id = self.entries[i].row_id;
                    let row_idx = self.entries[i].row_idx;
                    self.entries[j] = ColEntry { row_id, row_idx };
                    // Update row's back-pointer to new position
                    rows[row_id as usize].entries[row_idx as usize].col_idx = j as i32;
                }
                j += 1;
            }
        }
        debug_assert_eq!(j, self.size as usize);
        self.entries.truncate(j);
        self.first_free_idx = -1;
    }

    /// Compress if more than half the entries are dead.
    fn compress_if_needed(&mut self, rows: &mut [Row]) {
        if self.size > 0 && (self.size as usize) * 2 < self.entries.len() && self.refs == 0 {
            self.compress(rows);
        }
    }
}

/// Cross-linked sparse matrix for simplex tableau storage.
///
/// Matches Z3's `sparse_matrix` architecture: rows and columns contain
/// entry arrays with dead-slot free lists, cross-referenced via indices.
/// A shared work vector enables O(1) coefficient lookup during pivot operations.
#[derive(Debug, Clone)]
pub(crate) struct SparseMatrix {
    /// Row storage, indexed by row ID.
    pub(crate) rows: Vec<Row>,
    /// Dead rows available for reuse. Z3: `m_dead_rows`.
    dead_rows: Vec<u32>,
    /// Column storage, indexed by variable ID.
    pub(crate) columns: Vec<Column>,
    /// Work vector: maps variable -> entry index within a row.
    /// -1 means "not present". Used by `add_scaled_row` for O(1) lookup.
    /// Z3: `m_var_pos`.
    work_vec: Vec<i32>,
    /// Variables whose work_vec entry is dirty (non -1).
    /// Used for efficient reset. Z3: `m_var_pos_idx`.
    work_vec_dirty: Vec<u32>,
}

impl SparseMatrix {
    pub(crate) fn new() -> Self {
        Self {
            rows: Vec::new(),
            dead_rows: Vec::new(),
            columns: Vec::new(),
            work_vec: Vec::new(),
            work_vec_dirty: Vec::new(),
        }
    }

    /// Ensure variable `v` has column storage allocated.
    /// Z3: `ensure_var`.
    pub(crate) fn ensure_var(&mut self, v: u32) {
        let needed = v as usize + 1;
        while self.columns.len() < needed {
            self.columns.push(Column::new());
        }
        if self.work_vec.len() < needed {
            self.work_vec.resize(needed, -1);
        }
    }

    /// Allocate a new row (or reuse a dead one). Returns the row ID.
    /// Z3: `mk_row`.
    pub(crate) fn mk_row(&mut self) -> u32 {
        if let Some(id) = self.dead_rows.pop() {
            id
        } else {
            let id = self.rows.len() as u32;
            self.rows.push(Row::new());
            id
        }
    }

    /// Add a variable with coefficient `coeff` to row `row_id`.
    /// Z3: `add_var`.
    pub(crate) fn add_var(&mut self, row_id: u32, var: u32, coeff: Rational) {
        if coeff.is_zero() {
            return;
        }
        self.ensure_var(var);

        let row = &mut self.rows[row_id as usize];
        let r_idx = row.add_entry();

        let col = &mut self.columns[var as usize];
        let c_idx = col.add_entry();

        // Fill row entry
        let r_entry = &mut row.entries[r_idx as usize];
        r_entry.var = var;
        r_entry.coeff = coeff;
        r_entry.col_idx = c_idx;

        // Fill column entry
        let c_entry = &mut col.entries[c_idx as usize];
        c_entry.row_id = row_id;
        c_entry.row_idx = r_idx as i32;
    }

    /// Delete a row entry at position `pos` in the row, updating column cross-refs.
    /// Z3: `del_row_entry`.
    fn del_row_entry(&mut self, row_id: u32, pos: u32) {
        let row = &mut self.rows[row_id as usize];
        let entry = &row.entries[pos as usize];
        let var = entry.var;
        let col_idx = entry.col_idx;

        row.del_entry(pos);

        let col = &mut self.columns[var as usize];
        col.del_entry(col_idx as u32);
        col.compress_if_needed(&mut self.rows);
    }

    /// Delete an entire row, removing all its entries from columns.
    /// Z3: `del`.
    pub(crate) fn del_row(&mut self, row_id: u32) {
        let num_entries = self.rows[row_id as usize].entries.len();
        for i in 0..num_entries {
            if !self.rows[row_id as usize].entries[i].is_dead() {
                self.del_row_entry(row_id, i as u32);
            }
        }
        debug_assert_eq!(self.rows[row_id as usize].size, 0);
        self.dead_rows.push(row_id);
    }

    /// Get the coefficient of variable `var` in row `row_id`.
    /// Linear scan -- use `work_vec_coeff` in hot paths.
    pub(crate) fn get_coeff(&self, row_id: u32, var: u32) -> Option<&Rational> {
        let row = &self.rows[row_id as usize];
        for entry in &row.entries {
            if !entry.is_dead() && entry.var == var {
                return Some(&entry.coeff);
            }
        }
        None
    }

    /// Number of live entries in a row.
    #[inline]
    pub(crate) fn row_size(&self, row_id: u32) -> u32 {
        self.rows[row_id as usize].size()
    }

    /// Number of rows containing variable `var`.
    #[inline]
    pub(crate) fn col_size(&self, var: u32) -> u32 {
        if (var as usize) < self.columns.len() {
            self.columns[var as usize].size()
        } else {
            0
        }
    }

    /// Iterate over live entries in a row, yielding `(var, &coeff)`.
    #[inline]
    pub(crate) fn row_iter(&self, row_id: u32) -> RowIter<'_> {
        RowIter {
            entries: &self.rows[row_id as usize].entries,
            pos: 0,
        }
    }

    /// Iterate over live entries in a column, yielding `(row_id, &coeff)`.
    /// The coefficient is accessed through the row entry cross-reference.
    pub(crate) fn col_iter(&self, var: u32) -> ColIter<'_> {
        if (var as usize) >= self.columns.len() {
            return ColIter {
                col_entries: &[],
                rows: &self.rows,
                pos: 0,
            };
        }
        ColIter {
            col_entries: &self.columns[var as usize].entries,
            rows: &self.rows,
            pos: 0,
        }
    }

    /// Populate the work vector for row `row_id`, enabling O(1) lookups.
    /// Must be followed by `clear_work_vec()` after use.
    /// Z3: `_row::save_var_pos`.
    pub(crate) fn prepare_work_vec(&mut self, row_id: u32) {
        self.rows[row_id as usize].save_var_pos(&mut self.work_vec, &mut self.work_vec_dirty);
    }

    /// Reset work vector entries that were set by `prepare_work_vec`.
    /// Z3: resetting `m_var_pos` via `m_var_pos_idx`.
    #[inline]
    pub(crate) fn clear_work_vec(&mut self) {
        for &var in &self.work_vec_dirty {
            self.work_vec[var as usize] = -1;
        }
        self.work_vec_dirty.clear();
    }

    /// O(1) lookup using the work vector. Returns the entry index in the
    /// prepared row, or None if the variable is not present.
    #[inline]
    pub(crate) fn work_vec_get(&self, var: u32) -> Option<u32> {
        if (var as usize) < self.work_vec.len() {
            let idx = self.work_vec[var as usize];
            if idx >= 0 {
                return Some(idx as u32);
            }
        }
        None
    }

    /// O(1) coefficient reference using the work vector.
    /// Assumes `prepare_work_vec` was called for the row containing this var.
    #[inline]
    pub(crate) fn work_vec_coeff(&self, row_id: u32, var: u32) -> Option<&Rational> {
        self.work_vec_get(var)
            .map(|idx| &self.rows[row_id as usize].entries[idx as usize].coeff)
    }

    /// Set `dst_row += src_row * scale`, using the work vector for O(1) lookup.
    /// This is the critical hot path for pivot operations.
    ///
    /// Z3: `sparse_matrix::add` with the `ADD_ROW` macro
    /// (`sparse_matrix_def.h:321-388`).
    ///
    /// Returns the list of variables that were added to / removed from `dst_row`
    /// (for column index maintenance by the caller).
    pub(crate) fn add_scaled_row(
        &mut self,
        dst_row: u32,
        src_row: u32,
        scale: &Rational,
    ) -> (Vec<u32>, Vec<u32>) {
        let mut added = Vec::new();
        let mut removed = Vec::new();

        // 1. Populate work vector for dst_row
        self.rows[dst_row as usize].save_var_pos(&mut self.work_vec, &mut self.work_vec_dirty);

        // 2. Iterate over src_row entries, merging into dst_row
        let scale_is_one = scale.is_one();
        let scale_is_neg_one = scale.is_neg_one();

        // Collect src entries to avoid borrow conflict with self.rows
        let src_entries: Vec<(u32, Rational)> = self.rows[src_row as usize]
            .entries
            .iter()
            .filter(|e| !e.is_dead())
            .map(|e| (e.var, e.coeff.clone()))
            .collect();

        for (var, src_coeff) in src_entries {
            let pos = self.work_vec[var as usize];
            if pos == -1 {
                // Variable not in dst_row -- add new entry
                let scaled = if scale_is_one {
                    src_coeff
                } else if scale_is_neg_one {
                    -&src_coeff
                } else {
                    &src_coeff * scale
                };
                if !scaled.is_zero() {
                    self.add_var(dst_row, var, scaled);
                    // Update work_vec for this new entry (last added entry)
                    let new_idx = self.rows[dst_row as usize].entries.len() as i32 - 1;
                    self.work_vec[var as usize] = new_idx;
                    self.work_vec_dirty.push(var);
                    added.push(var);
                }
            } else {
                // Variable already in dst_row -- add to existing coefficient
                let pos = pos as usize;
                let entry = &mut self.rows[dst_row as usize].entries[pos];
                if scale_is_one {
                    entry.coeff += &src_coeff;
                } else if scale_is_neg_one {
                    entry.coeff -= &src_coeff;
                } else {
                    entry.coeff += &src_coeff * scale;
                }
                if entry.coeff.is_zero() {
                    // Coefficient cancelled out -- remove entry
                    let v = entry.var;
                    self.del_row_entry(dst_row, pos as u32);
                    removed.push(v);
                }
            }
        }

        // 3. Reset work vector
        for &var in &self.work_vec_dirty {
            self.work_vec[var as usize] = -1;
        }
        self.work_vec_dirty.clear();

        // 4. Compress dst_row if needed
        self.rows[dst_row as usize].compress_if_needed(&mut self.columns);

        (added, removed)
    }

    /// Multiply all entries in a row by `n`. Z3: `mul`.
    pub(crate) fn mul_row(&mut self, row_id: u32, n: &Rational) {
        if n.is_one() {
            return;
        }
        let row = &mut self.rows[row_id as usize];
        if n.is_neg_one() {
            for entry in &mut row.entries {
                if !entry.is_dead() {
                    entry.coeff = -&entry.coeff;
                }
            }
        } else {
            for entry in &mut row.entries {
                if !entry.is_dead() {
                    entry.coeff = &entry.coeff * n;
                }
            }
        }
    }

    /// Negate all entries in a row. Z3: `neg`.
    #[allow(dead_code)]
    pub(crate) fn neg_row(&mut self, row_id: u32) {
        let row = &mut self.rows[row_id as usize];
        for entry in &mut row.entries {
            if !entry.is_dead() {
                entry.coeff = -&entry.coeff;
            }
        }
    }

    /// Collect row entries as sorted `(var, coeff)` pairs.
    /// Used for compatibility with the existing `TableauRow` API.
    pub(crate) fn row_to_sorted_coeffs(&self, row_id: u32) -> Vec<(u32, Rational)> {
        let mut coeffs: Vec<(u32, Rational)> = self.rows[row_id as usize]
            .entries
            .iter()
            .filter(|e| !e.is_dead())
            .map(|e| (e.var, e.coeff.clone()))
            .collect();
        coeffs.sort_unstable_by_key(|(v, _)| *v);
        coeffs
    }

    /// Build the matrix from a set of `TableauRow` entries.
    /// Used for migrating from the old representation.
    pub(crate) fn from_tableau_rows(rows: &[super::tableau::TableauRow]) -> Self {
        let mut matrix = Self::new();

        for (row_idx, trow) in rows.iter().enumerate() {
            // Ensure the row exists
            while matrix.rows.len() <= row_idx {
                matrix.mk_row();
            }

            // Add each coefficient
            for &(var, ref coeff) in &trow.coeffs {
                matrix.add_var(row_idx as u32, var, coeff.clone());
            }
        }

        matrix
    }

    /// Check structural consistency (debug only).
    #[cfg(debug_assertions)]
    pub(crate) fn well_formed(&self) -> bool {
        // Check each row
        for (row_id, row) in self.rows.iter().enumerate() {
            let mut live_count = 0u32;
            for (entry_idx, entry) in row.entries.iter().enumerate() {
                if entry.is_dead() {
                    continue;
                }
                live_count += 1;

                // Cross-check: column entry points back to this row entry
                let var = entry.var;
                assert!(
                    (var as usize) < self.columns.len(),
                    "row {row_id} entry {entry_idx}: var {var} out of column range"
                );
                let col = &self.columns[var as usize];
                let col_entry = &col.entries[entry.col_idx as usize];
                assert!(
                    !col_entry.is_dead(),
                    "row {row_id} entry {entry_idx}: col entry is dead"
                );
                assert_eq!(
                    col_entry.row_id, row_id as u32,
                    "row {row_id} entry {entry_idx}: col entry row_id mismatch"
                );
                assert_eq!(
                    col_entry.row_idx, entry_idx as i32,
                    "row {row_id} entry {entry_idx}: col entry row_idx mismatch"
                );
            }
            assert_eq!(
                live_count, row.size,
                "row {row_id}: live count {live_count} != size {}",
                row.size
            );
        }

        // Check each column
        for (col_id, col) in self.columns.iter().enumerate() {
            let mut live_count = 0u32;
            for (entry_idx, entry) in col.entries.iter().enumerate() {
                if entry.is_dead() {
                    continue;
                }
                live_count += 1;

                // Cross-check: row entry points back to this column entry
                let row = &self.rows[entry.row_id as usize];
                let row_entry = &row.entries[entry.row_idx as usize];
                assert!(
                    !row_entry.is_dead(),
                    "col {col_id} entry {entry_idx}: row entry is dead"
                );
                assert_eq!(
                    row_entry.var, col_id as u32,
                    "col {col_id} entry {entry_idx}: row entry var mismatch"
                );
                assert_eq!(
                    row_entry.col_idx, entry_idx as i32,
                    "col {col_id} entry {entry_idx}: row entry col_idx mismatch"
                );
            }
            assert_eq!(
                live_count, col.size,
                "col {col_id}: live count {live_count} != size {}",
                col.size
            );
        }

        true
    }
}

/// Iterator over live entries in a row. Yields `(var, &coeff)`.
pub(crate) struct RowIter<'a> {
    entries: &'a [RowEntry],
    pos: usize,
}

impl<'a> Iterator for RowIter<'a> {
    type Item = (u32, &'a Rational);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.pos < self.entries.len() {
            let entry = &self.entries[self.pos];
            self.pos += 1;
            if !entry.is_dead() {
                return Some((entry.var, &entry.coeff));
            }
        }
        None
    }
}

/// Iterator over live entries in a column. Yields `(row_id, &coeff)`.
pub(crate) struct ColIter<'a> {
    col_entries: &'a [ColEntry],
    rows: &'a [Row],
    pos: usize,
}

impl<'a> Iterator for ColIter<'a> {
    type Item = (u32, &'a Rational);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.pos < self.col_entries.len() {
            let ce = &self.col_entries[self.pos];
            self.pos += 1;
            if !ce.is_dead() {
                let row_entry = &self.rows[ce.row_id as usize].entries[ce.row_idx as usize];
                return Some((ce.row_id, &row_entry.coeff));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> Rational {
        Rational::from(n)
    }

    #[test]
    fn test_sparse_matrix_basic_insert_and_iterate() {
        let mut m = SparseMatrix::new();
        m.ensure_var(3);
        let r0 = m.mk_row();
        m.add_var(r0, 0, rat(3));
        m.add_var(r0, 2, rat(-5));
        m.add_var(r0, 1, rat(7));

        // Row iteration (unordered)
        let entries: Vec<(u32, Rational)> = m.row_iter(r0).map(|(v, c)| (v, c.clone())).collect();
        assert_eq!(entries.len(), 3);
        assert!(entries.iter().any(|(v, c)| *v == 0 && *c == rat(3)));
        assert!(entries.iter().any(|(v, c)| *v == 1 && *c == rat(7)));
        assert!(entries.iter().any(|(v, c)| *v == 2 && *c == rat(-5)));

        // Column iteration
        let col0: Vec<_> = m.col_iter(0).collect();
        assert_eq!(col0.len(), 1);
        assert_eq!(col0[0].0, r0);
        assert_eq!(col0[0].1.clone(), rat(3));
    }

    #[test]
    fn test_sparse_matrix_row_size_and_col_size() {
        let mut m = SparseMatrix::new();
        m.ensure_var(2);
        let r0 = m.mk_row();
        let r1 = m.mk_row();
        m.add_var(r0, 0, rat(1));
        m.add_var(r0, 1, rat(2));
        m.add_var(r1, 1, rat(3));

        assert_eq!(m.row_size(r0), 2);
        assert_eq!(m.row_size(r1), 1);
        assert_eq!(m.col_size(0), 1);
        assert_eq!(m.col_size(1), 2);
    }

    #[test]
    fn test_sparse_matrix_get_coeff() {
        let mut m = SparseMatrix::new();
        m.ensure_var(2);
        let r0 = m.mk_row();
        m.add_var(r0, 0, rat(42));
        m.add_var(r0, 2, rat(-7));

        assert_eq!(m.get_coeff(r0, 0), Some(&rat(42)));
        assert_eq!(m.get_coeff(r0, 1), None);
        assert_eq!(m.get_coeff(r0, 2), Some(&rat(-7)));
    }

    #[test]
    fn test_sparse_matrix_del_row() {
        let mut m = SparseMatrix::new();
        m.ensure_var(1);
        let r0 = m.mk_row();
        m.add_var(r0, 0, rat(1));
        m.add_var(r0, 1, rat(2));
        assert_eq!(m.col_size(0), 1);
        assert_eq!(m.col_size(1), 1);

        m.del_row(r0);
        assert_eq!(m.row_size(r0), 0);
        assert_eq!(m.col_size(0), 0);
        assert_eq!(m.col_size(1), 0);
    }

    #[test]
    fn test_sparse_matrix_dead_row_reuse() {
        let mut m = SparseMatrix::new();
        m.ensure_var(0);
        let r0 = m.mk_row();
        m.add_var(r0, 0, rat(1));
        m.del_row(r0);

        let r1 = m.mk_row();
        assert_eq!(r1, r0, "dead row should be reused");
        assert_eq!(m.row_size(r1), 0);
    }

    #[test]
    fn test_sparse_matrix_work_vec() {
        let mut m = SparseMatrix::new();
        m.ensure_var(3);
        let r0 = m.mk_row();
        m.add_var(r0, 0, rat(10));
        m.add_var(r0, 2, rat(20));
        m.add_var(r0, 3, rat(30));

        m.prepare_work_vec(r0);
        assert!(m.work_vec_get(0).is_some());
        assert!(m.work_vec_get(1).is_none());
        assert!(m.work_vec_get(2).is_some());
        assert!(m.work_vec_get(3).is_some());

        // O(1) coefficient access
        assert_eq!(m.work_vec_coeff(r0, 0), Some(&rat(10)));
        assert_eq!(m.work_vec_coeff(r0, 2), Some(&rat(20)));

        m.clear_work_vec();
        assert!(m.work_vec_get(0).is_none());
        assert!(m.work_vec_get(2).is_none());
    }

    #[test]
    fn test_sparse_matrix_add_scaled_row_basic() {
        let mut m = SparseMatrix::new();
        m.ensure_var(3);

        // dst = 3*x0 + 7*x2
        let dst = m.mk_row();
        m.add_var(dst, 0, rat(3));
        m.add_var(dst, 2, rat(7));

        // src = 1*x0 + 2*x1 + (-3)*x3
        let src = m.mk_row();
        m.add_var(src, 0, rat(1));
        m.add_var(src, 1, rat(2));
        m.add_var(src, 3, rat(-3));

        // dst += src * 2
        // Expected: dst = (3+2)*x0 + (4)*x1 + 7*x2 + (-6)*x3
        let (added, removed) = m.add_scaled_row(dst, src, &rat(2));

        let coeffs = m.row_to_sorted_coeffs(dst);
        assert_eq!(coeffs.len(), 4);
        assert_eq!(coeffs[0], (0, rat(5)));
        assert_eq!(coeffs[1], (1, rat(4)));
        assert_eq!(coeffs[2], (2, rat(7)));
        assert_eq!(coeffs[3], (3, rat(-6)));

        assert_eq!(added.len(), 2); // x1, x3 were new
        assert!(removed.is_empty());
    }

    #[test]
    fn test_sparse_matrix_add_scaled_row_cancellation() {
        let mut m = SparseMatrix::new();
        m.ensure_var(1);

        // dst = 5*x0 + 3*x1
        let dst = m.mk_row();
        m.add_var(dst, 0, rat(5));
        m.add_var(dst, 1, rat(3));

        // src = (-5)*x0 + 1*x1
        let src = m.mk_row();
        m.add_var(src, 0, rat(-5));
        m.add_var(src, 1, rat(1));

        // dst += src * 1  => dst = 0*x0 + 4*x1
        let (added, removed) = m.add_scaled_row(dst, src, &rat(1));

        let coeffs = m.row_to_sorted_coeffs(dst);
        assert_eq!(coeffs.len(), 1);
        assert_eq!(coeffs[0], (1, rat(4)));

        assert!(added.is_empty());
        assert_eq!(removed, vec![0]); // x0 was removed due to cancellation
    }

    #[test]
    fn test_sparse_matrix_mul_row() {
        let mut m = SparseMatrix::new();
        m.ensure_var(1);
        let r0 = m.mk_row();
        m.add_var(r0, 0, rat(3));
        m.add_var(r0, 1, rat(-2));

        m.mul_row(r0, &rat(4));

        let coeffs = m.row_to_sorted_coeffs(r0);
        assert_eq!(coeffs, vec![(0, rat(12)), (1, rat(-8))]);
    }

    #[test]
    fn test_sparse_matrix_row_to_sorted_coeffs() {
        let mut m = SparseMatrix::new();
        m.ensure_var(4);
        let r0 = m.mk_row();
        m.add_var(r0, 4, rat(1));
        m.add_var(r0, 1, rat(2));
        m.add_var(r0, 3, rat(3));

        let sorted = m.row_to_sorted_coeffs(r0);
        assert_eq!(sorted, vec![(1, rat(2)), (3, rat(3)), (4, rat(1))]);
    }

    #[test]
    fn test_sparse_matrix_well_formed_after_operations() {
        let mut m = SparseMatrix::new();
        m.ensure_var(2);
        let r0 = m.mk_row();
        let r1 = m.mk_row();
        m.add_var(r0, 0, rat(1));
        m.add_var(r0, 1, rat(2));
        m.add_var(r0, 2, rat(3));
        m.add_var(r1, 0, rat(4));
        m.add_var(r1, 2, rat(5));

        #[cfg(debug_assertions)]
        assert!(m.well_formed());

        // After add_scaled_row
        let _ = m.add_scaled_row(r1, r0, &rat(-1));
        // r1 = (4-1)*x0 + (-2)*x1 + (5-3)*x2 = 3*x0 + (-2)*x1 + 2*x2

        #[cfg(debug_assertions)]
        assert!(m.well_formed());
    }

    #[test]
    fn test_sparse_matrix_col_iter_multi_row() {
        let mut m = SparseMatrix::new();
        m.ensure_var(0);
        let r0 = m.mk_row();
        let r1 = m.mk_row();
        let r2 = m.mk_row();
        m.add_var(r0, 0, rat(10));
        m.add_var(r1, 0, rat(20));
        m.add_var(r2, 0, rat(30));

        let col0: Vec<_> = m.col_iter(0).map(|(row, c)| (row, c.clone())).collect();
        assert_eq!(col0.len(), 3);
        assert!(col0.iter().any(|(r, c)| *r == 0 && *c == rat(10)));
        assert!(col0.iter().any(|(r, c)| *r == 1 && *c == rat(20)));
        assert!(col0.iter().any(|(r, c)| *r == 2 && *c == rat(30)));
    }

    #[test]
    fn test_sparse_matrix_from_tableau_rows() {
        use crate::tableau::TableauRow;

        let rows = vec![
            TableauRow::new_rat(0, vec![(1, rat(3)), (2, rat(-5))], rat(7)),
            TableauRow::new_rat(1, vec![(0, rat(2)), (2, rat(4))], rat(0)),
        ];

        let m = SparseMatrix::from_tableau_rows(&rows);
        assert_eq!(m.rows.len(), 2);
        assert_eq!(m.row_size(0), 2);
        assert_eq!(m.row_size(1), 2);

        // Check coefficients match
        let r0_sorted = m.row_to_sorted_coeffs(0);
        assert_eq!(r0_sorted, vec![(1, rat(3)), (2, rat(-5))]);
        let r1_sorted = m.row_to_sorted_coeffs(1);
        assert_eq!(r1_sorted, vec![(0, rat(2)), (2, rat(4))]);

        // Check column sizes
        assert_eq!(m.col_size(0), 1); // only in row 1
        assert_eq!(m.col_size(1), 1); // only in row 0
        assert_eq!(m.col_size(2), 2); // in both rows

        #[cfg(debug_assertions)]
        assert!(m.well_formed());
    }

    #[test]
    fn test_sparse_matrix_add_scaled_row_neg_one_scale() {
        let mut m = SparseMatrix::new();
        m.ensure_var(1);

        let dst = m.mk_row();
        m.add_var(dst, 0, rat(10));
        m.add_var(dst, 1, rat(5));

        let src = m.mk_row();
        m.add_var(src, 0, rat(3));
        m.add_var(src, 1, rat(2));

        // dst += src * (-1) => dst = (10-3)*x0 + (5-2)*x1 = 7*x0 + 3*x1
        let _ = m.add_scaled_row(dst, src, &rat(-1));

        let coeffs = m.row_to_sorted_coeffs(dst);
        assert_eq!(coeffs, vec![(0, rat(7)), (1, rat(3))]);
    }

    #[test]
    fn test_sparse_matrix_add_scaled_row_zero_result() {
        // All entries cancel out
        let mut m = SparseMatrix::new();
        m.ensure_var(1);

        let dst = m.mk_row();
        m.add_var(dst, 0, rat(3));
        m.add_var(dst, 1, rat(7));

        let src = m.mk_row();
        m.add_var(src, 0, rat(3));
        m.add_var(src, 1, rat(7));

        let (_, removed) = m.add_scaled_row(dst, src, &rat(-1));

        assert_eq!(m.row_size(dst), 0);
        assert_eq!(removed.len(), 2);
    }
}
