// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Packed bit row for GF(2) matrix operations.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use crate::constraint::XorConstraint;
use crate::VarId;

/// Iterator over set bits in a u64 word.
///
/// Efficiently iterates only over the 1 bits using the x & (x-1) trick.
pub(crate) struct SetBitsIter {
    word: u64,
    base_col: usize,
    num_cols: usize,
}

impl Iterator for SetBitsIter {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.word == 0 {
            return None;
        }
        let bit = self.word.trailing_zeros() as usize;
        self.word &= self.word - 1; // Clear lowest set bit
        let col = self.base_col + bit;
        if col < self.num_cols {
            Some(col)
        } else {
            None
        }
    }
}

/// Packed bit row for GF(2) matrix operations.
///
/// Stores a row of the matrix as packed bits for efficient XOR operations.
/// Each u64 holds 64 column values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PackedRow {
    /// Bits representing column values (column i is bit i%64 of bits[i/64]).
    pub(crate) bits: Vec<u64>,
    /// Right-hand side of the equation.
    pub(crate) rhs: bool,
    /// Number of columns (for bounds checking).
    num_cols: usize,
}

impl PackedRow {
    /// Create a new packed row with the given number of columns.
    pub(crate) fn new(num_cols: usize) -> Self {
        let num_words = num_cols.div_ceil(64);
        Self {
            bits: vec![0; num_words],
            rhs: false,
            num_cols,
        }
    }

    /// Clear all bits in the row.
    pub(crate) fn clear_all(&mut self) {
        self.bits.fill(0);
        self.rhs = false;
    }

    /// Set all in-range bits to 1.
    pub(crate) fn fill_ones(&mut self) {
        self.bits.fill(!0);
        if let Some(last_word) = self.bits.last_mut() {
            let used_bits = self.num_cols % 64;
            if used_bits != 0 {
                *last_word = (1u64 << used_bits) - 1;
            }
        }
        self.rhs = false;
    }

    /// Create a row from an XOR constraint given a variable-to-column mapping.
    pub(crate) fn from_xor(
        xor: &XorConstraint,
        var_to_col: &HashMap<VarId, usize>,
        num_cols: usize,
    ) -> Self {
        let mut row = Self::new(num_cols);
        row.rhs = xor.rhs;
        for &var in &xor.vars {
            if let Some(&col) = var_to_col.get(&var) {
                row.set(col, true);
            }
        }
        row
    }

    /// Get the value at a column.
    pub(crate) fn get(&self, col: usize) -> bool {
        debug_assert!(col < self.num_cols);
        let word = col / 64;
        let bit = col % 64;
        (self.bits[word] >> bit) & 1 == 1
    }

    /// Set the value at a column.
    pub(crate) fn set(&mut self, col: usize, value: bool) {
        debug_assert!(col < self.num_cols);
        let word = col / 64;
        let bit = col % 64;
        if value {
            self.bits[word] |= 1 << bit;
        } else {
            self.bits[word] &= !(1 << bit);
        }
    }

    /// XOR another row into this one (row += other in GF(2)).
    pub(crate) fn xor_in(&mut self, other: &Self) {
        debug_assert_eq!(self.bits.len(), other.bits.len());
        for (a, b) in self.bits.iter_mut().zip(&other.bits) {
            *a ^= *b;
        }
        self.rhs ^= other.rhs;
    }

    /// Return the parity of the bitwise intersection with another row.
    pub(crate) fn parity_of_and(&self, other: &Self) -> bool {
        debug_assert_eq!(self.bits.len(), other.bits.len());

        self.bits
            .iter()
            .zip(&other.bits)
            .fold(false, |parity, (a, b)| {
                parity ^ (((a & b).count_ones() & 1) == 1)
            })
    }

    /// Check if this row is all zeros.
    pub(crate) fn is_zero(&self) -> bool {
        self.bits.iter().all(|&w| w == 0)
    }

    /// Iterator over all set bit indices (columns with value 1).
    ///
    /// This is O(popcount) rather than O(num_cols), making it efficient
    /// for sparse rows. Uses bit manipulation tricks to iterate only
    /// over set bits.
    pub(crate) fn iter_set_bits(&self) -> impl Iterator<Item = usize> + '_ {
        self.bits
            .iter()
            .enumerate()
            .flat_map(move |(word_idx, &word)| {
                let base_col = word_idx * 64;
                let num_cols = self.num_cols;
                SetBitsIter {
                    word,
                    base_col,
                    num_cols,
                }
            })
    }

    /// Evaluate this row against packed assignment state.
    ///
    /// `cols_true` has a 1 for columns assigned to true.
    /// `cols_unset` has a 1 for columns that are currently unassigned.
    pub(crate) fn evaluate_with_column_state(
        &self,
        cols_true: &Self,
        cols_unset: &Self,
    ) -> RowState {
        debug_assert_eq!(self.bits.len(), cols_true.bits.len());
        debug_assert_eq!(self.bits.len(), cols_unset.bits.len());

        let mut unassigned_col = None;
        let parity = self.rhs ^ self.parity_of_and(cols_true);

        for (word_idx, &row_word) in self.bits.iter().enumerate() {
            let unset_word = row_word & cols_unset.bits[word_idx];
            if unset_word == 0 {
                continue;
            }

            if unset_word & (unset_word - 1) != 0 || unassigned_col.is_some() {
                return RowState::Unknown;
            }

            let bit = unset_word.trailing_zeros() as usize;
            let col = word_idx * 64 + bit;
            if col >= self.num_cols {
                break;
            }
            unassigned_col = Some(col);
        }

        match unassigned_col {
            Some(col) => RowState::Unit(col, parity),
            None if parity => RowState::Conflict,
            None => RowState::Satisfied,
        }
    }
}

/// State of a row after evaluation against current assignments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RowState {
    /// Two or more unassigned variables remain.
    Unknown,
    /// Exactly one unassigned variable (column, required_value).
    Unit(usize, bool),
    /// All variables assigned, parity matches.
    Satisfied,
    /// All variables assigned, parity mismatch (0 = 1).
    Conflict,
}
