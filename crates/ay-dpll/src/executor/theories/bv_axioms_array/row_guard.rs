// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reuse ROW2's exact index-equality summary in ROW1's value clauses.
//!
//! The caller has already emitted `diff_k <=> (i_k XOR j_k)` and checked
//! widths/available bits. When ROW2 is admitted, its existing fresh `eq_idx`
//! satisfies `eq_idx <=> !OR(diff)`. Therefore ROW1 can use `!eq_idx` rather
//! than repeating every difference literal. The defining clauses are kept in
//! their original position: ROW1, summary definition, ROW2. A forward reference
//! changes neither the meaning of the CNF conjunction nor its variable scope.
//! No new variable or clause is introduced. Without ROW2 the old wide ROW1 is
//! emitted exactly, including ordering. Empty differences are handled by the
//! caller's unconditional ROW1 path and remain outside this helper's admission.

/// Emit the value constraints after the caller's unchanged index-bit guards.
///
/// `result` and `value` have identical widths. `row2`, when present, contains
/// the already-reserved fresh summary variable and a same-width base read.
/// Inputs are final signed CNF literals; aliases and negative literals are
/// preserved without simplification. Storage is one clause at a time, not an
/// additional retained CNF batch.
pub(super) fn emit_row_clauses(
    differences: &[i32],
    result: &[i32],
    value: &[i32],
    row2: Option<(i32, &[i32])>,
    mut emit: impl FnMut(Vec<i32>),
) {
    if differences.is_empty() {
        return;
    }
    if let Some((eq_idx, _)) = row2 {
        for (&result_bit, &value_bit) in result.iter().zip(value) {
            emit(vec![-eq_idx, -result_bit, value_bit]);
            emit(vec![-eq_idx, result_bit, -value_bit]);
        }
    } else {
        let suffix = differences.len();
        let mut clause = Vec::with_capacity(suffix + 2);
        clause.extend_from_slice(differences);
        clause.extend_from_slice(&[0, 0]);
        for (&result_bit, &value_bit) in result.iter().zip(value) {
            clause[suffix] = -result_bit;
            clause[suffix + 1] = value_bit;
            emit(clause.clone());
            clause[suffix] = result_bit;
            clause[suffix + 1] = -value_bit;
            emit(clause.clone());
        }
    }
    if let Some((eq_idx, read)) = row2 {
        for &difference in differences {
            emit(vec![-eq_idx, -difference]);
        }
        let mut definition = differences.to_vec();
        definition.push(eq_idx);
        emit(definition);
        for (&result_bit, &read_bit) in result.iter().zip(read) {
            emit(vec![eq_idx, -result_bit, read_bit]);
            emit(vec![eq_idx, result_bit, -read_bit]);
        }
    }
}

#[cfg(test)]
mod tests;
