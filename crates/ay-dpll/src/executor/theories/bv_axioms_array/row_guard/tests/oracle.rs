// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

/// Frozen pre-sharing ROW1/definition/ROW2 shape, with XOR guards supplied by
/// the caller as before. This is deliberately independent of the production
/// emitter and preserves its original clause/literal order.
pub(super) fn legacy(
    differences: &[i32],
    result: &[i32],
    value: &[i32],
    row2: Option<(i32, &[i32])>,
) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    if differences.is_empty() {
        return clauses;
    }
    let suffix = differences.len();
    let mut clause = Vec::with_capacity(suffix + 2);
    clause.extend_from_slice(differences);
    clause.push(0);
    clause.push(0);
    for (&result_bit, &value_bit) in result.iter().zip(value) {
        clause[suffix] = -result_bit;
        clause[suffix + 1] = value_bit;
        clauses.push(clause.clone());
        clause[suffix] = result_bit;
        clause[suffix + 1] = -value_bit;
        clauses.push(clause.clone());
    }
    if let Some((eq_idx, read)) = row2 {
        for &difference in differences {
            clauses.push(vec![-eq_idx, -difference]);
        }
        let mut definition = differences.to_vec();
        definition.push(eq_idx);
        clauses.push(definition);
        for (&result_bit, &read_bit) in result.iter().zip(read) {
            clauses.push(vec![eq_idx, -result_bit, read_bit]);
            clauses.push(vec![eq_idx, result_bit, -read_bit]);
        }
    }
    clauses
}
