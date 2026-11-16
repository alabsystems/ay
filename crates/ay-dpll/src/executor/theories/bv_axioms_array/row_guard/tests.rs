// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::emit_row_clauses;

mod oracle;
mod storage;

fn collect(
    differences: &[i32],
    result: &[i32],
    value: &[i32],
    row2: Option<(i32, &[i32])>,
) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    emit_row_clauses(differences, result, value, row2, |clause| {
        clauses.push(clause)
    });
    clauses
}

fn literal(lit: i32, assignment: u32) -> bool {
    assert!(lit != 0 && lit.unsigned_abs() <= u32::BITS);
    let bit = assignment & (1 << (lit.unsigned_abs() - 1)) != 0;
    if lit > 0 {
        bit
    } else {
        !bit
    }
}

fn satisfied(clauses: &[Vec<i32>], assignment: u32) -> bool {
    clauses
        .iter()
        .all(|clause| clause.iter().any(|&lit| literal(lit, assignment)))
}

fn equal(left: &[i32], right: &[i32], assignment: u32) -> bool {
    left.iter()
        .zip(right)
        .all(|(&left, &right)| literal(left, assignment) == literal(right, assignment))
}

fn assert_all_assignments(
    differences: &[i32],
    result: &[i32],
    value: &[i32],
    row2: Option<(i32, &[i32])>,
    variables: u32,
) {
    let old = oracle::legacy(differences, result, value, row2);
    let new = collect(differences, result, value, row2);
    assert_eq!(old.len(), new.len());
    for assignment in 0..1 << variables {
        let differs = differences.iter().any(|&lit| literal(lit, assignment));
        let row1 = differs || equal(result, value, assignment);
        let expected = match row2 {
            Some((eq_idx, read)) => {
                literal(eq_idx, assignment) != differs
                    && row1
                    && (!differs || equal(result, read, assignment))
            }
            None => row1,
        };
        assert_eq!(
            satisfied(&old, assignment),
            expected,
            "legacy assignment {assignment}"
        );
        assert_eq!(
            satisfied(&new, assignment),
            expected,
            "shared assignment {assignment}"
        );
    }
}

#[test]
fn exact_truth_table_for_two_index_differences_and_two_value_bits() {
    assert_all_assignments(&[1, 2], &[3, 4], &[5, 6], Some((9, &[7, 8])), 9);
}

#[test]
fn signed_and_aliased_literals_preserve_exact_semantics() {
    assert_all_assignments(&[1, -2], &[3, -4], &[-3, 5], Some((6, &[4, -5])), 6);
    assert_all_assignments(&[-1, 2, -1], &[3, 3], &[4, -4], Some((6, &[5, 5])), 6);
}

#[test]
fn single_difference_bool_value_keeps_both_guard_polarities() {
    assert_all_assignments(&[1], &[2], &[3], Some((5, &[4])), 5);
}

#[test]
fn missing_base_read_retains_byte_exact_wide_row1() {
    for differences in [vec![1], vec![1, 2, 3], vec![-1, 2, -3]] {
        let result = [4, -5];
        let value = [-4, 6];
        assert_eq!(
            collect(&differences, &result, &value, None),
            oracle::legacy(&differences, &result, &value, None)
        );
        assert_all_assignments(&differences, &result, &value, None, 6);
    }
}

#[test]
fn empty_differences_retain_existing_no_emission_behavior() {
    assert_eq!(collect(&[], &[1], &[2], None), [] as [Vec<i32>; 0]);
    assert_eq!(
        collect(&[], &[1], &[2], Some((4, &[3]))),
        [] as [Vec<i32>; 0]
    );
}

#[test]
fn known_different_index_bit_leaves_only_base_value_equality() {
    // Literal 1 represents a known-true difference (e.g. a constant 0/1
    // index-bit pair). Other literals may still be symbolic or negated.
    let mut clauses = collect(&[1, -2], &[3, -4], &[1, -1], Some((5, &[-1, 1])));
    clauses.push(vec![1]);
    for assignment in 0..1 << 5 {
        let expected = literal(1, assignment)
            && !literal(5, assignment)
            && equal(&[3, -4], &[-1, 1], assignment);
        assert_eq!(satisfied(&clauses, assignment), expected);
    }
}

#[test]
fn all_false_differences_require_stored_value_not_base_value() {
    let mut clauses = collect(&[1, 2], &[3], &[4], Some((6, &[5])));
    clauses.extend([vec![-1], vec![-2]]);
    for assignment in 0..1 << 6 {
        let expected = !literal(1, assignment)
            && !literal(2, assignment)
            && literal(6, assignment)
            && equal(&[3], &[4], assignment);
        assert_eq!(satisfied(&clauses, assignment), expected);
    }
}

#[test]
fn original_definition_and_row2_clause_order_is_preserved() {
    let old = oracle::legacy(&[1, 2], &[3, 4], &[5, 6], Some((9, &[7, 8])));
    let new = collect(&[1, 2], &[3, 4], &[5, 6], Some((9, &[7, 8])));
    assert_eq!(
        &new[..4],
        &[
            vec![-9, -3, 5],
            vec![-9, 3, -5],
            vec![-9, -4, 6],
            vec![-9, 4, -6]
        ]
    );
    assert_eq!(&new[4..], &old[4..]);
}

#[test]
fn polarity_mutation_is_detected_by_satisfiable_neighbors() {
    let original = collect(&[1], &[2], &[3], Some((5, &[4])));
    let mut wrong = original.clone();
    wrong[0][0] = 5;
    assert!((0..1 << 5)
        .any(|assignment| { satisfied(&original, assignment) != satisfied(&wrong, assignment) }));
}
