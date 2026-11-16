// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn bv64_indices_and_byte_values_remove_1008_literal_copies_per_read() {
    let differences: Vec<_> = (1..=64).collect();
    let result: Vec<_> = (65..=72).collect();
    let value: Vec<_> = (73..=80).collect();
    let read: Vec<_> = (81..=88).collect();
    let old = oracle::legacy(&differences, &result, &value, Some((89, &read)));
    let new = collect(&differences, &result, &value, Some((89, &read)));
    let old_literals: usize = old.iter().map(Vec::len).sum();
    let new_literals: usize = new.iter().map(Vec::len).sum();
    assert_eq!(old.len(), 97);
    assert_eq!(new.len(), old.len());
    assert_eq!(old_literals, 1297);
    assert_eq!(new_literals, 289);
    assert_eq!((old_literals - new_literals) * size_of::<i32>(), 4032);
    assert_eq!(new.iter().flatten().map(|lit| lit.abs()).max(), Some(89));
    assert_eq!(new[..16].iter().map(Vec::len).sum::<usize>(), 48);
    assert_eq!(&new[16..], &old[16..]);
    // The unchanged 4*64 three-literal XOR clauses are outside this helper.
    assert_eq!(old_literals + 4 * 64 * 3, 2065);
    assert_eq!(new_literals + 4 * 64 * 3, 1057);
}

#[test]
fn unavailable_base_keeps_exact_original_literal_and_variable_inventory() {
    let differences: Vec<_> = (1..=64).collect();
    let result: Vec<_> = (65..=72).collect();
    let value: Vec<_> = (73..=80).collect();
    let old = oracle::legacy(&differences, &result, &value, None);
    let new = collect(&differences, &result, &value, None);
    assert_eq!(new, old);
    assert_eq!(new.len(), 16);
    assert_eq!(new.iter().map(Vec::len).sum::<usize>(), 1056);
    assert_eq!(new.iter().flatten().map(|lit| lit.abs()).max(), Some(80));
}

#[test]
fn wide_guard_emits_linear_literal_storage_without_retaining_an_extra_batch() {
    let differences: Vec<_> = (1..=4096).collect();
    let result: Vec<_> = (4097..=4352).collect();
    let value: Vec<_> = (4353..=4608).collect();
    let read: Vec<_> = (4609..=4864).collect();
    let mut clauses = 0;
    let mut literals = 0;
    let mut widest = 0;
    emit_row_clauses(
        &differences,
        &result,
        &value,
        Some((4865, &read)),
        |clause| {
            if clauses < 2 * result.len() {
                assert_eq!(clause.len(), 3, "ROW1 must not copy the wide guard");
            }
            clauses += 1;
            literals += clause.len();
            widest = widest.max(clause.len());
        },
    );
    assert_eq!(clauses, 4 * result.len() + differences.len() + 1);
    assert_eq!(literals, 12 * result.len() + 3 * differences.len() + 1);
    assert_eq!(widest, differences.len() + 1);
}
