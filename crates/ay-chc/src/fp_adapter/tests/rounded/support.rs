// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn word(
    name: &str,
    width: u32,
    operands: &[u64],
    rm: RoundingMode,
    expected: u64,
    budget: &mut WorkBudget<'_>,
) {
    // SAME original test owner; this is fixture scratch, not a fresh case grant.
    budget.admit(8192, 65_536).unwrap();
    let mut terms = TermStore::new();
    let args = operands
        .iter()
        .map(|&bits| fp_constant(&mut terms, bits, width))
        .collect::<Vec<_>>();
    let actual = operation(&mut terms, name, width, rm, &args);
    let expected = fp_constant(&mut terms, expected, width);
    let correct = predicate(&mut terms, "=", &[actual, expected]);
    let wrong = terms.mk_not_raw(correct);
    // The unchanged paid UP + native SAT harness checks the WHOLE exact
    // structural result and negation, excluding EVERY other SMT FP value.
    roots(&terms, &[correct, wrong], &[true, false], budget);
    drop(terms);
    budget.charge(0).unwrap();
}

pub(super) fn nan(name: &str, width: u32, operands: &[u64], budget: &mut WorkBudget<'_>) {
    budget.admit(8192, 65_536).unwrap();
    let mut terms = TermStore::new();
    let args = operands
        .iter()
        .map(|&bits| fp_constant(&mut terms, bits, width))
        .collect::<Vec<_>>();
    let actual = operation(&mut terms, name, width, RoundingMode::RNE, &args);
    let classify = predicate(&mut terms, "fp.isNaN", &[actual]);
    let ieee_equal = predicate(&mut terms, "fp.eq", &[actual, actual]);
    roots(&terms, &[classify, ieee_equal], &[true, false], budget);
    drop(terms);
    budget.charge(0).unwrap();
}

pub(super) fn simple(name: &str) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let one = fp_constant(&mut terms, 0x3f800000, 32);
    let actual = if name == "fp.sqrt" {
        operation(&mut terms, name, 32, RoundingMode::RNE, &[one])
    } else {
        operation(&mut terms, name, 32, RoundingMode::RNE, &[one, one, one])
    };
    let root = predicate(&mut terms, "fp.isNormal", &[actual]);
    (terms, root)
}

pub(super) fn free(name: &str) -> (TermStore, TermId, [TermId; 3], [ChcVar; 3]) {
    let mut terms = TermStore::new();
    let sources = ["native_round_x", "native_round_y", "native_round_z"]
        .map(|n| terms.mk_var(n, Sort::FloatingPoint(11, 53)));
    let operands = if name == "fp.sqrt" {
        &sources[..1]
    } else {
        &sources[..]
    };
    let actual = operation(&mut terms, name, 64, RoundingMode::RNE, operands);
    let root = predicate(&mut terms, "fp.isNormal", &[actual]);
    let targets = ["native_round_x", "native_round_y", "native_round_z"]
        .map(|n| ChcVar::new(n, crate::ChcSort::BitVec(64)));
    (terms, root, sources, targets)
}
