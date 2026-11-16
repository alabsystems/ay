// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::Variable;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmissionError};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

mod controls;

fn owner(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn literal(variable: u32, positive: bool) -> Literal {
    let positive_literal = Literal::positive(Variable::new(variable));
    if positive {
        positive_literal
    } else {
        positive_literal.negated()
    }
}

fn input() -> Vec<Vec<Literal>> {
    let a = literal(0, true);
    let b = literal(1, false);
    let c = literal(2, true);
    vec![vec![c, b, a, b, c], vec![a, a.negated(), a], Vec::new()]
}

fn prepare(clauses: &[Vec<Literal>], original: CountedAdmission) -> Result<CountedInitialCnf> {
    let rows: Vec<&[Literal]> = clauses.iter().map(Vec::as_slice).collect();
    CountedInitialCnf::try_new(3, &rows, original)
}

#[test]
fn exact_rows_namespace_empty_clause_and_tautology_are_preserved() {
    let clauses = input();
    let before = clauses.clone();
    let prepared = prepare(&clauses, owner(10000, 10000)).unwrap();
    assert_eq!(prepared.num_vars(), 3);
    assert_eq!(prepared.len(), 3);
    assert_ne!(prepared.len(), 0);
    for (index, expected) in clauses.iter().enumerate() {
        assert_eq!(
            prepared.clause(index).unwrap().unwrap().original(),
            expected
        );
    }
    assert_eq!(
        prepared.clause(0).unwrap().unwrap().normalized(),
        Some([literal(0, true), literal(1, false), literal(2, true),].as_slice())
    );
    assert!(prepared.clause(1).unwrap().unwrap().normalized().is_none());
    assert_eq!(
        prepared.clause(2).unwrap().unwrap().normalized(),
        Some([].as_slice())
    );
    assert!(prepared.clause(3).unwrap().is_none());
    prepared.dispose().unwrap();
    assert_eq!(clauses, before);
}

fn evaluates(clause: &[Literal], assignment: u32) -> bool {
    clause.iter().any(|literal| {
        let bit = assignment & (1 << literal.variable().index()) != 0;
        bit == literal.is_positive()
    })
}

#[test]
fn positive_and_negative_formulas_match_all_original_assignments() {
    let a = literal(0, true);
    let b = literal(1, true);
    for (clauses, satisfiable) in [
        (vec![], true),
        (vec![vec![]], false),
        (vec![vec![a, a]], true),
        (vec![vec![a, a.negated()]], true),
        (vec![vec![a], vec![a.negated()]], false),
        (vec![vec![a, b], vec![a.negated(), b]], true),
        (
            vec![
                vec![a, b],
                vec![a.negated(), b],
                vec![a, b.negated()],
                vec![a.negated(), b.negated()],
            ],
            false,
        ),
    ] {
        let prepared = prepare(&clauses, owner(10000, 10000)).unwrap();
        let mut any = false;
        for assignment in 0..8 {
            let expected = clauses.iter().all(|clause| evaluates(clause, assignment));
            let mut actual = true;
            for index in 0..prepared.len() {
                let row = prepared.clause(index).unwrap().unwrap();
                actual &= row
                    .normalized()
                    .is_none_or(|clause| evaluates(clause, assignment));
            }
            assert_eq!(actual, expected);
            any |= actual;
        }
        assert_eq!(any, satisfiable);
    }
}

#[test]
fn every_four_literal_clause_over_three_variables_preserves_truth() {
    for code in 0..6_usize.pow(4) {
        let mut digits = code;
        let mut clause = Vec::new();
        for _ in 0..4 {
            let digit = digits % 6;
            digits /= 6;
            clause.push(literal((digit / 2) as u32, digit % 2 == 0));
        }
        let prepared = prepare(&[clause.clone()], owner(10000, 10000)).unwrap();
        let row = prepared.clause(0).unwrap().unwrap();
        for assignment in 0..8 {
            assert_eq!(
                row.normalized().is_none_or(|c| evaluates(c, assignment)),
                evaluates(&clause, assignment)
            );
        }
    }
}

#[test]
fn exact_and_one_short_work_and_storage_do_not_renew_credit() {
    let clauses = input();
    let baseline = owner(10000, 10000);
    let prepared = prepare(&clauses, baseline.clone()).unwrap();
    let used = baseline.usage().unwrap();
    drop(prepared);
    assert!(used.work_admitted > 0 && used.storage_admitted > 0);
    for (work, storage, refusal) in [
        (used.work_admitted, used.storage_admitted, None),
        (
            used.work_admitted - 1,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let original = owner(work, storage);
        let result = prepare(&clauses, original.clone());
        assert_eq!(result.as_ref().err().copied(), refusal);
        if let Some(error) = refusal {
            assert_eq!(original.check(), Err(error));
            assert_eq!(prepare(&clauses, original.clone()).err(), Some(error));
        } else {
            let remaining = original.usage().unwrap();
            assert_eq!(remaining.work_remaining, 0);
            assert_eq!(remaining.storage_remaining, 0);
        }
    }
}

#[test]
fn clauses_larger_than_the_arena_limit_are_not_truncated_or_renumbered() {
    let length = u16::MAX as usize + 17;
    let clause: Vec<Literal> = (0..length).rev().map(|i| literal(i as u32, true)).collect();
    let original = owner(100_000_000, 100_000_000);
    let prepared = CountedInitialCnf::try_new(length, &[&clause], original).unwrap();
    let row = prepared.clause(0).unwrap().unwrap();
    assert_eq!(row.original(), clause);
    let normalized = row.normalized().unwrap();
    assert_eq!(normalized.len(), length);
    assert!(normalized
        .iter()
        .enumerate()
        .all(|(i, lit)| lit.variable().index() == i));
    assert_eq!(prepared.num_vars(), length);
}
