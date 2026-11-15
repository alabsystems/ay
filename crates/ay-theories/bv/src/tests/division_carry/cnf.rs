// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::collections::VecDeque;

/// A literal-occurrence unit propagator, independent of BvSolver's gate tables.
/// With concrete inputs, every output must be forced, not merely satisfiable.
pub(super) struct Circuit<'a> {
    clauses: &'a [CnfClause],
    occurrences: Vec<Vec<(usize, CnfLit)>>,
    remaining: Vec<usize>,
    unresolved: Vec<CnfLit>,
    units: Vec<CnfLit>,
}

impl<'a> Circuit<'a> {
    pub(super) fn new(solver: &'a BvSolver<'_>) -> Self {
        Self::from_clauses(solver.num_vars(), solver.clauses())
    }

    pub(super) fn from_clauses(num_vars: u32, clauses: &'a [CnfClause]) -> Self {
        let mut occurrences = vec![Vec::new(); num_vars as usize + 1];
        let mut remaining = Vec::new();
        let mut unresolved = Vec::new();
        let mut units = Vec::new();
        for (index, clause) in clauses.iter().enumerate() {
            let lits = clause.literals();
            assert!(
                !lits.is_empty(),
                "division circuit contains an empty clause"
            );
            remaining.push(lits.len());
            unresolved.push(lits.iter().fold(0, |all, &lit| all ^ lit));
            if lits.len() == 1 {
                units.push(lits[0]);
            }
            for &lit in lits {
                assert_ne!(lit, 0);
                occurrences[lit.unsigned_abs() as usize].push((index, lit));
            }
        }
        Self {
            clauses,
            occurrences,
            remaining,
            unresolved,
            units,
        }
    }

    pub(super) fn propagate(&self, fixes: &[CnfLit]) -> Vec<Option<bool>> {
        let mut values = vec![None; self.occurrences.len()];
        let mut remaining = self.remaining.clone();
        let mut unresolved = self.unresolved.clone();
        let mut satisfied = vec![false; self.clauses.len()];
        let mut queue: VecDeque<_> = self.units.iter().chain(fixes).copied().collect();
        while let Some(lit) = queue.pop_front() {
            let variable = lit.unsigned_abs() as usize;
            let value = lit > 0;
            if let Some(old) = values[variable] {
                assert_eq!(old, value, "contradictory unit propagation for {lit}");
                continue;
            }
            values[variable] = Some(value);
            for &(clause, occurrence) in &self.occurrences[variable] {
                remaining[clause] -= 1;
                unresolved[clause] ^= occurrence;
                satisfied[clause] |= (occurrence > 0) == value;
                if !satisfied[clause] {
                    assert_ne!(remaining[clause], 0, "falsified clause {clause}");
                    if remaining[clause] == 1 {
                        queue.push_back(unresolved[clause]);
                    }
                }
            }
        }
        for clause in self.clauses {
            assert!(
                clause
                    .literals()
                    .iter()
                    .any(|&lit| { values[lit.unsigned_abs() as usize] == Some(lit > 0) }),
                "concrete input must satisfy every emitted clause"
            );
        }
        values
    }
}

pub(super) fn bit_value(model: &[Option<bool>], lit: CnfLit) -> bool {
    model[lit.unsigned_abs() as usize].expect("output must be forced by input units") == (lit > 0)
}

pub(super) fn word_value(model: &[Option<bool>], bits: &[CnfLit]) -> u64 {
    assert!(bits.len() <= 64);
    bits.iter().enumerate().fold(0, |word, (index, &lit)| {
        word | (u64::from(bit_value(model, lit)) << index)
    })
}
