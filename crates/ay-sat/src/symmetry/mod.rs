// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal, proof-free symmetry detection for root preprocessing.

pub(crate) mod detector;
pub(crate) mod hhw;
pub(crate) mod ir;
pub(crate) mod orbits;
pub(crate) mod refinement;
pub(crate) mod stats;

use std::collections::BTreeMap;

use crate::{Literal, Variable};

pub(crate) use stats::{SymmetrySkipReason, SymmetryStats};

/// A direct variable transposition `lhs <-> rhs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BinarySwap {
    pub(crate) lhs: Variable,
    pub(crate) rhs: Variable,
}

impl BinarySwap {
    fn ordered(a: Variable, b: Variable) -> Self {
        if a <= b {
            Self { lhs: a, rhs: b }
        } else {
            Self { lhs: b, rhs: a }
        }
    }
}

/// Canonical sorted clause key in raw-literal space.
pub(crate) fn canonical_clause_key(clause: &[Literal]) -> Vec<u32> {
    let mut key: Vec<u32> = clause.iter().map(|lit| lit.raw()).collect();
    key.sort_unstable();
    key
}

/// Build a multiset view of the current CNF snapshot.
pub(crate) fn build_formula_counts(clauses: &[Vec<Literal>]) -> BTreeMap<Vec<u32>, u32> {
    let mut counts = BTreeMap::new();
    for clause in clauses {
        *counts.entry(canonical_clause_key(clause)).or_insert(0) += 1;
    }
    counts
}
