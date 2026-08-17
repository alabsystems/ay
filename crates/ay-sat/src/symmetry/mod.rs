// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal, proof-free symmetry detection for root preprocessing.

pub(crate) mod detector;
pub(crate) mod hhw;
pub(crate) mod ir;
pub(crate) mod orbitope;
pub(crate) mod orbits;
pub(crate) mod refinement;
pub(crate) mod stats;

use std::collections::BTreeMap;

use crate::{Literal, Variable};

/// IR automorphism-search budgets, shared by the composite route
/// (`detector.rs`) and the signed route (`config_preprocess_symmetry.rs`).
///
/// B2 of the batteries-included migration: these were four `AY_SAT_IR_*` /
/// `AY_SAT_SIGNED_*` env overrides that nothing set, and the two node/generator
/// values were duplicated as bare literals at both call sites — a drift hazard
/// (the two routes could silently diverge). One source of truth now; the env
/// reads are deleted.
///
/// IR-tree node budget: keeps clique/colouring preprocessing well under a
/// couple of seconds.
pub(crate) const IR_NODE_BUDGET: u64 = 8_000;
/// Generator cap for one IR search.
pub(crate) const IR_MAX_GENERATORS: usize = 96;
/// Deterministic work ceiling for the whole IR search, in edge-visits. Sized so
/// detection stays in the tens of milliseconds on the instances it fires on.
pub(crate) const IR_WORK_BUDGET: u64 = 30_000_000;
/// Substantiality gate for the signed route: breaking pays only when the
/// symmetry is global. Measured: `ntil-90d-34` (1 generator) 30.5 s -> timeout;
/// `homer11.shuffled` (96 generators / 220 vars) 44.8 s -> 1.85 s.
pub(crate) const SIGNED_MIN_GENERATORS: usize = 2;
/// Minimum percent of variables the generators must move (see above).
pub(crate) const SIGNED_MIN_SUPPORT_PCT: usize = 10;

pub use stats::SymmetryReport;
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

/// DSR witness token stream certifying `clause` under the literal permutation
/// `perm`, in the same on-wire shape as
/// [`detector::sr_witness_tokens`](detector): the pivot repeated twice (the
/// second occurrence opens the PR part `pivot ↦ ⊤`, the third the substitution
/// part), then σ as literal↦literal pairs.
///
/// A signed automorphism is *already* a literal↦literal map, so it needs no
/// encoding gymnastics to become a DSR substitution — the sign flips ride along
/// in the literal tokens.
pub(crate) fn signed_sr_witness_tokens(
    clause: &[Literal],
    perm: &BTreeMap<Literal, Literal>,
) -> Vec<Literal> {
    let pivot = clause[0];
    let mut witness = vec![pivot, pivot];
    for (from, to) in perm {
        if from == to || from.variable() == pivot.variable() {
            continue;
        }
        witness.push(*from);
        witness.push(*to);
    }
    witness
}

/// Check that a LITERAL permutation maps the clause multiset onto itself.
///
/// Unlike [`detector::permutation_preserves_formula`], `perm` may flip signs, so
/// it can express the symmetries that survive competition-style polarity
/// shuffling. `perm` must be complement-closed (`perm[¬l] = ¬perm[l]`); the
/// caller builds it that way from a graph automorphism.
pub(crate) fn literal_permutation_preserves_formula(
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    perm: &BTreeMap<Literal, Literal>,
) -> bool {
    formula_counts.iter().all(|(clause, count)| {
        let mut image: Vec<u32> = clause
            .iter()
            .map(|&raw| {
                let lit = Literal::from_index(raw as usize);
                perm.get(&lit).copied().unwrap_or(lit).raw()
            })
            .collect();
        image.sort_unstable();
        formula_counts.get(&image) == Some(count)
    })
}

/// Build a multiset view of the current CNF snapshot.
pub(crate) fn build_formula_counts(clauses: &[Vec<Literal>]) -> BTreeMap<Vec<u32>, u32> {
    let mut counts = BTreeMap::new();
    for clause in clauses {
        *counts.entry(canonical_clause_key(clause)).or_insert(0) += 1;
    }
    counts
}

#[cfg(test)]
mod budget_tests {
    /// B2: the IR budgets have ONE source of truth. Before this batch the
    /// node/generator values were duplicated as bare literals at the composite
    /// and signed call sites (96 and 8_000, twice each), so the two routes
    /// could silently diverge. Both now name these constants — this test pins
    /// the values so any future fork of them is a reviewed change, not drift.
    #[test]
    fn symmetry_ir_budgets_have_a_single_source_of_truth() {
        assert_eq!(super::IR_NODE_BUDGET, 8_000);
        assert_eq!(super::IR_MAX_GENERATORS, 96);
        assert_eq!(super::IR_WORK_BUDGET, 30_000_000);
        assert_eq!(super::SIGNED_MIN_GENERATORS, 2);
        assert_eq!(super::SIGNED_MIN_SUPPORT_PCT, 10);
    }
}
