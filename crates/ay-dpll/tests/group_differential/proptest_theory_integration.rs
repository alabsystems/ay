// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Property-based tests for DPLL(T) theory integration (Gap 9).
//!
//! These tests generate small random theory formulas (EUF, LRA, LIA, arrays, and
//! combined variants) and cross-check AY's DPLL(T) result against lightweight
//! oracles.

use ay_core::term::Symbol;
use ay_core::{Sort, TermId, TermStore, TheoryResult, TheorySolver, Tseitin};
use ay_dpll::DpllT;
use ay_euf::EufSolver;
use ay_lia::LiaSolver;
use ay_lra::LraSolver;
use ay_sat::SatResult;
use ntest::timeout;
use proptest::prelude::*;

#[derive(Clone, Debug)]
pub(crate) enum BoolExpr {
    Atom(usize),
    Not(Box<Self>),
    And(Vec<Self>),
    Or(Vec<Self>),
}

impl BoolExpr {
    fn eval(&self, assignment: &[bool]) -> bool {
        match self {
            Self::Atom(i) => assignment[*i],
            Self::Not(e) => !e.eval(assignment),
            Self::And(es) => es.iter().all(|e| e.eval(assignment)),
            Self::Or(es) => es.iter().any(|e| e.eval(assignment)),
        }
    }

    fn mark_used(&self, used: &mut [bool]) {
        match self {
            Self::Atom(i) => used[*i] = true,
            Self::Not(e) => e.mark_used(used),
            Self::And(es) | Self::Or(es) => {
                for e in es {
                    e.mark_used(used);
                }
            }
        }
    }

    fn used_atoms(&self, num_atoms: usize) -> Vec<usize> {
        let mut used = vec![false; num_atoms];
        self.mark_used(&mut used);
        used.iter()
            .enumerate()
            .filter_map(|(i, b)| b.then_some(i))
            .collect()
    }
}

pub(crate) fn bool_expr_strategy(num_atoms: usize) -> impl Strategy<Value = BoolExpr> {
    let leaf = (0usize..num_atoms).prop_map(BoolExpr::Atom);
    leaf.prop_recursive(4, 64, 8, move |inner| {
        prop_oneof![
            inner.clone().prop_map(|e| BoolExpr::Not(Box::new(e))),
            prop::collection::vec(inner.clone(), 2..=3).prop_map(BoolExpr::And),
            prop::collection::vec(inner, 2..=3).prop_map(BoolExpr::Or),
        ]
    })
}

pub(crate) fn build_bool_term(terms: &mut TermStore, atoms: &[TermId], expr: &BoolExpr) -> TermId {
    match expr {
        BoolExpr::Atom(i) => atoms[*i],
        BoolExpr::Not(e) => {
            let inner = build_bool_term(terms, atoms, e);
            terms.mk_not(inner)
        }
        BoolExpr::And(es) => {
            let args = es
                .iter()
                .map(|e| build_bool_term(terms, atoms, e))
                .collect::<Vec<_>>();
            terms.mk_and(args)
        }
        BoolExpr::Or(es) => {
            let args = es
                .iter()
                .map(|e| build_bool_term(terms, atoms, e))
                .collect::<Vec<_>>();
            terms.mk_or(args)
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Expected {
    Sat,
    Unsat,
}

pub(crate) fn brute_force_expected<T: TheorySolver>(
    make_theory: impl Fn() -> T,
    atoms: &[TermId],
    expr: &BoolExpr,
) -> Expected {
    let used = expr.used_atoms(atoms.len());
    let num_used = used.len();
    debug_assert!(num_used > 0);
    debug_assert!(num_used <= 20, "brute force bound");

    for mask in 0u64..(1u64 << num_used) {
        let mut assignment = vec![false; atoms.len()];
        for (bit, &atom_idx) in used.iter().enumerate() {
            assignment[atom_idx] = ((mask >> bit) & 1) == 1;
        }

        if !expr.eval(&assignment) {
            continue;
        }

        // Check for contradictory assignments to atoms with the same TermId.
        // Due to hash-consing, different atom indices may map to the same TermId.
        // If a=true and b=false but atoms[a] == atoms[b], that's a Boolean conflict.
        let mut term_to_value: std::collections::HashMap<TermId, bool> =
            std::collections::HashMap::new();
        let mut has_conflict = false;
        for &atom_idx in &used {
            let term_id = atoms[atom_idx];
            let value = assignment[atom_idx];
            if let Some(&prev_value) = term_to_value.get(&term_id) {
                if prev_value != value {
                    has_conflict = true;
                    break;
                }
            } else {
                term_to_value.insert(term_id, value);
            }
        }
        if has_conflict {
            continue;
        }

        let mut theory = make_theory();
        for &atom_idx in &used {
            theory.assert_literal(atoms[atom_idx], assignment[atom_idx]);
        }
        match theory.check() {
            TheoryResult::Sat => return Expected::Sat,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => continue,
            TheoryResult::Unknown
            | TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedStringLemma(_)
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_)
            | TheoryResult::NeedLemmas(_) => {
                // Conservative: treat as possibly SAT to avoid false soundness alarms
                return Expected::Sat;
            }
            // Wildcard covers future variants from #[non_exhaustive].
            _ => return Expected::Sat,
        }
    }

    Expected::Unsat
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum LraCmp {
    Le,
    Ge,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct LraAtomSpec {
    cmp: LraCmp,
    bound: i8,
}

pub(crate) fn lra_atom_spec_strategy() -> impl Strategy<Value = LraAtomSpec> {
    (prop_oneof![Just(LraCmp::Le), Just(LraCmp::Ge)], -5i8..=5i8)
        .prop_map(|(cmp, bound)| LraAtomSpec { cmp, bound })
}

mod euf_lra_lia {
    use super::*;
    include!("proptest_theory_integration/euf_lra_lia.rs");
}

mod lia {
    use super::*;
    include!("proptest_theory_integration/lia.rs");
}

mod arrays_euf {
    use super::*;
    include!("proptest_theory_integration/arrays_euf.rs");
}

mod uflia_nelson_oppen {
    use super::*;
    include!("proptest_theory_integration/uflia_nelson_oppen.rs");
}

mod uflia_congruence {
    use super::*;
    include!("proptest_theory_integration/uflia_congruence.rs");
}

mod transitive {
    use super::*;
    include!("proptest_theory_integration/transitive.rs");
}

mod nia {
    use super::*;
    include!("proptest_theory_integration/nia.rs");
}
