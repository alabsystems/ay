// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::rational::Rational;
use crate::types::add_sparse_term;
use ay_core::assert_conflict_soundness;
use ay_core::term::{Symbol, TermData, TermStore};
use ay_core::{Sort, TheorySolver};

mod basics;
mod bound_interest;
mod decision_index;
mod deferred_reason_materialization;
mod delta_objective;
mod faithfulness_audit;
mod farkas_optimization;
mod incremental_bounds;
mod jit_propagation;
mod jit_snapshot_persistence;
mod model_snapshot;
mod optimality_certificate;
mod warm_simplex_state;

/// Helper: check() may return NeedModelEquality or NeedModelEqualities when
/// `discover_model_value_equalities()` fires. In unit tests without a DPLL(T)
/// driver, these are functionally equivalent to Sat.
fn is_sat_like(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Sat
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_)
    )
}

/// Verify that `unassigned_atom_count` is zero for each given term's variable.
/// After pop()+reset(), the count vector may be empty (#4919) — this is a known
/// optimization gap, not a correctness issue. When populated, all counts must be 0.
fn assert_unassigned_counts_zero(solver: &LraSolver, terms: &[TermId]) {
    if solver.unassigned_atom_count.is_empty() {
        return; // #4919: unassigned_atom_count not rebuilt after pop+reset
    }
    for &term in terms {
        let var = solver
            .term_to_var
            .get(&term)
            .copied()
            .unwrap_or_else(|| panic!("term {term:?} must be registered as a variable"));
        let vi = var as usize;
        assert!(
            vi < solver.unassigned_atom_count.len(),
            "var index {vi} out of bounds (len={})",
            solver.unassigned_atom_count.len()
        );
        assert_eq!(
            solver.unassigned_atom_count[vi], 0,
            "var {vi} should have 0 unassigned atoms after all asserted"
        );
    }
}

#[derive(Clone, Copy, Debug)]
enum CompoundDirtyResetKind {
    Pop,
    SoftReset,
}

fn assert_compound_source_keys_reseeded(reset_kind: CompoundDirtyResetKind) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    for source_var in [x_var, y_var] {
        assert!(
            solver.compound_use_index.contains_key(&source_var),
            "compound wakeups must be keyed by source var {source_var}"
        );
        assert!(
            !solver.atom_index.contains_key(&source_var),
            "compound source var {source_var} must stay out of atom_index so the reseed test exercises compound_use_index"
        );
    }

    match reset_kind {
        CompoundDirtyResetKind::Pop => {
            solver.push();
            solver.assert_literal(sum_le_3, true);
            solver.propagation_dirty_vars.clear();
            assert!(
                solver.propagation_dirty_vars.is_empty(),
                "test setup must clear dirty vars before pop() reseeding"
            );
            solver.pop();
        }
        CompoundDirtyResetKind::SoftReset => {
            solver.assert_literal(sum_le_3, true);
            solver.propagation_dirty_vars.clear();
            assert!(
                solver.propagation_dirty_vars.is_empty(),
                "test setup must clear dirty vars before soft_reset() reseeding"
            );
            solver.soft_reset();
        }
    }

    for source_var in [x_var, y_var] {
        assert!(
            solver.compound_use_index.contains_key(&source_var),
            "{reset_kind:?} must preserve compound wakeups for source var {source_var}"
        );
        assert!(
            solver.propagation_dirty_vars.contains(&source_var),
            "{reset_kind:?} must re-add compound source var {source_var} to propagation_dirty_vars"
        );
    }
}
