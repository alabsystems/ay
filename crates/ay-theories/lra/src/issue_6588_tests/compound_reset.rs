// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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
    let slack = *solver
        .atom_index
        .keys()
        .next()
        .expect("compound atom must register a slack-keyed atom_index entry");
    assert_ne!(
        slack, x_var,
        "compound atom slack must differ from direct source vars"
    );
    assert_ne!(
        slack, y_var,
        "compound atom slack must differ from direct source vars"
    );
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
    assert!(
        solver.compound_use_index.contains_key(&slack),
        "compound wakeups must also be keyed by the shared slack var {slack}"
    );

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
    assert!(
        solver.propagation_dirty_vars.contains(&slack),
        "{reset_kind:?} must also re-add the shared slack var {slack} to propagation_dirty_vars"
    );
}

#[test]
fn test_pop_reseeds_compound_source_dirty_vars_6588() {
    assert_compound_source_keys_reseeded(CompoundDirtyResetKind::Pop);
}

#[test]
fn test_soft_reset_reseeds_compound_source_dirty_vars_6588() {
    assert_compound_source_keys_reseeded(CompoundDirtyResetKind::SoftReset);
}
