// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for model reconstruction.

use super::*;

#[kani::proof]
fn proof_witness_reconstruction_soundness() {
    let var_idx: usize = kani::any();
    kani::assume(var_idx < 10);
    let is_positive: bool = kani::any();
    let witness_lit = if is_positive {
        Literal::positive(Variable(var_idx as u32))
    } else {
        Literal::negative(Variable(var_idx as u32))
    };
    let clause = vec![witness_lit];
    let witness = [witness_lit];
    let mut model = vec![false; var_idx + 1];
    reconstruct_witness(&mut model, &witness, &clause);
    let lit_satisfied = if is_positive {
        model[var_idx]
    } else {
        !model[var_idx]
    };
    assert!(lit_satisfied, "Witness should be true after reconstruction");
}

#[kani::proof]
fn proof_sweep_identity_preserves_model() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars > 0 && num_vars < 5);
    let mut model: Vec<bool> = Vec::with_capacity(num_vars);
    for _ in 0..num_vars {
        model.push(kani::any());
    }
    let original_model = model.clone();
    let num_lits = num_vars * 2;
    let mut lit_map = Vec::with_capacity(num_lits);
    for i in 0..num_lits {
        lit_map.push(Literal(i as u32));
    }
    reconstruct_sweep(&mut model, num_vars, &lit_map);
    for i in 0..num_vars {
        assert_eq!(model[i], original_model[i], "Identity preserves model");
    }
}

#[kani::proof]
fn proof_stack_is_empty_consistent() {
    let mut stack = ReconstructionStack::new();
    assert!(stack.is_empty());
    assert_eq!(stack.len(), 0);
    stack.push_bce(
        Literal::positive(Variable(0)),
        vec![Literal::positive(Variable(0))],
    );
    assert!(!stack.is_empty());
    assert_eq!(stack.len(), 1);
    stack.clear();
    assert!(stack.is_empty());
    assert_eq!(stack.len(), 0);
}
