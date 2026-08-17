// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Primitive model-reconstruction operations.

use crate::literal::{Literal, Variable};

pub(super) fn reconstruct_witness(model: &mut Vec<bool>, witness: &[Literal], clause: &[Literal]) {
    for &w in witness {
        let var_idx = w.variable().index();
        if var_idx >= model.len() {
            model.resize(var_idx + 1, false);
        }
    }

    let already_sat = clause.iter().any(|&lit| {
        let v = lit.variable().index();
        if v >= model.len() {
            false
        } else if lit.is_positive() {
            model[v]
        } else {
            !model[v]
        }
    });

    if already_sat {
        return;
    }

    // CaDiCaL-style conditional autarky: for each witness literal, if it is
    // currently false under the model, flip its variable assignment.
    for &w in witness {
        let var_idx = w.variable().index();
        let lit_satisfied = if w.is_positive() {
            model[var_idx]
        } else {
            !model[var_idx]
        };
        if !lit_satisfied {
            model[var_idx] = !model[var_idx];
        }
    }

    // Post-condition: clause must be satisfied after witness flipping.
    // Reference: CaDiCaL extend.cpp:200 has the same assertion.
    debug_assert!(
        clause.iter().any(|&lit| {
            let v = lit.variable().index();
            v < model.len() && (model[v] == lit.is_positive())
        }),
        "BUG: reconstruct_witness postcondition: clause={clause:?} witness={witness:?}"
    );
}

pub(super) fn reconstruct_sweep(model: &mut Vec<bool>, num_vars: usize, lit_map: &[Literal]) {
    if num_vars > model.len() {
        model.resize(num_vars, false);
    }

    for var_idx in 0..num_vars {
        let pos_lit = Literal::positive(Variable(var_idx as u32));
        let pos_idx = pos_lit.index();

        if pos_idx >= lit_map.len() {
            continue;
        }

        let mapped_lit = lit_map[pos_idx];
        let mapped_var_idx = mapped_lit.variable().index();

        if mapped_var_idx != var_idx && mapped_var_idx < model.len() {
            let mapped_value = model[mapped_var_idx];
            model[var_idx] = if mapped_lit.is_positive() {
                mapped_value
            } else {
                !mapped_value
            };
        }
    }
}
