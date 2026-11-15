// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Primitive model-reconstruction operations.

use super::admitted::{ordinary, Ordinary, Work};
use crate::literal::{Literal, Variable};

pub(super) fn reconstruct_witness(model: &mut Vec<bool>, witness: &[Literal], clause: &[Literal]) {
    ordinary(reconstruct_witness_admitted(
        model, witness, clause, &Ordinary,
    ));
}

pub(super) fn reconstruct_witness_admitted<P: Work>(
    model: &mut Vec<bool>,
    witness: &[Literal],
    clause: &[Literal],
    policy: &P,
) -> Result<(), P::Error> {
    for &w in witness {
        policy.work(1)?;
        let var_idx = w.variable().index();
        if var_idx >= model.len() {
            policy.resize(model, var_idx + 1)?;
        }
    }

    if clause_satisfied_admitted(clause, model, policy)? {
        return Ok(());
    }

    // CaDiCaL-style conditional autarky: for each witness literal, if it is
    // currently false under the model, flip its variable assignment.
    for &w in witness {
        policy.work(1)?;
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

    // Reference: CaDiCaL extend.cpp:200. The ordinary diagnostic remains
    // debug-only; counted replay checks without formatting a panic payload.
    policy.witness_postcondition(model, witness, clause)
}

pub(super) fn reconstruct_sweep(model: &mut Vec<bool>, num_vars: usize, lit_map: &[Literal]) {
    ordinary(reconstruct_sweep_admitted(
        model, num_vars, lit_map, &Ordinary,
    ));
}

pub(super) fn reconstruct_sweep_admitted<P: Work>(
    model: &mut Vec<bool>,
    num_vars: usize,
    lit_map: &[Literal],
    policy: &P,
) -> Result<(), P::Error> {
    if num_vars > model.len() {
        policy.resize(model, num_vars)?;
    }

    for var_idx in 0..num_vars {
        policy.work(1)?;
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
    Ok(())
}

pub(crate) fn clause_satisfied_admitted<P: Work>(
    clause: &[Literal],
    model: &[bool],
    policy: &P,
) -> Result<bool, P::Error> {
    for lit in clause {
        policy.work(1)?;
        let var = lit.variable().index();
        if var < model.len() && model[var] == lit.is_positive() {
            return Ok(true);
        }
    }
    Ok(false)
}
