// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::gates::GateExtractor;
use crate::ProofOutput;

use super::add_duplicate_and_gate_formula;

mod elimination;
mod fastelim_census;
mod preprocess;
mod resolvents;
mod scheduling;

fn add_uniform_3sat_clauses(solver: &mut Solver, num_vars: u32, num_clauses: usize) {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(3);
        let mut vars = [u32::MAX; 3];
        while clause.len() < 3 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let var = (state % u64::from(num_vars)) as u32;
            if vars.contains(&var) {
                continue;
            }
            vars[clause.len()] = var;
            state ^= state.rotate_left(17);
            let lit = if state & 1 == 0 {
                Literal::positive(Variable(var))
            } else {
                Literal::negative(Variable(var))
            };
            clause.push(lit);
        }
        solver.add_clause(clause);
    }
}
