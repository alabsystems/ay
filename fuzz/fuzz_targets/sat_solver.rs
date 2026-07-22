// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT Solver Fuzz Target
//!
//! This fuzz target verifies the SAT solver doesn't panic on random CNF
//! formulas generated from structured input. Uses arbitrary crate to generate
//! valid CNF structures.

#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::fuzz_target;
use ay_sat::{Literal, Solver, Variable};

/// Convert DIMACS literal (1-indexed, signed) to ay Literal
fn dimacs_to_literal(lit: i32) -> Literal {
    // Variable is a newtype around u32 (0-indexed)
    let var_idx = (lit.abs() - 1) as u32;
    let var = Variable::new(var_idx);
    if lit > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

/// A fuzzable CNF formula with bounded size
#[derive(Debug, Clone)]
struct FuzzCnf {
    num_vars: u32,
    clauses: Vec<Vec<i32>>,
}

impl<'a> Arbitrary<'a> for FuzzCnf {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        // Limit variables to prevent excessive memory usage
        let num_vars: u32 = u.int_in_range(1..=100)?;

        // Limit clauses
        let num_clauses: usize = u.int_in_range(0..=200)?;

        let mut clauses = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses {
            // Clause length between 1 and 10
            let clause_len: usize = u.int_in_range(1..=10)?;
            let mut clause = Vec::with_capacity(clause_len);

            for _ in 0..clause_len {
                // Variable in range [1, num_vars]
                let var: i32 = u.int_in_range(1..=(num_vars as i32))?;
                // Sign: positive or negative
                let sign: bool = u.arbitrary()?;
                let lit = if sign { var } else { -var };
                clause.push(lit);
            }

            // Remove duplicates within clause
            clause.sort_by_key(|x| x.abs());
            clause.dedup_by_key(|x| x.abs());

            if !clause.is_empty() {
                clauses.push(clause);
            }
        }

        Ok(FuzzCnf { num_vars, clauses })
    }
}

fuzz_target!(|cnf: FuzzCnf| {
    // Create solver with the given number of variables
    let mut solver = Solver::new(cnf.num_vars as usize);

    // Add clauses - handle any errors gracefully
    for clause_lits in &cnf.clauses {
        let lits: Vec<Literal> = clause_lits
            .iter()
            .filter_map(|&lit| {
                let var = lit.abs() as u32;
                if var > 0 && var <= cnf.num_vars {
                    Some(dimacs_to_literal(lit))
                } else {
                    None
                }
            })
            .collect();

        if !lits.is_empty() {
            solver.add_clause(lits);
        }
    }

    // Solve - should not panic
    let result = solver.solve();

    // If SAT, verify the model (catches soundness bugs)
    if let Some(model) = result.model() {
        for clause_lits in &cnf.clauses {
            let mut satisfied = false;
            for &lit in clause_lits {
                let var = (lit.abs() - 1) as usize;
                if var < model.len() {
                    let value = model[var];
                    let positive = lit > 0;
                    if value == positive {
                        satisfied = true;
                        break;
                    }
                }
            }
            // If clause is non-empty and uses only valid vars, it must be satisfied
            let all_valid = clause_lits
                .iter()
                .all(|&l| (l.abs() as u32) <= cnf.num_vars);
            if all_valid && !clause_lits.is_empty() {
                assert!(
                    satisfied,
                    "SOUNDNESS BUG: Model doesn't satisfy clause {:?}",
                    clause_lits
                );
            }
        }
    }
});
