// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF formula representation and XOR encoding utilities.

use ay_sat::Literal;

use crate::{Lit, Var};

/// A CNF formula represented as a list of clauses.
#[derive(Debug, Clone)]
pub struct Cnf {
    /// Number of variables
    num_vars: u32,
    /// Clauses (each clause is a list of literals)
    clauses: Vec<Vec<Literal>>,
}

impl Cnf {
    /// Create a new CNF with reserved capacity.
    pub fn new_with_capacity(num_vars: u32, clause_capacity: usize) -> Self {
        Self {
            num_vars,
            clauses: Vec::with_capacity(clause_capacity),
        }
    }

    /// Add a clause to the formula.
    pub fn add_clause(&mut self, literals: &[Literal]) {
        self.clauses.push(literals.to_vec());
    }

    /// Number of variables.
    pub fn num_vars(&self) -> usize {
        self.num_vars as usize
    }

    /// Number of clauses.
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Iterate over clauses.
    pub fn clauses(&self) -> impl Iterator<Item = &Vec<Literal>> {
        self.clauses.iter()
    }

    /// Write the CNF to a writer in standard DIMACS format:
    /// `p cnf <num_vars> <num_clauses>` header, then one clause per line
    /// (space-separated `±var` terms terminated by `0`).
    pub fn to_dimacs<W: std::io::Write>(&self, mut w: W) -> std::io::Result<()> {
        writeln!(w, "p cnf {} {}", self.num_vars, self.clauses.len())?;
        for clause in &self.clauses {
            for lit in clause {
                let v = lit.variable().index() as i64 + 1;
                if lit.is_positive() {
                    write!(w, "{v} ")?;
                } else {
                    write!(w, "-{v} ")?;
                }
            }
            writeln!(w, "0")?;
        }
        Ok(())
    }

    /// Parse a single DIMACS-style clause (signed 1-based ints, no trailing
    /// zero expected) and append it to this formula. Positive ints encode
    /// the positive literal of var `|x|-1`; negative ints encode the
    /// negation. A zero in `dimacs_lits` is skipped so callers that
    /// include the standard trailing `0` still work. Variables referenced
    /// beyond the CNF's declared `num_vars` still succeed — the caller is
    /// responsible for sizing `num_vars` appropriately.
    pub fn add_clause_from_dimacs(&mut self, dimacs_lits: &[i32]) {
        let mut lits: Vec<Literal> = Vec::with_capacity(dimacs_lits.len());
        for &x in dimacs_lits {
            if x == 0 {
                continue;
            }
            let var = ay_sat::Variable::new(x.unsigned_abs().saturating_sub(1));
            let lit = if x > 0 {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            lits.push(lit);
        }
        self.clauses.push(lits);
    }

    /// Convert to a solver with adaptive inprocessing gating.
    ///
    /// Extracts syntactic features from the clause database and applies
    /// instance-driven adjustments to the inprocessing profile before
    /// returning the solver. This matches the adaptive gating applied
    /// by the DIMACS entry point in `ay-sat`.
    pub fn into_solver(self) -> ay_sat::Solver {
        let features = ay_sat::SatFeatures::extract(self.num_vars as usize, &self.clauses);
        let class = ay_sat::InstanceClass::classify(&features);

        let mut solver = ay_sat::Solver::new(self.num_vars as usize);

        // Apply adaptive inprocessing adjustments via unified profile (#8149).
        let mut profile = solver.inprocessing_feature_profile();
        if ay_sat::adjust_features_for_instance(&features, &class, &mut profile) {
            solver.apply_feature_profile(&profile);
        }

        for clause in self.clauses {
            solver.add_clause(clause);
        }
        solver
    }
}

pub(crate) fn xor_clause_count(num_vars: usize, parity: bool) -> usize {
    if num_vars == 0 {
        usize::from(parity)
    } else {
        1usize << (num_vars - 1)
    }
}

pub(crate) fn add_xor_equals_clauses(vars: &[Var], parity: bool, cnf: &mut Cnf) {
    if vars.is_empty() {
        if parity {
            cnf.add_clause(&[]); // UNSAT
        }
        return;
    }

    let num_vars = vars.len();
    for mask in 0..(1u64 << num_vars) {
        let assignment_is_odd = mask.count_ones() % 2 == 1;
        if assignment_is_odd != parity {
            // This assignment should be forbidden
            // Clause: at least one literal must be flipped
            let clause: Vec<Lit> = vars
                .iter()
                .enumerate()
                .map(|(idx, &var)| {
                    if (mask >> idx) & 1 == 1 {
                        Lit::negative(var)
                    } else {
                        Lit::positive(var)
                    }
                })
                .collect();
            cnf.add_clause(&clause);
        }
    }
}
