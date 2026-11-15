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
    ///
    /// `clause_capacity` is a hint: when the reservation cannot be made the
    /// clause list starts empty and grows as clauses are added.
    pub fn new_with_capacity(num_vars: u32, clause_capacity: usize) -> Self {
        let mut clauses = Vec::new();
        // A failed reservation only forgoes the pre-sizing.
        let _ = clauses.try_reserve_exact(clause_capacity);
        Self { num_vars, clauses }
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
                let v = lit.variable().index().checked_add(1).ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "variable index has no 1-based DIMACS name",
                    )
                })?;
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
        let mut lits: Vec<Literal> = Vec::new();
        // A failed reservation only forgoes the pre-sizing.
        let _ = lits.try_reserve_exact(dimacs_lits.len());
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

/// Number of clauses `add_xor_equals_clauses` emits for `num_vars` variables:
/// `2^(num_vars - 1)`, saturating at `usize::MAX` once that count no longer
/// fits (callers use it only as a capacity estimate).
pub(crate) fn xor_clause_count(num_vars: usize, parity: bool) -> usize {
    let Some(exponent) = num_vars.checked_sub(1) else {
        return usize::from(parity);
    };
    u32::try_from(exponent)
        .ok()
        .and_then(|exponent| 1usize.checked_shl(exponent))
        .unwrap_or(usize::MAX)
}

pub(crate) fn add_xor_equals_clauses(vars: &[Var], parity: bool, cnf: &mut Cnf) {
    if vars.is_empty() {
        if parity {
            cnf.add_clause(&[]); // UNSAT
        }
        return;
    }

    // Enumerate every assignment in counting order (variable 0 is the least
    // significant digit) with an odometer, so no fixed-width mask limits the
    // number of variables. `clause` holds the clause forbidding the current
    // assignment: a variable assigned true appears negated.
    let mut clause: Vec<Lit> = Vec::new();
    // A failed reservation only forgoes the pre-sizing.
    let _ = clause.try_reserve_exact(vars.len());
    for &var in vars {
        clause.push(Lit::positive(var));
    }
    let mut assignment_is_odd = false;
    loop {
        if assignment_is_odd != parity {
            // This assignment should be forbidden
            // Clause: at least one literal must be flipped
            cnf.add_clause(&clause);
        }
        // Advance to the next assignment: clear trailing true digits, then
        // set the first false one. Every digit true means all were visited.
        let mut advanced = false;
        for (lit, &var) in clause.iter_mut().zip(vars) {
            assignment_is_odd = !assignment_is_odd;
            if lit.is_positive() {
                *lit = Lit::negative(var);
                advanced = true;
                break;
            }
            *lit = Lit::positive(var);
        }
        if !advanced {
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type TestResult = Result<(), Box<dyn std::error::Error>>;

    #[test]
    fn xor_clause_count_saturates_past_the_word_width() -> TestResult {
        let cases = [
            (0, false, 0),
            (0, true, 1),
            (1, true, 1),
            (3, false, 4),
            (64, true, 1usize << 63),
            (65, true, usize::MAX),
            (usize::MAX, false, usize::MAX),
        ];
        for (num_vars, parity, expected) in cases {
            let got = xor_clause_count(num_vars, parity);
            if got != expected {
                return Err(format!("xor_clause_count({num_vars}, {parity}) = {got}").into());
            }
        }
        Ok(())
    }

    /// The clauses the fixed-width mask enumeration produced, in its order.
    fn mask_reference(vars: &[Var], parity: bool) -> Result<Vec<Vec<Lit>>, String> {
        let width = u32::try_from(vars.len()).map_err(|e| e.to_string())?;
        let end = 1u64
            .checked_shl(width)
            .ok_or("reference needs fewer vars")?;
        let mut clauses = Vec::new();
        for mask in 0..end {
            if (mask.count_ones() % 2 == 1) == parity {
                continue;
            }
            let mut clause = Vec::new();
            for (idx, &var) in vars.iter().enumerate() {
                let bit = u32::try_from(idx).map_err(|e| e.to_string())?;
                let set = mask.checked_shr(bit).ok_or("shift in range")? & 1 == 1;
                clause.push(if set {
                    Lit::negative(var)
                } else {
                    Lit::positive(var)
                });
            }
            clauses.push(clause);
        }
        Ok(clauses)
    }

    #[test]
    fn xor_clauses_match_the_mask_enumeration_in_order() -> TestResult {
        let mut vars: Vec<Var> = Vec::new();
        for width in 1..=6u32 {
            // Sparse, non-zero-based variable ids.
            vars.push(Var::new(width.saturating_mul(3)));
            for parity in [false, true] {
                let mut cnf = Cnf::new_with_capacity(32, 0);
                add_xor_equals_clauses(&vars, parity, &mut cnf);
                let got: Vec<Vec<Lit>> = cnf.clauses().cloned().collect();
                let expected = mask_reference(&vars, parity)?;
                if got != expected {
                    return Err(format!("width {width}, parity {parity}: {got:?}").into());
                }
                let count = xor_clause_count(vars.len(), parity);
                if got.len() != count {
                    return Err(
                        format!("width {width}: {} clauses, count {count}", got.len()).into(),
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn empty_xor_is_unsat_only_for_odd_parity() -> TestResult {
        for parity in [false, true] {
            let mut cnf = Cnf::new_with_capacity(0, 0);
            add_xor_equals_clauses(&[], parity, &mut cnf);
            if cnf.num_clauses() != usize::from(parity) {
                return Err(format!("parity {parity}: {} clauses", cnf.num_clauses()).into());
            }
        }
        Ok(())
    }
}
