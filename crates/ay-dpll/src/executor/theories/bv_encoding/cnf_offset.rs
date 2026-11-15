// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Moving CNF clauses between variable spaces: the offset that places
//! bit-blasted variables past the Tseitin range, and adding clauses to a
//! persistent SAT solver.

use std::borrow::Borrow;

use ay_core::CnfClause;
use ay_sat::Solver as SatSolver;

/// Offset a DIMACS-style CNF literal by `var_offset`.
///
/// Positive literals are shifted up, negative literals are shifted down,
/// preserving sign semantics. Both BV solve paths use this to translate
/// bitblasted variables past the Tseitin range.
#[inline]
pub(in crate::executor::theories) fn offset_cnf_lit(lit: i32, var_offset: i32) -> i32 {
    if lit > 0 {
        lit + var_offset
    } else {
        lit - var_offset
    }
}

/// Offset all literals in `clauses` by `var_offset` and push into `all_clauses`.
pub(in crate::executor::theories) fn offset_and_push_clauses(
    clauses: impl IntoIterator<Item = CnfClause>,
    var_offset: i32,
    all_clauses: &mut Vec<CnfClause>,
) {
    for clause in clauses {
        let offset_lits: Vec<i32> = clause
            .literals()
            .iter()
            .map(|&lit| offset_cnf_lit(lit, var_offset))
            .collect();
        all_clauses.push(CnfClause::new(offset_lits));
    }
}

/// Add `clauses` to the persistent SAT solver without changing variable IDs.
pub(in crate::executor::theories) fn add_clauses_global<T>(
    solver: &mut SatSolver,
    clauses: impl IntoIterator<Item = T>,
) where
    T: Borrow<CnfClause>,
{
    for clause in clauses {
        let lits = clause
            .borrow()
            .literals()
            .iter()
            .map(|&lit| crate::cnf_lit_to_sat(lit))
            .collect();
        solver.add_clause_global(lits);
    }
}

/// Add `clauses` to the persistent SAT solver after offsetting each literal.
pub(in crate::executor::theories) fn add_offset_clauses_global<T>(
    solver: &mut SatSolver,
    clauses: impl IntoIterator<Item = T>,
    var_offset: i32,
) where
    T: Borrow<CnfClause>,
{
    for clause in clauses {
        let lits = clause
            .borrow()
            .literals()
            .iter()
            .map(|&lit| crate::cnf_lit_to_sat(offset_cnf_lit(lit, var_offset)))
            .collect();
        solver.add_clause_global(lits);
    }
}
