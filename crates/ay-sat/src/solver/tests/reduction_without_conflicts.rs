// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The clause-DB limits hold in a search that makes few or no conflicts.
//!
//! An extension adds a theory clause for every propagation it makes (ay's
//! direct-CP engine does: every bound change comes with its explanation
//! clause). Before, the limits (`max_clause_db_bytes`, `max_learned_clauses`)
//! were checked only after a conflict, so a search that propagated a lot and
//! failed rarely grew its clause database without bound: on MiniZinc
//! `orthorio/challenge_04` the CP engine made 41 conflicts in 9 s, held
//! 601,088 clauses and 1.75 GB, and reached the 16 GB limit in 37 s.

use super::*;

/// Adds `per_call` wide, unconstrained lemmas over the variables
/// `junk..junk + width` on each of its first `calls` propagation calls, and
/// never a conflict.
struct LemmaFlood {
    junk: u32,
    width: u32,
    per_call: u32,
    calls: u32,
    made: u32,
}

impl Extension for LemmaFlood {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        if self.made >= self.calls {
            return ExtPropagateResult::none();
        }
        let call = self.made;
        self.made += 1;
        let clauses = (0..self.per_call)
            .map(|k| {
                (0..self.width)
                    .map(|i| {
                        let var = Variable(self.junk + i);
                        // A different sign pattern per lemma, so no two are
                        // duplicates and none is a tautology.
                        if (call * self.per_call + k) >> (i % 16) & 1 == 1 {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        }
                    })
                    .collect()
            })
            .collect();
        ExtPropagateResult::clauses(clauses)
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }
}

/// With a byte limit set and no conflict at all, the search still reduces
/// the theory clauses it no longer needs instead of keeping every one.
#[test]
fn byte_limit_reduces_without_a_conflict() {
    let width = 40;
    let mut solver = Solver::new(8 + width as usize);
    let mut ext = LemmaFlood {
        junk: 8,
        width,
        per_call: 100,
        calls: 64,
        made: 0,
    };
    let limit = solver.clause_db_memory_bytes() + 64 * 1024;
    solver.set_max_clause_db_bytes(Some(limit));

    let result = solver.solve_with_extension(&mut ext);

    assert!(result.is_sat(), "the lemmas are satisfiable: {result:?}");
    assert_eq!(ext.made, ext.calls, "every lemma batch was offered");
    assert_eq!(
        solver.num_conflicts(),
        0,
        "precondition: the search makes no conflict"
    );
    assert!(
        solver.cold.num_reductions > 0,
        "6,400 theory lemmas over a {limit}-byte limit and no reduction"
    );
}

/// Without a limit nothing changes: a conflict-free search does not reduce.
#[test]
fn no_limit_no_reduction_without_a_conflict() {
    let width = 40;
    let mut solver = Solver::new(8 + width as usize);
    let mut ext = LemmaFlood {
        junk: 8,
        width,
        per_call: 100,
        calls: 64,
        made: 0,
    };

    let result = solver.solve_with_extension(&mut ext);

    assert!(result.is_sat(), "the lemmas are satisfiable: {result:?}");
    assert_eq!(solver.num_conflicts(), 0);
    assert_eq!(solver.cold.num_reductions, 0);
}

/// A solver with the clause-ID table disabled (a caller that writes no
/// proof) accepts extension clauses. Before, the theory-clause path read the
/// table unguarded and panicked with an index out of bounds.
#[test]
fn theory_clauses_without_a_clause_id_table() {
    let width = 40;
    let mut solver = Solver::new(8 + width as usize);
    solver.set_clause_ids_disabled(true);
    let mut ext = LemmaFlood {
        junk: 8,
        width,
        per_call: 10,
        calls: 4,
        made: 0,
    };

    let result = solver.solve_with_extension(&mut ext);

    assert!(result.is_sat(), "the lemmas are satisfiable: {result:?}");
    assert_eq!(ext.made, ext.calls);
}
