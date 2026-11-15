// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The defining rules the exact acyclic encodings unroll.
//!
//! The classifier calls a problem acyclic although it has stutter rules
//! `P(args) /\ C => P(args)` (#9191,
//! [`ChcProblem::is_tautological_self_loop_clause`]), and the adaptive probes
//! then run this solver in exact acyclic mode. A stutter rule re-derives a
//! tuple its body already holds, so the least model without it is closed
//! under it: deleting it changes no predicate's reachable tuples and no
//! query's verdict. The exact encodings must read the rules the same way.
//! Kept as a definition, a stutter rule on `P` was a cycle to the path
//! expansion (which refused) and a circular definition to the polynomial DAG
//! encoding: `P`'s reach literal justified itself with unconstrained
//! arguments, so a safe query came back as a satisfiable branch that no
//! derivation could replay. That Unknown sent the adaptive probe into its
//! unsafe-only standard pass for the rest of its stage budget (MODEL_CHECKER_CONSUMER ask
//! 2026-10-14-acyclic-8bit-ite-chain, with a stutter rule on the chain's
//! predicate: 11.4 s of a 20 s solve).

use super::*;

impl BmcSolver {
    /// Clause indices by head predicate, without the stutter rules (see the
    /// module documentation). A derivation over these clauses is a derivation
    /// of the original problem, and every original derivation shortens to one.
    pub(super) fn acyclic_defs_by_head(&self) -> FxHashMap<PredicateId, Vec<usize>> {
        let mut defs: FxHashMap<PredicateId, Vec<usize>> = FxHashMap::default();
        for (idx, clause) in self.problem.clauses().iter().enumerate() {
            if ChcProblem::is_tautological_self_loop_clause(clause) {
                continue;
            }
            if let ClauseHead::Predicate(pred, _) = &clause.head {
                defs.entry(*pred).or_default().push(idx);
            }
        }
        defs
    }
}

#[cfg(test)]
mod tests;
