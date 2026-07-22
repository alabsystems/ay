// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV delayed operation extension for SAT solver integration (#8284).
//!
//! NOTE: This module is currently UNUSED. The BV solve path uses a post-solve
//! re-check loop instead of Extension::check() + AddClauses (#8480). The
//! AddClauses path caused spurious UNSAT when injecting thousands of
//! new-variable circuit clauses into a complete model via add_theory_lemma.
//! This code is retained for potential future use if add_theory_lemma's
//! bulk-addition path is fixed.
//!
//! Implements the `Extension` trait so that delayed BV operations (mul, div,
//! rem on wide bitvectors) are checked during SAT search rather than in a
//! post-solve re-solve loop.
//!
//! Reference: `reference/z3/src/sat/smt/bv_solver.cpp:628-652`

#![allow(dead_code)]

// #8529: Use deterministic hash maps in all builds.
use ay_bv::{BvBits, BvSolver, DelayedBvState};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{CnfLit, TermId, TermStore};
use ay_sat::{ExtCheckResult, ExtPropagateResult, Extension, Literal, SolverContext};

use super::bv_encoding;

/// Maximum check iterations within a single SAT solve. After this many
/// check() calls that add clauses, we accept the result to prevent
/// infinite loops. Z3 guarantees convergence because Phase 2 always
/// builds the full circuit; we do the same.
const MAX_CHECK_ITERATIONS: u32 = 32;

/// Extension that checks delayed BV operations during SAT search.
///
/// NOTE: Currently unused -- see module-level doc comment (#8480).
#[allow(dead_code)]
pub(in crate::executor) struct BvDelayedExtension<'a> {
    /// Delayed operation state extracted from the BvSolver.
    delayed_state: DelayedBvState,
    /// Offset to convert BV literal space to SAT literal space.
    /// BV variables are numbered starting from 1; after Tseitin encoding,
    /// they are shifted by `tseitin_num_vars` in the combined CNF.
    var_offset: i32,
    /// Reference to the term store for building circuits.
    terms: &'a TermStore,
    /// Division caches from the original BvSolver: (unsigned_cache, signed_cache, next_var).
    /// Used when building full circuits for Phase 2 escalation.
    div_caches: Option<(
        HashMap<(TermId, TermId), (BvBits, BvBits)>,
        HashMap<(TermId, TermId), (BvBits, BvBits, CnfLit, CnfLit)>,
        u32,
    )>,
    /// Number of check iterations performed.
    check_iterations: u32,
}

impl<'a> BvDelayedExtension<'a> {
    /// Create a new BV delayed extension.
    pub(in crate::executor) fn new(
        delayed_state: DelayedBvState,
        var_offset: i32,
        terms: &'a TermStore,
        div_caches: Option<(
            HashMap<(TermId, TermId), (BvBits, BvBits)>,
            HashMap<(TermId, TermId), (BvBits, BvBits, CnfLit, CnfLit)>,
            u32,
        )>,
    ) -> Self {
        Self {
            delayed_state,
            var_offset,
            terms,
            div_caches,
            check_iterations: 0,
        }
    }

    /// Convert a BV-space CNF clause to SAT-space literals.
    fn bv_clause_to_sat_lits(&self, clause: &ay_core::CnfClause) -> Vec<Literal> {
        clause
            .literals()
            .iter()
            .map(|&lit| crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(lit, self.var_offset)))
            .collect()
    }

    /// Build a partial assignment map from the SAT solver trail.
    ///
    /// Returns an array indexed by SAT variable id where each entry is
    /// `Some(true/false)` if assigned, `None` if unassigned. Used by
    /// `check_partial` to evaluate delayed operations on partial models.
    fn build_partial_assignment(&self, ctx: &dyn SolverContext) -> Vec<Option<bool>> {
        let trail = ctx.trail();
        let num_vars = trail
            .iter()
            .map(|lit| lit.variable().id() as usize + 1)
            .max()
            .unwrap_or(0);
        let mut assigned = vec![None; num_vars];
        for &lit in trail {
            let var = lit.variable();
            assigned[var.id() as usize] = Some(lit.is_positive());
        }
        assigned
    }
}

impl Extension for BvDelayedExtension<'_> {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        // #8480: Temporarily disabled BCP-time partial checks.
        // The check_partial path was producing unsound clauses during BCP
        // that caused spurious UNSAT on satisfiable QF_ABV/QF_BV instances.
        // The complete-model check() path remains active.
        ExtPropagateResult::default()
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        if !self.delayed_state.has_unresolved() {
            return ExtCheckResult::Sat;
        }

        if self.check_iterations >= MAX_CHECK_ITERATIONS {
            return ExtCheckResult::Sat;
        }

        self.check_iterations += 1;

        let trail = ctx.trail();
        let num_vars = trail
            .iter()
            .map(|lit| lit.variable().id() as usize + 1)
            .max()
            .unwrap_or(0);
        let mut model = vec![false; num_vars];
        for &lit in trail {
            let var = lit.variable();
            model[var.id() as usize] = lit.is_positive();
        }

        // Phase 1: Check delayed ops with cheap axiom escalation.
        let (cheap_clauses, needs_circuit) = self.delayed_state.check(&model, self.var_offset);

        let mut all_sat_clauses: Vec<Vec<Literal>> = Vec::new();

        for clause in &cheap_clauses {
            all_sat_clauses.push(self.bv_clause_to_sat_lits(clause));
        }

        // Phase 2: Build full circuits for ops that exhausted cheap axioms.
        if !needs_circuit.is_empty() {
            let mut tmp_bv = BvSolver::new(self.terms);
            tmp_bv.set_term_to_bits(self.delayed_state.term_to_bits().clone());
            if let Some((ref ucache, ref scache, ref mut next_var)) = self.div_caches {
                tmp_bv.set_div_caches(ucache.clone(), scache.clone());
                tmp_bv.set_next_var(*next_var);
            }
            tmp_bv.set_delayed_ops(self.delayed_state.delayed_ops().to_vec());

            for &idx in &needs_circuit {
                let circuit_clauses = tmp_bv.build_delayed_circuit(idx);
                for clause in &circuit_clauses {
                    all_sat_clauses.push(self.bv_clause_to_sat_lits(clause));
                }
                let bv_extra = tmp_bv.take_clauses();
                for clause in &bv_extra {
                    all_sat_clauses.push(self.bv_clause_to_sat_lits(clause));
                }
            }

            if let Some((_, _, ref mut next_var)) = self.div_caches {
                *next_var = tmp_bv.num_vars() + 1;
            }
        }

        if all_sat_clauses.is_empty() {
            ExtCheckResult::Sat
        } else {
            ExtCheckResult::AddClauses(all_sat_clauses)
        }
    }

    fn backtrack(&mut self, _new_level: u32) {}

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }
}
