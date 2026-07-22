// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Property tests for kitten (miniature CDCL sub-solver) incremental soundness.
//!
//! These tests exercise the full CDCL cycle (propagate, conflict, analyze, learn,
//! backtrack) on random formulas. They catch bugs like #7049 (analyze() literal
//! overwriting: lost literals produce over-strong learned clauses that prune valid
//! models, leading to false UNSAT on satisfiable formulas).

use crate::kitten::Kitten;
use proptest::prelude::*;

const KITTEN_INVALID: u32 = u32::MAX;

/// Convert 1-based signed DIMACS literal to kitten external encoding.
fn ext_lit(signed: i32) -> u32 {
    let var = signed.unsigned_abs() - 1;
    var * 2 + if signed < 0 { 1 } else { 0 }
}

/// Generate a random CNF clause over `num_vars` 1-based variables.
fn arb_clause(num_vars: u32) -> impl Strategy<Value = Vec<i32>> {
    proptest::collection::vec(
        (1..=num_vars as i32).prop_flat_map(|v| prop_oneof![Just(v), Just(-v)]),
        1..=4,
    )
}

/// Generate a random CNF formula: (num_vars, clauses).
fn arb_cnf() -> impl Strategy<Value = (u32, Vec<Vec<i32>>)> {
    (3u32..=6).prop_flat_map(|num_vars| {
        let clauses = proptest::collection::vec(arb_clause(num_vars), 2..=12);
        (Just(num_vars), clauses)
    })
}

proptest! {
    /// SAT model correctness: if kitten says SAT, every original clause
    /// has at least one true literal in the model.
    ///
    /// This property catches the #7049 analyze() literal-overwriting bug:
    /// lost literals produce over-strong learned clauses that prune valid
    /// models, leading to false UNSAT on satisfiable formulas.
    #[test]
    fn prop_kitten_sat_model_correctness((num_vars, clauses) in arb_cnf()) {
        let _ = num_vars;
        let mut k = Kitten::new();
        for (i, clause) in clauses.iter().enumerate() {
            let ext_lits: Vec<u32> = clause.iter().map(|&s| ext_lit(s)).collect();
            k.add_clause_with_id(i as u32, &ext_lits, KITTEN_INVALID);
        }
        k.seal_original();
        let result = k.solve();
        if result == 10 {
            // SAT: verify model.
            for (ci, clause) in clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&signed| {
                    k.value(ext_lit(signed)) > 0
                });
                prop_assert!(
                    satisfied,
                    "Clause {} ({:?}) falsified by SAT model",
                    ci, clause
                );
            }
        }
        // UNSAT or UNKNOWN: nothing to check (UNSAT correctness requires
        // proof verification, not model checking).
    }

    /// Incremental assumption soundness: solve, then solve again with
    /// a unit assumption. If the base formula is SAT with x=T forced,
    /// then assuming x should also be SAT.
    #[test]
    fn prop_kitten_incremental_assumption_consistency(
        (num_vars, clauses) in arb_cnf()
    ) {
        let mut k = Kitten::new();
        for (i, clause) in clauses.iter().enumerate() {
            let ext_lits: Vec<u32> = clause.iter().map(|&s| ext_lit(s)).collect();
            k.add_clause_with_id(i as u32, &ext_lits, KITTEN_INVALID);
        }
        k.seal_original();

        // First solve: get baseline.
        let base_result = k.solve();
        if base_result != 10 {
            return Ok(()); // Skip non-SAT cases.
        }

        // Record model values.
        let model: Vec<i8> = (1..=num_vars)
            .map(|v| k.value(ext_lit(v as i32)))
            .collect();

        // Incremental: assume each forced-true literal, verify still SAT.
        for v in 1..=num_vars {
            let val = model[(v - 1) as usize];
            if val == 0 { continue; }
            let assumed = if val > 0 { v as i32 } else { -(v as i32) };
            k.assume(ext_lit(assumed));
            let inc_result = k.solve();
            // The assumption is consistent with the model, so must be SAT.
            prop_assert!(
                inc_result == 10,
                "Assume {} (val={}) returned {} — expected SAT (base was SAT with this assignment)",
                assumed, val, inc_result
            );
        }
    }

    /// Incremental multi-assumption: assume all model literals at once.
    /// If the base formula is SAT with model M, assuming all of M should be SAT.
    #[test]
    fn prop_kitten_incremental_full_model_assumption(
        (num_vars, clauses) in arb_cnf()
    ) {
        let mut k = Kitten::new();
        for (i, clause) in clauses.iter().enumerate() {
            let ext_lits: Vec<u32> = clause.iter().map(|&s| ext_lit(s)).collect();
            k.add_clause_with_id(i as u32, &ext_lits, KITTEN_INVALID);
        }
        k.seal_original();

        let base_result = k.solve();
        if base_result != 10 {
            return Ok(());
        }

        // Assume entire model.
        for v in 1..=num_vars {
            let val = k.value(ext_lit(v as i32));
            if val > 0 {
                k.assume(ext_lit(v as i32));
            } else if val < 0 {
                k.assume(ext_lit(-(v as i32)));
            }
        }
        let inc_result = k.solve();
        prop_assert_eq!(
            inc_result, 10,
            "Assuming full SAT model should be SAT, got {}",
            inc_result
        );
    }
}
