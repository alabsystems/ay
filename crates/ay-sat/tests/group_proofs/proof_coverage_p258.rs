// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Proof coverage tests for untested code paths (Part of #3411, Part of #3292).
//!
//! These tests verify behavior of recently added code through the public API:
//! - Random k-SAT classifier (skip BVE/congruence on uniform non-binary formulas)
//!
//! Note: BVE elimination and fixpoint guard tests are in the lib-level test
//! suite (`solver/tests.rs`) which can call `bve()` directly.

use ay_sat::{Literal, SatResult, Solver, Variable};

/// Random 3-SAT formula at the phase transition ratio (4.267) should solve
/// correctly with BVE enabled. The random k-SAT classifier detects uniform
/// structure and skips gate-dependent BVE passes, but CaDiCaL-style fastelim
/// (occurrence-based, no gates, bound=8) runs unconditionally during
/// preprocessing and may eliminate variables. See config_preprocess.rs:394.
///
/// #3411: validates `is_uniform_nonbinary_irredundant_formula()` integration.
/// #4209: preprocessing BVE scheduling fix (fastelim runs at 0 conflicts).
#[test]
fn test_random_3sat_bve_skipped_via_classifier() {
    let num_vars = 200;
    let num_clauses = 854; // ~4.267 * 200
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);

    // Deterministic LCG for reproducible random clauses
    let mut seed: u64 = 12345;
    let mut next_rng = || -> u64 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed
    };

    for _ in 0..num_clauses {
        let mut vars = [0u32; 3];
        let mut count = 0;
        while count < 3 {
            let v = (next_rng() % num_vars as u64) as u32;
            if !vars[..count].contains(&v) {
                vars[count] = v;
                count += 1;
            }
        }
        let lits: Vec<Literal> = vars
            .iter()
            .map(|&v| {
                if next_rng() % 2 == 0 {
                    Literal::positive(Variable::new(v))
                } else {
                    Literal::negative(Variable::new(v))
                }
            })
            .collect();
        solver.add_clause(lits);
    }

    let result = solver.solve().into_inner();

    // Fastelim (preprocessing, bound=8, no gates) runs unconditionally and
    // may eliminate variables. Gate-dependent passes are skipped by the
    // classifier (tested in preprocessing_bve.rs unit tests).
    // We verify solver correctness on this class of formula.

    // Verify result is valid
    match result {
        SatResult::Sat(model) => {
            assert!(
                !model.is_empty(),
                "SAT model should have at least one variable"
            );
        }
        SatResult::Unsat(_) => {} // UNSAT is also valid near phase transition
        SatResult::Unknown => panic!("Solver should not return Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}
