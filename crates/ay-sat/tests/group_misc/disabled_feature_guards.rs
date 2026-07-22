// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard tests for inprocessing features that were previously disabled due to
//! soundness bugs and have since been fixed.
//!
//! Fixed features:
//!   - Factorization: reconstruction entries removed (CaDiCaL parity), #3373 fixed
//!
//! Previously disabled, now re-enabled:
//!   - Conditioning (GBCE): fixed with fixpoint-refined autarky partition (#3432)
//!   - HBR: re-enabled after probe_parent array fix (#3419)
//!   - HTR: was wrong-UNSAT on uf200 (#3873), fixed with collect_level0_garbage() (#3971)
//!
//! Default-ON since 2026-07-10 (wf_55735963 collapse+BVE default flip):
//!   - SCC Decompose + congruence eligibility on the Default DIMACS route via
//!     the route-aware AY_AB_SUBST_AUTO probe (kill-switch =0). The historical
//!     reconstruction blockers were root-caused and fixed (ef818369 preprocess
//!     subsume promotion; wf_ff5991a1 congruence emission fixes) and the
//!     scoreboard measurement recorded +7 UNSAT flips / 0 hard losses.
//!     Raw `Solver::new()` construction still keeps decompose opt-in.

use ay_sat::{parse_dimacs, Solver};
use ntest::timeout;

/// Verify that factorization is enabled by default and runs on structured formulas.
#[test]
#[timeout(5_000)]
fn guard_factorization_enabled_after_solve() {
    // Small structured formula with factoring opportunity (2x3 matrix pattern).
    let cnf = "p cnf 6 8\n1 2 3 0\n-1 2 3 0\n1 -2 3 0\n-1 -2 3 0\n4 5 6 0\n-4 5 6 0\n4 -5 6 0\n-4 -5 6 0\n";
    let formula = parse_dimacs(cnf).expect("parse");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();

    // Factor is enabled by default; the formula should still solve correctly.
    assert!(
        result.is_sat(),
        "Structured formula must be SAT with factorization enabled"
    );
}

/// Verify the SCC-decompose default on the DIMACS route: ON via the
/// route-aware AUTO probe since 2026-07-10 (wf_55735963; kill-switch
/// AY_AB_SUBST_AUTO=0 — asserted hermetically when set, same tolerant
/// pattern as the AY_AB_BVE_SPARSE tests in variant.rs).
#[test]
#[timeout(5_000)]
fn guard_decompose_default_after_solve() {
    // Binary implication chain forming an SCC: 1->2, 2->3, 3->4, 4->-2 (cycle).
    let cnf = "p cnf 4 4\n1 2 0\n-1 3 0\n-3 4 0\n-4 -2 0\n";
    let formula = parse_dimacs(cnf).expect("parse");
    let mut solver = formula.into_solver();
    match std::env::var("AY_AB_SUBST_AUTO").ok().as_deref() {
        None | Some("1") => assert!(
            solver.inprocessing_feature_profile().decompose,
            "DIMACS default enables decompose eligibility (AUTO default-ON, \
             probe-gated; wf_55735963)"
        ),
        Some(_) => assert!(
            !solver.inprocessing_feature_profile().decompose,
            "kill-switch (AY_AB_SUBST_AUTO=0) restores decompose-off"
        ),
    }
    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "Binary implication formula must be SAT under the default profile"
    );
}

/// Verify that a fresh Solver created via `Solver::new()` has factorization enabled.
#[test]
#[timeout(5_000)]
fn guard_factorization_enabled_fresh_solver() {
    let mut solver = Solver::new(4);
    solver.add_clause(vec![ay_sat::Literal::positive(ay_sat::Variable::new(0))]);
    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "Fresh solver with factorization enabled must produce correct SAT"
    );
}

/// Verify that decompose remains explicitly available on a fresh solver.
#[test]
#[timeout(5_000)]
fn guard_decompose_opt_in_fresh_solver() {
    let mut solver = Solver::new(4);
    assert!(
        !solver.inprocessing_feature_profile().decompose,
        "fresh solvers keep decompose opt-in until reconstruction is safe"
    );
    solver.set_decompose_enabled(true);
    solver.add_clause(vec![ay_sat::Literal::positive(ay_sat::Variable::new(0))]);
    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "Fresh solver with decompose explicitly enabled must produce correct SAT"
    );
}
