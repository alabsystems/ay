// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Facade-level integration tests for check_sat_assuming and UNSAT core APIs (#8247).
//!
//! Verifies that neural-verification-consumer can use assumption-based solving and UNSAT core
//! extraction entirely through the `ay` facade crate, without depending on
//! internal crates like `ay_dpll`.

use ay::prelude::*;

/// Core use case: check_sat_assuming is accessible through ay::Solver.
///
/// Exercises the exact API pattern neural-verification-consumer needs for ReLU branch-and-bound:
/// 1. Build a solver with constraints
/// 2. Call check_sat_assuming with temporary assumptions
/// 3. On UNSAT, extract which assumptions caused the conflict
#[test]
fn test_check_sat_assuming_accessible_through_facade() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Permanent constraint: 0 <= x <= 10
    let x_ge_0 = solver.ge(x, zero);
    let x_le_10 = solver.le(x, ten);
    solver.assert_term(x_ge_0);
    solver.assert_term(x_le_10);

    // Satisfiable without assumptions
    assert!(solver.check_sat().is_sat());

    // Temporary assumptions that contradict permanent constraints: x > 100
    let hundred = solver.int_const(100);
    let x_gt_100 = solver.gt(x, hundred);
    let result = solver.check_sat_assuming(&[x_gt_100]);
    assert!(result.is_unsat(), "x > 100 contradicts x <= 10");

    // After UNSAT, unsat_assumptions returns the conflicting assumptions
    let unsat_assumptions = solver.unsat_assumptions();
    assert!(
        unsat_assumptions.is_some(),
        "unsat_assumptions should be available after check_sat_assuming UNSAT"
    );

    // The original constraints still hold (assumptions were temporary)
    assert!(
        solver.check_sat().is_sat(),
        "permanent constraints are still satisfiable"
    );
}

/// Verify the `AssumptionSolveDetails` atomic envelope is accessible.
///
/// neural-verification-consumer benefits from `check_sat_assuming_with_details` which returns
/// the UNSAT assumptions and solve statistics in a single atomic call.
#[test]
fn test_check_sat_assuming_with_details_through_facade() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // x >= 0
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    // Assume x < 0 (contradicts x >= 0)
    let x_lt_0 = solver.lt(x, zero);
    let details: AssumptionSolveDetails = solver.check_sat_assuming_with_details(&[x_lt_0]);

    assert!(details.solve.result.is_unsat(), "x < 0 contradicts x >= 0");
    assert!(
        details.unsat_assumptions.is_some(),
        "unsat assumptions should be in the atomic envelope"
    );
}

/// Verify named UNSAT core extraction works through the facade.
///
/// Named assertions + unsat_core() gives neural-verification-consumer the ability to identify
/// which constraint groups caused a conflict.
#[test]
fn test_named_unsat_core_through_facade() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let five = solver.int_const(5);
    let ten = solver.int_const(10);

    // Named contradictory assertions
    let x_gt_10 = solver.gt(x, ten);
    let x_lt_5 = solver.lt(x, five);
    let x_ge_0 = solver.ge(x, zero);

    solver.try_assert_named(x_gt_10, "relu_upper").unwrap();
    solver.try_assert_named(x_lt_5, "relu_lower").unwrap();
    solver.try_assert_named(x_ge_0, "nonneg").unwrap();

    let result = solver.check_sat();
    assert!(result.is_unsat());

    // Named UNSAT core should identify the conflicting assertions
    let core = solver.unsat_core();
    assert!(core.is_some(), "unsat core should be available");
    let core = core.unwrap();
    assert!(
        core.contains(&"relu_upper".to_string()) || core.contains(&"relu_lower".to_string()),
        "core should include relu_upper and/or relu_lower: {core:?}"
    );
}

/// Verify SmtProofCertificate is accessible and functional through the facade.
///
/// When check_sat_assuming returns UNSAT, the SolveResult::Unsat variant
/// carries an SmtProofCertificate that consumers can inspect.
#[test]
fn test_smt_proof_certificate_from_assumptions() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    let x_lt_0 = solver.lt(x, zero);
    let result = solver.check_sat_assuming(&[x_lt_0]);
    assert!(result.is_unsat());

    // Extract the proof certificate from the UNSAT result
    let inner = result.into_inner();
    match inner {
        SolveResult::Unsat(cert) => {
            // SmtProofCertificate is accessible through the facade
            let _cert: SmtProofCertificate = cert;
            // Diagnostic original-clause support is available.
            let _support = _cert.tracked_original_clause_ids();
        }
        _ => panic!("expected Unsat variant"),
    }
}

/// Verify panic-safe try_check_sat_assuming is accessible.
///
/// neural-verification-consumer runs in a long-lived process and needs panic safety.
#[test]
fn test_try_check_sat_assuming_through_facade() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let eq = solver.eq(x, one);

    let result = solver.try_check_sat_assuming(&[eq]);
    assert!(result.is_ok());
    assert!(result.unwrap().is_sat());
}

/// Verify the annotated UNSAT core (theory-attributed) works through the facade.
///
/// neural-verification-consumer can use theory attributions to understand which theory
/// (LIA, EUF, etc.) contributed to each part of the UNSAT proof.
#[test]
fn test_annotated_unsat_core_with_assumptions() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let ten = solver.int_const(10);
    let five = solver.int_const(5);

    let x_gt_10 = solver.gt(x, ten);
    let x_lt_5 = solver.lt(x, five);
    solver.try_assert_named(x_gt_10, "upper_bound").unwrap();
    solver.try_assert_named(x_lt_5, "lower_bound").unwrap();

    let result = solver.check_sat();
    assert!(result.is_unsat());

    // Annotated core provides theory attributions
    let annotated: Option<AnnotatedUnsatCore> = solver.annotated_unsat_core();
    assert!(
        annotated.is_some(),
        "annotated unsat core should be available with proofs enabled"
    );
    let core = annotated.unwrap();
    assert!(!core.is_empty(), "annotated core should not be empty");

    // Each entry has a name and theory attributions
    for entry in core.entries() {
        let _name: &str = &entry.name;
        let _attrs: &[TheoryAttribution] = &entry.attributions;
    }
}

/// Verify all assumption-related types are importable through ay::api::{...}.
#[test]
fn test_assumption_types_accessible_through_api_module() {
    use ay::api::{
        AssumptionSolveDetails, SmtProofCertificate, SolveDetails, SolveResult, Solver,
        SolverError, Term, VerifiedSolveResult,
    };

    let _: Option<AssumptionSolveDetails> = None;
    let _: Option<SmtProofCertificate> = None;
    let _: Option<SolveDetails> = None;
    let _: fn(&SolveResult) -> bool = SolveResult::is_unsat;
    let _: fn(&VerifiedSolveResult) -> bool = VerifiedSolveResult::is_unsat;
    let _: Option<Solver> = None;
    let _: Option<SolverError> = None;
    let _: Option<Term> = None;
}

/// Verify all assumption-related types are importable through ay::{...} (root).
#[test]
fn test_assumption_types_accessible_through_root() {
    let _: Option<ay::AssumptionSolveDetails> = None;
    let _: Option<ay::SmtProofCertificate> = None;
    let _: Option<ay::SolveDetails> = None;
    let _: Option<ay::SolveResult> = None;
    let _: Option<ay::VerifiedSolveResult> = None;
    let _: Option<ay::Solver> = None;
    let _: Option<ay::SolverError> = None;
    let _: Option<ay::Term> = None;
    let _: Option<ay::AnnotatedUnsatCore> = None;
    let _: Option<ay::AnnotatedCoreLiteral> = None;
    let _: Option<ay::TheoryAttribution> = None;
}

/// End-to-end: ReLU branch-and-bound simulation.
///
/// This test simulates the exact neural-verification-consumer usage pattern: encode ReLU
/// activation states as assumptions, check with assumptions, and extract
/// the conflicting assumptions on UNSAT.
#[test]
fn test_relu_branch_and_bound_simulation() {
    let mut solver = Solver::new(Logic::QfLia);

    // Network: x -> [relu1] -> y -> [relu2] -> z
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let z = solver.declare_const("z", Sort::Int);
    let zero = solver.int_const(0);

    // Input bounds: -5 <= x <= 5
    let neg5 = solver.int_const(-5);
    let five = solver.int_const(5);
    let x_ge_neg5 = solver.ge(x, neg5);
    solver.assert_term(x_ge_neg5);
    let x_le_5 = solver.le(x, five);
    solver.assert_term(x_le_5);

    // relu1: y = max(0, x) encoded as:
    //   y >= 0, y >= x, (y = 0 or y = x)
    let y_ge_0 = solver.ge(y, zero);
    solver.assert_term(y_ge_0);
    let y_ge_x = solver.ge(y, x);
    solver.assert_term(y_ge_x);

    // relu2: z = max(0, y) -- since y >= 0, z = y
    let z_ge_0 = solver.ge(z, zero);
    solver.assert_term(z_ge_0);
    let z_ge_y = solver.ge(z, y);
    solver.assert_term(z_ge_y);

    // Branch-and-bound: assume relu1 is inactive (y = 0) and relu2 is
    // active (z > 0). If y = 0 then z <= y = 0, so z > 0 is contradictory.
    let relu1_inactive = solver.eq(y, zero);
    let z_positive = solver.gt(z, zero);
    let z_le_y = solver.le(z, y);

    // With y=0 and z<=y and z>0, this should be UNSAT
    let result = solver.check_sat_assuming(&[relu1_inactive, z_positive, z_le_y]);
    assert!(
        result.is_unsat(),
        "relu1 inactive + z > 0 + z <= y should be UNSAT"
    );

    // Extract conflicting assumptions
    let conflicts = solver.unsat_assumptions();
    assert!(conflicts.is_some(), "should have conflicting assumptions");

    // The solver should be reusable for the next branch
    let relu1_active = solver.gt(y, zero);
    let x_positive = solver.gt(x, zero);
    let result2 = solver.check_sat_assuming(&[relu1_active, x_positive]);
    assert!(result2.is_sat(), "relu1 active + x > 0 should be SAT");
}
