// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for IncrementalCoreEvolution (Phase 6b) and multi-check-sat
//! via the Solver API (Phase 6c), issue #8154.
//!
//! Covers:
//! - IncrementalCoreEvolution unit tests (6b)
//! - Incremental push/pop with QF_LIA (6a)
//! - Incremental push/pop with QF_UF (6a)
//! - Proof certificates survive push/pop (6a)
//! - Proof quality matches standalone (6a)

#![allow(deprecated)]

use ay_dpll::api::{Logic, Solver, Sort};
use ay_dpll::IncrementalCoreEvolution;
use ntest::timeout;

#[test]
fn test_core_evolution_basic_overlap() {
    let evo =
        IncrementalCoreEvolution::new(vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]);
    assert_eq!(evo.persisted(), &["b"]);
    assert_eq!(evo.entered(), &["c"]);
    assert_eq!(evo.exited(), &["a"]);
    assert!(!evo.is_independent());
    assert!(!evo.is_unchanged());
    assert!((evo.persistence_ratio() - 0.5).abs() < f64::EPSILON);
}

#[test]
fn test_core_evolution_independent() {
    let evo =
        IncrementalCoreEvolution::new(vec!["a".into(), "b".into()], vec!["c".into(), "d".into()]);
    assert!(evo.persisted().is_empty());
    assert_eq!(evo.entered(), &["c", "d"]);
    assert_eq!(evo.exited(), &["a", "b"]);
    assert!(evo.is_independent());
    assert!((evo.persistence_ratio()).abs() < f64::EPSILON);
}

#[test]
fn test_core_evolution_unchanged() {
    let evo =
        IncrementalCoreEvolution::new(vec!["x".into(), "y".into()], vec!["y".into(), "x".into()]);
    assert_eq!(evo.persisted().len(), 2);
    assert!(evo.entered().is_empty());
    assert!(evo.exited().is_empty());
    assert!(evo.is_unchanged());
    assert!((evo.persistence_ratio() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_core_evolution_empty_both() {
    let evo = IncrementalCoreEvolution::new(vec![], vec![]);
    assert!(evo.is_independent());
    assert!(evo.is_unchanged());
    assert!((evo.persistence_ratio()).abs() < f64::EPSILON);
}

#[test]
#[timeout(10_000)]
fn test_solver_api_two_unsat_scopes() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    solver.try_push().unwrap();
    let ten = solver.int_const(10);
    let c = solver.gt(x, ten);
    solver.try_assert_term(c).unwrap();
    let five = solver.int_const(5);
    let c = solver.lt(x, five);
    solver.try_assert_term(c).unwrap();
    assert!(solver.check_sat_with_details().result.is_unsat());
    solver.try_pop().unwrap();

    solver.try_push().unwrap();
    let twenty = solver.int_const(20);
    let c = solver.gt(y, twenty);
    solver.try_assert_term(c).unwrap();
    let fifteen = solver.int_const(15);
    let c = solver.lt(y, fifteen);
    solver.try_assert_term(c).unwrap();
    assert!(solver.check_sat_with_details().result.is_unsat());
    solver.try_pop().unwrap();
}

#[test]
#[timeout(10_000)]
fn test_solver_api_sat_then_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    solver.try_push().unwrap();
    let five = solver.int_const(5);
    let c = solver.gt(x, five);
    solver.try_assert_term(c).unwrap();
    assert!(solver.check_sat_with_details().result.is_sat());
    solver.try_pop().unwrap();

    solver.try_push().unwrap();
    let ten = solver.int_const(10);
    let c = solver.gt(y, ten);
    solver.try_assert_term(c).unwrap();
    let five = solver.int_const(5);
    let c = solver.lt(y, five);
    solver.try_assert_term(c).unwrap();
    assert!(solver.check_sat_with_details().result.is_unsat());
    solver.try_pop().unwrap();
}

#[test]
#[timeout(10_000)]
fn test_solver_api_three_scopes_with_proofs() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_option("produce-proofs", "true");
    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let c = solver.declare_const("c", Sort::Int);

    for (var, lo, hi, idx) in [(a, 10i64, 5i64, 1), (b, 20, 15, 2), (c, 30, 25, 3)] {
        solver.try_push().unwrap();
        let lo_t = solver.int_const(lo);
        let gt = solver.gt(var, lo_t);
        solver.try_assert_term(gt).unwrap();
        let hi_t = solver.int_const(hi);
        let lt = solver.lt(var, hi_t);
        solver.try_assert_term(lt).unwrap();
        assert!(
            solver.check_sat_with_details().result.is_unsat(),
            "scope {idx}"
        );
        assert!(
            solver.export_last_unsat_artifact().is_some(),
            "proof scope {idx}"
        );
        solver.try_pop().unwrap();
    }
}

// --- QF_UF incremental tests (#8154 acceptance criterion 3) ---

#[test]
#[timeout(10_000)]
fn test_qf_uf_incremental_two_unsat_scopes() {
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let c = solver.declare_const("c", Sort::Bool);
    let d = solver.declare_const("d", Sort::Bool);

    // Scope 1: a AND NOT a
    solver.try_push().unwrap();
    solver.try_assert_term(a).unwrap();
    let not_a = solver.not(a);
    solver.try_assert_term(not_a).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "QF_UF scope 1 should be unsat");
    solver.try_pop().unwrap();

    // Scope 2: b AND NOT b (independent conflict)
    solver.try_push().unwrap();
    solver.try_assert_term(b).unwrap();
    let not_b = solver.not(b);
    solver.try_assert_term(not_b).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "QF_UF scope 2 should be unsat");
    solver.try_pop().unwrap();

    // Scope 3: c OR d is SAT
    solver.try_push().unwrap();
    let c_or_d = solver.or(c, d);
    solver.try_assert_term(c_or_d).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "QF_UF scope 3 should be sat");
    solver.try_pop().unwrap();
}

#[test]
#[timeout(10_000)]
fn test_qf_uf_incremental_equality_contradiction() {
    // QF_UF with uninterpreted sorts
    let mut solver = Solver::new(Logic::QfUf);
    let us = Sort::Uninterpreted("U".to_string());
    let a = solver.declare_const("a", us.clone());
    let b = solver.declare_const("b", us.clone());
    let c = solver.declare_const("c", us);

    // Scope 1: a=b AND a!=b (unsat)
    solver.try_push().unwrap();
    let eq_ab = solver.eq(a, b);
    solver.try_assert_term(eq_ab).unwrap();
    let neq_ab = solver.distinct(&[a, b]);
    solver.try_assert_term(neq_ab).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "a=b AND a!=b should be unsat");
    solver.try_pop().unwrap();

    // Scope 2: a=b AND b=c AND a!=c (unsat by transitivity)
    solver.try_push().unwrap();
    let eq_ab = solver.eq(a, b);
    solver.try_assert_term(eq_ab).unwrap();
    let eq_bc = solver.eq(b, c);
    solver.try_assert_term(eq_bc).unwrap();
    let neq_ac = solver.distinct(&[a, c]);
    solver.try_assert_term(neq_ac).unwrap();
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "transitivity violation should be unsat"
    );
    solver.try_pop().unwrap();

    // Scope 3: a!=b AND b!=c (sat -- a,b,c can all be different)
    solver.try_push().unwrap();
    let neq_ab = solver.distinct(&[a, b]);
    solver.try_assert_term(neq_ab).unwrap();
    let neq_bc = solver.distinct(&[b, c]);
    solver.try_assert_term(neq_bc).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "a!=b AND b!=c should be sat");
    solver.try_pop().unwrap();
}

#[test]
#[timeout(10_000)]
fn test_qf_uf_incremental_with_proofs() {
    // Verify proof artifacts survive push/pop in QF_UF
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_option("produce-proofs", "true");
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);

    for (idx, vars) in [(1, (p, p)), (2, (q, q))] {
        solver.try_push().unwrap();
        // Assert v AND NOT v
        solver.try_assert_term(vars.0).unwrap();
        let neg = solver.not(vars.1);
        solver.try_assert_term(neg).unwrap();
        let details = solver.check_sat_with_details();
        assert!(details.result.is_unsat(), "QF_UF proof scope {idx}");
        assert!(
            solver.export_last_unsat_artifact().is_some(),
            "QF_UF proof artifact scope {idx}"
        );
        solver.try_pop().unwrap();
    }
}

// --- Proof certificate on SolveResult (#8154 acceptance criterion 1) ---

#[test]
#[timeout(10_000)]
fn test_incremental_proof_certificate_on_solve_result() {
    // Verify that SolveResult::Unsat carries an SmtProofCertificate after
    // each incremental check-sat, matching standalone quality.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);

    for scope_idx in 0..3 {
        solver.try_push().unwrap();
        let lo = solver.int_const(10 + i64::from(scope_idx));
        let hi = solver.int_const(5 + i64::from(scope_idx));
        let gt = solver.gt(x, lo);
        solver.try_assert_term(gt).unwrap();
        let lt = solver.lt(x, hi);
        solver.try_assert_term(lt).unwrap();

        let details = solver.check_sat_with_details();
        assert!(details.result.is_unsat(), "scope {scope_idx}");

        // The SolveResult::Unsat variant carries an SmtProofCertificate.
        // Verify it exists (proof_certificate returns Some for Unsat).
        let result = details.result.result();
        let cert = result.proof_certificate();
        assert!(
            cert.is_some(),
            "scope {scope_idx}: SolveResult::Unsat should carry SmtProofCertificate"
        );

        solver.try_pop().unwrap();
    }
}

#[test]
#[timeout(10_000)]
fn test_incremental_proof_certificate_matches_standalone_quality() {
    // Compare: standalone UNSAT proof quality vs incremental UNSAT proof quality.
    // Both should produce non-empty Alethe proofs when produce-proofs is enabled.

    // Standalone
    let mut standalone = Solver::new(Logic::QfLia);
    standalone.set_option("produce-proofs", "true");
    let x = standalone.declare_const("x", Sort::Int);
    let ten = standalone.int_const(10);
    let five = standalone.int_const(5);
    let gt = standalone.gt(x, ten);
    standalone.try_assert_term(gt).unwrap();
    let lt = standalone.lt(x, five);
    standalone.try_assert_term(lt).unwrap();
    let standalone_details = standalone.check_sat_with_details();
    assert!(standalone_details.result.is_unsat());
    let standalone_artifact = standalone.export_last_unsat_artifact();
    assert!(
        standalone_artifact.is_some(),
        "standalone should produce proof artifact"
    );

    // Incremental -- same constraints in a pushed scope
    let mut incremental = Solver::new(Logic::QfLia);
    incremental.set_option("produce-proofs", "true");
    let x = incremental.declare_const("x", Sort::Int);

    incremental.try_push().unwrap();
    let ten = incremental.int_const(10);
    let five = incremental.int_const(5);
    let gt = incremental.gt(x, ten);
    incremental.try_assert_term(gt).unwrap();
    let lt = incremental.lt(x, five);
    incremental.try_assert_term(lt).unwrap();
    let incr_details = incremental.check_sat_with_details();
    assert!(incr_details.result.is_unsat());
    let incr_artifact = incremental.export_last_unsat_artifact();
    assert!(
        incr_artifact.is_some(),
        "incremental should produce proof artifact (no trust degradation)"
    );
    incremental.try_pop().unwrap();

    // Both should have non-empty Alethe proofs
    let sa = standalone_artifact.unwrap();
    let ia = incr_artifact.unwrap();
    assert!(
        !sa.alethe.is_empty(),
        "standalone Alethe proof should be non-empty"
    );
    assert!(
        !ia.alethe.is_empty(),
        "incremental Alethe proof should be non-empty"
    );
}

// --- QF_UFLIA incremental test (mixed theory) ---

#[test]
#[timeout(10_000)]
fn test_qf_uflia_incremental_mixed_theory() {
    // Mixed EUF + LIA in incremental mode
    let mut solver = Solver::new(Logic::QfUflia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    // Scope 1: x > 10 AND x < 5 (pure LIA, unsat)
    solver.try_push().unwrap();
    let ten = solver.int_const(10);
    let five = solver.int_const(5);
    let gt = solver.gt(x, ten);
    solver.try_assert_term(gt).unwrap();
    let lt = solver.lt(x, five);
    solver.try_assert_term(lt).unwrap();
    assert!(
        solver.check_sat_with_details().result.is_unsat(),
        "pure LIA scope"
    );
    solver.try_pop().unwrap();

    // Scope 2: x = y AND x != y (EUF equality, unsat)
    solver.try_push().unwrap();
    let eq_xy = solver.eq(x, y);
    solver.try_assert_term(eq_xy).unwrap();
    let neq_xy = solver.distinct(&[x, y]);
    solver.try_assert_term(neq_xy).unwrap();
    assert!(
        solver.check_sat_with_details().result.is_unsat(),
        "EUF scope"
    );
    solver.try_pop().unwrap();

    // Scope 3: x > 0 (sat)
    solver.try_push().unwrap();
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.try_assert_term(gt).unwrap();
    assert!(solver.check_sat_with_details().result.is_sat(), "sat scope");
    solver.try_pop().unwrap();
}
