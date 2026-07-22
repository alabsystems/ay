// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Facade-level tests for incremental core evolution (#8154).
//!
//! Verifies that `IncrementalCoreEvolution` and `SmtProofCertificate` are
//! accessible through `ay::prelude::*` and work correctly at the consumer
//! API boundary.

use ay::prelude::*;

#[test]
fn test_incremental_core_evolution_type_accessible() {
    let _: Option<IncrementalCoreEvolution> = None;
    let _: Option<SmtProofCertificate> = None;
}

#[test]
fn test_incremental_core_evolution_unit() {
    let evo =
        IncrementalCoreEvolution::new(vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]);
    assert_eq!(evo.persisted(), &["b".to_string()]);
    assert_eq!(evo.entered(), &["c".to_string()]);
    assert_eq!(evo.exited(), &["a".to_string()]);
    assert!(!evo.is_independent());
    assert!(!evo.is_unchanged());
    assert!((evo.persistence_ratio() - 0.5).abs() < f64::EPSILON);
}

#[test]
fn test_incremental_core_evolution_independent() {
    let evo =
        IncrementalCoreEvolution::new(vec!["a".into(), "b".into()], vec!["c".into(), "d".into()]);
    assert!(evo.persisted().is_empty());
    assert!(evo.is_independent());
    assert!(!evo.is_unchanged());
    assert!((evo.persistence_ratio() - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_incremental_core_evolution_unchanged() {
    let evo =
        IncrementalCoreEvolution::new(vec!["a".into(), "b".into()], vec!["a".into(), "b".into()]);
    assert_eq!(evo.persisted().len(), 2);
    assert!(evo.entered().is_empty());
    assert!(evo.exited().is_empty());
    assert!(!evo.is_independent());
    assert!(evo.is_unchanged());
    assert!((evo.persistence_ratio() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_smt_proof_certificate_on_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let ten = solver.int_const(10);
    let five = solver.int_const(5);
    let gt = solver.gt(x, ten);
    let lt = solver.lt(x, five);
    solver.assert_term(gt);
    solver.assert_term(lt);

    let result = solver.check_sat();
    assert!(result.is_unsat(), "Expected UNSAT, got {result:?}");

    // SolveResult::Unsat carries an SmtProofCertificate
    let cert = result.result().proof_certificate();
    assert!(
        cert.is_some(),
        "UNSAT result should carry a proof certificate"
    );
}

#[test]
fn test_smt_proof_certificate_via_details() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let ten = solver.int_const(10);
    let five = solver.int_const(5);
    let gt = solver.gt(x, ten);
    let lt = solver.lt(x, five);
    solver.assert_term(gt);
    solver.assert_term(lt);

    let details = solver.check_sat_with_details();
    match details.accept_for_consumer() {
        Ok(SolveResult::Unsat(cert)) => {
            // Certificate exists -- verify it has the expected type
            let _ = cert.sat_certificate();
        }
        other => panic!("Expected Unsat with cert, got {other:?}"),
    }
}

#[test]
fn test_incremental_types_accessible_through_api_module() {
    use ay::api::{IncrementalCoreEvolution, SmtProofCertificate};

    let _: Option<IncrementalCoreEvolution> = None;
    let _: Option<SmtProofCertificate> = None;
}

#[test]
fn test_incremental_types_accessible_through_root() {
    let _: Option<IncrementalCoreEvolution> = None;
    let _: Option<SmtProofCertificate> = None;
}
