// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for structured explanation reports (#8693).

use num_bigint::BigInt;

use crate::api::{ExplanationKind, Logic, ModelValue, Solver, SolverError, Sort, UnsatCoreSource};

#[test]
fn test_sat_explanation_report_includes_model_value_and_reason() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let eq = solver.eq(x, one);
    solver.try_assert_term(eq).unwrap();

    assert!(solver.check_sat().is_sat());

    let report = solver.try_explain_last_result().unwrap();
    let sat = report
        .sat_explanation()
        .expect("SAT report should carry SAT explanation");
    let x_assignment = sat
        .assignments()
        .iter()
        .find(|assignment| assignment.name() == "x")
        .expect("x should be in assignment explanation");

    assert_eq!(
        x_assignment.value(),
        Some(&ModelValue::Int(BigInt::from(1)))
    );
    assert!(
        !matches!(
            report.kind(),
            ExplanationKind::Unsat(_) | ExplanationKind::Unknown(_)
        ),
        "expected SAT report, got {report:?}"
    );

    let rendered = report.render_text();
    assert!(rendered.contains("SAT explanation:"), "got:\n{rendered}");
    assert!(rendered.contains("x = 1"), "got:\n{rendered}");
    assert!(rendered.contains("assignment(s)"), "got:\n{rendered}");
}

#[test]
fn test_unsat_explanation_report_falls_back_to_named_core_without_proofs() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let pos = solver.gt(x, zero);
    let neg = solver.lt(x, zero);
    solver.try_assert_named(pos, "x_gt_0").unwrap();
    solver.try_assert_named(neg, "x_lt_0").unwrap();

    assert!(solver.check_sat().is_unsat());

    let report = solver.try_explain_last_result().unwrap();
    let unsat = report
        .unsat_explanation()
        .expect("UNSAT report should carry UNSAT explanation");
    assert_eq!(unsat.core_source(), UnsatCoreSource::NamedCoreOnly);
    assert!(
        unsat.core().iter().any(|entry| entry.name() == "x_gt_0")
            || unsat.core().iter().any(|entry| entry.name() == "x_lt_0"),
        "core should mention at least one named contradictory bound: {:?}",
        unsat.core()
    );
    assert!(
        report
            .diagnostics()
            .iter()
            .any(|msg| msg.contains("annotated unsat core unavailable")),
        "missing attribution diagnostic: {:?}",
        report.diagnostics()
    );

    let rendered = report.render_text();
    assert!(rendered.contains("UNSAT explanation:"), "got:\n{rendered}");
    assert!(
        rendered.contains("named core without proof-derived theory attribution"),
        "got:\n{rendered}"
    );
}

#[test]
fn test_explanation_report_before_solve_returns_no_result() {
    let solver = Solver::new(Logic::QfLia);
    match solver.try_explain_last_result() {
        Err(SolverError::NoResult) => {}
        other => panic!("expected NoResult, got {other:?}"),
    }
}
