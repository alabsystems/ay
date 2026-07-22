// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Facade-level tests for explainability types (#8153).
//!
//! Verifies that `AnnotatedUnsatCore`, `TheoryAttribution`, `ModelProvenance`,
//! and related types are accessible through `ay::prelude::*` and work correctly
//! at the consumer API boundary.

use ay::prelude::*;

#[test]
fn test_annotated_unsat_core_type_accessible_through_facade() {
    // Verify the types are importable through ay::prelude
    let _: Option<AnnotatedUnsatCore> = None;
    let _: Option<TheoryAttribution> = None;
    let _: Option<AnnotatedCoreLiteral> = None;
    let _: Option<CongruenceStep> = None;
    let _: Option<CongruenceReason> = None;
    let _: Option<ModelProvenance> = None;
    let _: Option<VariableProvenance> = None;
    let _: Option<AssignmentReason> = None;
    let _: Option<ExplanationReport> = None;
    let _: Option<ExplanationKind> = None;
    let _: Option<SatExplanation> = None;
    let _: Option<ModelAssignmentExplanation> = None;
    let _: Option<UnsatExplanation> = None;
    let _: Option<UnsatCoreSource> = None;
    let _: Option<CoreConstraintExplanation> = None;
    let _: Option<UnknownExplanation> = None;
}

#[test]
fn test_annotated_core_lia_contradiction() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let ten = solver.int_const(10);
    let five = solver.int_const(5);

    // x > 10 AND x < 5 -> UNSAT
    let gt = solver.gt(x, ten);
    let lt = solver.lt(x, five);
    solver.try_assert_named(gt, "x_gt_10").unwrap();
    solver.try_assert_named(lt, "x_lt_5").unwrap();

    let result = solver.check_sat();
    assert!(result.is_unsat(), "Expected UNSAT, got {result:?}");

    // annotated_unsat_core should be available after UNSAT with proofs enabled
    let core = solver.annotated_unsat_core();
    assert!(
        core.is_some(),
        "annotated core should be available after UNSAT with proofs enabled"
    );

    let core = core.unwrap();
    assert!(
        !core.is_empty(),
        "core should not be empty for contradiction"
    );

    // Core should reference at least one of our named assertions
    let names: Vec<&str> = core.entries().iter().map(|e| e.name.as_str()).collect();
    assert!(
        names.contains(&"x_gt_10") || names.contains(&"x_lt_5"),
        "core names should include at least one of x_gt_10/x_lt_5: {names:?}"
    );
}

#[test]
fn test_model_provenance_accessible() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    let result = solver.check_sat();
    assert!(result.is_sat(), "Expected SAT");

    // model_provenance() should return provenance after SAT
    let prov = solver.model_provenance();
    assert!(
        prov.is_some(),
        "model provenance should be available after SAT"
    );

    let prov = prov.unwrap();
    assert!(!prov.is_empty(), "should have at least one variable");

    // x was constrained by the gt assertion
    let x_prov = prov.get("x");
    assert!(x_prov.is_some(), "should find provenance for x");
}

#[test]
fn test_explainability_types_accessible_through_api_module() {
    // Verify the types are also accessible through ay::api::{...}
    use ay::api::{
        AnnotatedCoreLiteral, AnnotatedUnsatCore, AssignmentReason, CongruenceReason,
        CongruenceStep, CoreConstraintExplanation, ExplanationKind, ExplanationReport,
        ModelAssignmentExplanation, ModelProvenance, SatExplanation, TheoryAttribution,
        UnknownExplanation, UnsatCoreSource, UnsatExplanation, VariableProvenance,
    };

    let _: Option<AnnotatedUnsatCore> = None;
    let _: Option<TheoryAttribution> = None;
    let _: Option<AnnotatedCoreLiteral> = None;
    let _: Option<CongruenceStep> = None;
    let _: Option<CongruenceReason> = None;
    let _: Option<ModelProvenance> = None;
    let _: Option<VariableProvenance> = None;
    let _: Option<AssignmentReason> = None;
    let _: Option<ExplanationReport> = None;
    let _: Option<ExplanationKind> = None;
    let _: Option<SatExplanation> = None;
    let _: Option<ModelAssignmentExplanation> = None;
    let _: Option<UnsatExplanation> = None;
    let _: Option<UnsatCoreSource> = None;
    let _: Option<CoreConstraintExplanation> = None;
    let _: Option<UnknownExplanation> = None;
}

#[test]
fn test_explainability_types_accessible_through_root() {
    // Verify the types are accessible through ay::{...} (root re-export)
    let _: Option<ay::AnnotatedUnsatCore> = None;
    let _: Option<ay::TheoryAttribution> = None;
    let _: Option<ay::AnnotatedCoreLiteral> = None;
    let _: Option<ay::CongruenceStep> = None;
    let _: Option<ay::CongruenceReason> = None;
    let _: Option<ay::ModelProvenance> = None;
    let _: Option<ay::VariableProvenance> = None;
    let _: Option<ay::AssignmentReason> = None;
    let _: Option<ay::ExplanationReport> = None;
    let _: Option<ay::ExplanationKind> = None;
    let _: Option<ay::SatExplanation> = None;
    let _: Option<ay::ModelAssignmentExplanation> = None;
    let _: Option<ay::UnsatExplanation> = None;
    let _: Option<ay::UnsatCoreSource> = None;
    let _: Option<ay::CoreConstraintExplanation> = None;
    let _: Option<ay::UnknownExplanation> = None;
}

#[test]
fn test_explanation_report_facade_sat_smoke() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let eq = solver.eq(x, one);
    solver.try_assert_term(eq).unwrap();

    assert!(solver.check_sat().is_sat());

    let report = solver
        .explain_last_result()
        .expect("SAT explanation report should be available");
    let rendered = report.render_text();
    assert!(rendered.contains("SAT explanation:"), "got:\n{rendered}");
    assert!(rendered.contains("x = 1"), "got:\n{rendered}");
}
