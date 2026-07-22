// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Detailed execute_direct envelope tests for #6708.

use super::*;

#[test]
fn test_execute_with_details_projects_unknown_and_preserves_metadata_6708() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-models", "false"));
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.int_gt(Expr::int(0)));
    program.check_sat();

    let details = execute_with_details(&program).unwrap();
    match details.result {
        ExecuteResult::Unknown(reason) => {
            assert!(
                reason.contains("model extraction failed"),
                "expected model extraction unknown, got: {reason}"
            );
        }
        other => panic!("expected Unknown with details projection, got {other:?}"),
    }

    let degradation = details.degradation.expect("expected degradation metadata");
    assert_eq!(
        degradation.kind,
        ExecuteDegradationKind::ModelExtractionFailure
    );
    assert!(
        matches!(
            details
                .solve_details
                .expect("expected retained SAT solve details")
                .result
                .result(),
            SolveResult::Sat
        ),
        "expected SAT solve result"
    );
    assert!(details.assumption_solve_details.is_none());
}
