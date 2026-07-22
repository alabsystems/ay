// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_flatzinc_parser::ast::FznModel;
use ay_fzn2smt::{solve_cp, Fzn2smtError};

fn parse_model(source: &str) -> FznModel {
    ay_flatzinc_parser::parse_flatzinc(source).expect("test FlatZinc should parse")
}

#[test]
fn unsupported_constraints_exposes_unknown_variable_as_typed_error() {
    let model = parse_model(
        r#"
        constraint int_eq(missing_scalar, 1);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("missing scalar should be a typed public error");

    match err {
        Fzn2smtError::UnknownVariable { name } => assert_eq!(name, "missing_scalar"),
        other => panic!("expected UnknownVariable, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_unknown_array_as_typed_error() {
    let model = parse_model(
        r#"
        constraint int_lin_eq([1], missing_array, 0);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("missing array should be a typed public error");

    match err {
        Fzn2smtError::UnknownArray { name } => assert_eq!(name, "missing_array"),
        other => panic!("expected UnknownArray, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_set_identifier_shape_as_typed_error() {
    let model = parse_model(
        r#"
        constraint set_card(1, 0);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("non-identifier set argument should be a typed public error");

    match err {
        Fzn2smtError::ExpectedSetVariableIdentifier { constraint } => {
            assert_eq!(constraint, "set_card");
        }
        other => panic!("expected ExpectedSetVariableIdentifier, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_unknown_set_array_as_typed_error() {
    let model = parse_model(
        r#"
        var set of 1..2: result_set;
        constraint array_set_element(1, missing_sets, result_set);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("missing set array should be a typed public error");

    match err {
        Fzn2smtError::UnknownSetArray { constraint, name } => {
            assert_eq!(constraint, "array_set_element");
            assert_eq!(name, "missing_sets");
        }
        other => panic!("expected UnknownSetArray, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_inverse_length_mismatch_as_typed_error() {
    let model = parse_model(
        r#"
        var 1..2: x1;
        var 1..2: x2;
        var 1..1: y1;
        constraint inverse([x1, x2], [y1]);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("inverse length mismatch should be a typed public error");

    match err {
        Fzn2smtError::InverseArrayLengthMismatch { left, right } => {
            assert_eq!(left, 2);
            assert_eq!(right, 1);
        }
        other => panic!("expected InverseArrayLengthMismatch, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_global_cardinality_length_mismatch_as_typed_error() {
    let model = parse_model(
        r#"
        var 1..2: x;
        var 0..1: c;
        constraint fzn_global_cardinality([x], [1, 2], [c]);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("global_cardinality length mismatch should be a typed public error");

    match err {
        Fzn2smtError::GlobalCardinalityLengthMismatch { cover, counts } => {
            assert_eq!(cover, 2);
            assert_eq!(counts, 1);
        }
        other => panic!("expected GlobalCardinalityLengthMismatch, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_table_tuple_length_mismatch_as_typed_error() {
    let model = parse_model(
        r#"
        var 1..3: x;
        var 1..3: y;
        constraint table_int([x, y], [1, 2, 3]);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("table_int tuple length mismatch should be a typed public error");

    match err {
        Fzn2smtError::TableTupleLengthMismatch { values, arity } => {
            assert_eq!(values, 3);
            assert_eq!(arity, 2);
        }
        other => panic!("expected TableTupleLengthMismatch, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_cumulative_array_length_mismatch_as_typed_error() {
    let model = parse_model(
        r#"
        var 0..5: s;
        constraint fzn_cumulative([s], [1, 2], [1], 2);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("cumulative length mismatch should be a typed public error");

    match err {
        Fzn2smtError::CumulativeArrayLengthMismatch {
            starts,
            durations,
            resources,
        } => {
            assert_eq!(starts, 1);
            assert_eq!(durations, 2);
            assert_eq!(resources, 1);
        }
        other => panic!("expected CumulativeArrayLengthMismatch, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_diffn_array_length_mismatch_as_typed_error() {
    let model = parse_model(
        r#"
        var 0..5: x;
        var 0..5: y;
        constraint fzn_diffn([x], [y], [1, 2], [1]);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("diffn length mismatch should be a typed public error");

    match err {
        Fzn2smtError::DiffnArrayLengthMismatch { x, y, dx, dy } => {
            assert_eq!(x, 1);
            assert_eq!(y, 1);
            assert_eq!(dx, 2);
            assert_eq!(dy, 1);
        }
        other => panic!("expected DiffnArrayLengthMismatch, got {other:?}"),
    }
}

#[test]
fn unsupported_constraints_exposes_array_element_empty_array_as_typed_error() {
    let model = parse_model(
        r#"
        var 1..1: idx;
        var 0..1: val;
        constraint array_int_element(idx, [], val);
        solve satisfy;
        "#,
    );

    let err = solve_cp::unsupported_constraints(&model)
        .expect_err("array_int_element empty array should be a typed public error");

    match err {
        Fzn2smtError::ArrayElementEmptyArray { constraint } => {
            assert_eq!(constraint, "array_int_element");
        }
        other => panic!("expected ArrayElementEmptyArray, got {other:?}"),
    }
}

#[test]
fn public_result_alias_uses_fzn2smt_error() {
    fn assert_public_result_type(
        result: ay_fzn2smt::Result<Vec<String>>,
    ) -> Result<Vec<String>, Fzn2smtError> {
        result
    }

    let model = parse_model("solve satisfy;");
    let unsupported = assert_public_result_type(solve_cp::unsupported_constraints(&model))
        .expect("empty model should have no unsupported constraints");

    assert!(unsupported.is_empty());
}
