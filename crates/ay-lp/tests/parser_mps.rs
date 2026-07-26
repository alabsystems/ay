// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MPS parser unit tests, kept as an integration test file so
//! `crates/ay-lp/src/parser/mps.rs` stays under the 500-line module budget.

use ay_lp::{parse_mps, LpError, RowKind, Sense, VarKind};

#[test]
fn test_parse_mps_trivial_minimize() {
    let input = "\
NAME          TRIVIAL
ROWS
 N  COST
 L  C1
COLUMNS
    X1        COST         1.0   C1           1.0
    X2        COST         1.0   C1           1.0
RHS
    RHS       C1           2.0
BOUNDS
ENDATA
";
    let p = parse_mps(input).expect("parse");
    assert_eq!(p.name, "TRIVIAL");
    assert_eq!(p.sense, Sense::Min);
    assert_eq!(p.variables.len(), 2);
    assert_eq!(p.constraints.len(), 1);
    assert_eq!(p.constraints[0].kind, RowKind::Le);
    assert_eq!(p.constraints[0].rhs, 2.0);
}

#[test]
fn test_parse_mps_rejects_duplicate_row() {
    let input = "\
NAME T
ROWS
 N OBJ
 L C1
 L C1
COLUMNS
RHS
ENDATA
";
    let err = parse_mps(input).unwrap_err();
    assert!(matches!(err, LpError::InvalidInstance(_)));
}

#[test]
fn test_parse_mps_bounds_binary() {
    let input = "\
NAME BV
ROWS
 N OBJ
 L C1
COLUMNS
    X1 OBJ 1.0 C1 1.0
RHS
    RHS C1 1.0
BOUNDS
 BV BND X1
ENDATA
";
    let p = parse_mps(input).expect("parse");
    assert_eq!(p.variables[0].kind, VarKind::Binary);
    assert_eq!(p.variables[0].upper, 1.0);
    assert_eq!(p.variables[0].lower, 0.0);
}

#[test]
fn test_parse_mps_integer_marker() {
    let input = "\
NAME INT
ROWS
 N OBJ
 L C1
COLUMNS
    MARKER1 'MARKER' 'INTORG'
    X1 OBJ 1.0 C1 1.0
    MARKER2 'MARKER' 'INTEND'
    X2 OBJ 1.0 C1 1.0
RHS
    RHS C1 3.0
ENDATA
";
    let p = parse_mps(input).expect("parse");
    assert_eq!(p.variables[0].kind, VarKind::Integer);
    assert_eq!(p.variables[1].kind, VarKind::Continuous);
}

#[test]
fn test_parse_mps_objsense_max() {
    let input = "\
NAME MAX
OBJSENSE
    MAX
ROWS
 N OBJ
 L C1
COLUMNS
    X1 OBJ 1.0 C1 1.0
RHS
    RHS C1 5.0
ENDATA
";
    let p = parse_mps(input).expect("parse");
    assert_eq!(p.sense, Sense::Max);
}

#[test]
fn test_parse_mps_rejects_non_finite_numeric_fields() {
    let input = "\
NAME INF
ROWS
 N OBJ
 L C1
COLUMNS
    X1 OBJ 1e999 C1 1.0
RHS
    RHS C1 1.0
ENDATA
";
    assert!(matches!(
        parse_mps(input),
        Err(LpError::InvalidNumber { .. })
    ));

    let input = "\
NAME INF
ROWS
 N OBJ
 L C1
COLUMNS
    X1 OBJ 1.0 C1 1.0
RHS
    RHS C1 1e999
ENDATA
";
    assert!(matches!(
        parse_mps(input),
        Err(LpError::InvalidNumber { .. })
    ));
}
