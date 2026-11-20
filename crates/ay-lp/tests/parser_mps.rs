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
    assert!(matches!(err, LpError::Parse { line: 5, .. }), "{err:?}");
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
    // The checker's type of a marker column with no BOUNDS entry: binary.
    assert_eq!(p.variables[0].kind, VarKind::Binary);
    assert_eq!((p.variables[0].lower, p.variables[0].upper), (0.0, 1.0));
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

/// A repeated objective entry of a column is refused: the MIPLIB checker
/// keeps the last value, other readers sum (review finding on 200554215).
#[test]
fn test_parse_mps_refuses_repeated_objective_entries() {
    let input = "\
NAME SUMOBJ
ROWS
 N OBJ
 L C1
COLUMNS
    X1 OBJ 1.5 C1 1.0
    X1 OBJ 2.5
RHS
    RHS C1 4.0
ENDATA
";
    assert!(matches!(
        parse_mps(input),
        Err(LpError::Parse { line: 7, .. })
    ));
}

#[test]
fn test_parse_mps_rejects_finite_objective_entries_whose_sum_overflows() {
    let input = "\
NAME BIGOBJ
ROWS
 N OBJ
COLUMNS
    X1 OBJ 1e308
    X1 OBJ 1e308
ENDATA
";
    assert!(matches!(parse_mps(input), Err(LpError::Parse { .. })));
}

#[test]
fn test_parse_mps_normalizes_repeated_constraint_entries_and_rejects_overflow() {
    let finite = "\
NAME SUMROW
ROWS
 N OBJ
 L C1
COLUMNS
    X1 C1 1.5
    X1 C1 2.5
RHS
    RHS C1 4
ENDATA
";
    let problem = parse_mps(finite).expect("parse");
    assert_eq!(problem.constraints[0].coeffs, vec![(0, 4.0)]);

    let overflow = "\
NAME BIGROW
ROWS
 N OBJ
 L C1
COLUMNS
    X1 C1 1e308
    X1 C1 1e308
RHS
    RHS C1 1
ENDATA
";
    assert!(matches!(parse_mps(overflow), Err(LpError::Parse { .. })));
}

#[test]
fn test_parse_mps_rejects_finite_ranges_whose_derived_bound_overflows() {
    for (row_kind, rhs) in [("G", "1e308"), ("L", "-1e308"), ("E", "1e308")] {
        let input = format!(
            "NAME BIGRANGE\nROWS\n N OBJ\n {row_kind} C1\nCOLUMNS\n    X1 C1 1\nRHS\n    RHS C1 {rhs}\nRANGES\n    RNG C1 1e308\nENDATA\n"
        );
        assert!(
            matches!(parse_mps(&input), Err(LpError::Parse { .. })),
            "{row_kind} range overflow must be rejected"
        );
    }
}

fn parse_err_line(input: &str) -> usize {
    match parse_mps(input) {
        Err(LpError::Parse { line, .. }) => line,
        other => panic!("expected a parse refusal, got {other:?}"),
    }
}

/// The MIPLIB checker's default: an integer column of a marker section that
/// no BOUNDS entry touches is in [0, 1]; a bound entry other than `UP 1`
/// first resets its upper bound to +inf.
#[test]
fn test_parse_mps_marker_integer_default_bounds_follow_the_checker() {
    let input = "\
NAME INTB
ROWS
 N OBJ
 L C1
COLUMNS
    M 'MARKER' 'INTORG'
    A OBJ 1 C1 1
    B OBJ 1 C1 1
    C OBJ 1 C1 1
    D OBJ 1 C1 1
    M 'MARKER' 'INTEND'
    E OBJ 1 C1 1
RHS
    RHS C1 3
BOUNDS
 UP BND B 1
 LO BND C 2
 UP BND D 7
ENDATA
";
    let p = parse_mps(input).expect("parse");
    let bounds: Vec<(f64, f64)> = p.variables.iter().map(|v| (v.lower, v.upper)).collect();
    assert_eq!(
        bounds,
        vec![
            (0.0, 1.0),
            (0.0, 1.0),
            (2.0, f64::INFINITY),
            (0.0, 7.0),
            (0.0, f64::INFINITY)
        ]
    );
    let kinds: Vec<VarKind> = p.variables.iter().map(|v| v.kind).collect();
    assert_eq!(
        kinds,
        vec![
            VarKind::Binary,
            VarKind::Binary,
            VarKind::Integer,
            VarKind::Integer,
            VarKind::Continuous
        ]
    );
}

/// Constructs MPS readers disagree on are refused, each at its line.
#[test]
fn test_parse_mps_refuses_what_readers_disagree_on() {
    let head = "NAME R\nROWS\n N OBJ\n L C1\nCOLUMNS\n";
    // Lower-case marker words (the checker ignores the line, others do not).
    assert_eq!(
        parse_err_line(&format!(
            "{head}    M 'MARKER' 'intorg'\n    X OBJ 1 C1 1\nENDATA\n"
        )),
        6
    );
    // Non-contiguous column records.
    assert_eq!(
        parse_err_line(&format!(
            "{head}    XX OBJ 1 C1 1\n    YY OBJ 1 C1 1\n    XX C1 1 C1 1\nENDATA\n"
        )),
        8
    );
    // A second RHS set.
    assert_eq!(
        parse_err_line(&format!(
            "{head}    X OBJ 1 C1 1\nRHS\n    RHS1 C1 1\n    RHS2 C1 2\nENDATA\n"
        )),
        9
    );
    // A second BOUNDS set.
    assert_eq!(
        parse_err_line(&format!(
            "{head}    X OBJ 1 C1 1\nBOUNDS\n UP B1 X 1\n UP B2 X 2\nENDATA\n"
        )),
        9
    );
    // UP below 0 with lower bound 0 (0 in the checker, -inf elsewhere).
    assert_eq!(
        parse_err_line(&format!(
            "{head}    X OBJ 1 C1 1\nBOUNDS\n UP BND X -1\nENDATA\n"
        )),
        8
    );
    // ... accepted once a lower bound other than 0 is given.
    let p = parse_mps(&format!(
        "{head}    X OBJ 1 C1 1\nBOUNDS\n UP BND X -1\n MI BND X\nENDATA\n"
    ))
    .expect("parse");
    assert_eq!(
        (p.variables[0].lower, p.variables[0].upper),
        (f64::NEG_INFINITY, -1.0)
    );
}

/// A column whose name contains MARKER is a column; entries of extra `N`
/// rows are ignored, as in the checker.
#[test]
fn test_parse_mps_marker_named_column_and_free_rows() {
    let input = "\
NAME FREE
ROWS
 N OBJ
 N SPARE
 L C1
COLUMNS
    MARKER1 OBJ 1 C1 1
    MARKER1 SPARE 5
RHS
    RHS C1 3
ENDATA
";
    let p = parse_mps(input).expect("parse");
    assert_eq!(p.variables.len(), 1);
    assert_eq!(p.variables[0].kind, VarKind::Continuous);
    assert_eq!(p.constraints.len(), 1);
    assert_eq!(p.constraints[0].coeffs, vec![(0, 1.0)]);
}
