// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ─── parse_cnf tests ───────────────────────────────────────────

#[test]
fn test_parse_simple_cnf() {
    let input = b"c comment\np cnf 3 2\n1 -2 0\n2 3 0\n";
    let cnf = parse_cnf(&input[..]).unwrap();
    assert_eq!(cnf.num_vars, 3);
    assert_eq!(cnf.clauses.len(), 2);
    assert_eq!(cnf.clauses[0].len(), 2);
    assert_eq!(cnf.clauses[0][0].to_dimacs(), 1);
    assert_eq!(cnf.clauses[0][1].to_dimacs(), -2);
}

#[test]
fn test_parse_multiline_clause() {
    let input = b"p cnf 2 1\n1 2\n0\n";
    let cnf = parse_cnf(&input[..]).unwrap();
    assert_eq!(cnf.clauses.len(), 1);
    assert_eq!(cnf.clauses[0].len(), 2);
}

#[test]
fn test_parse_empty_clause() {
    let input = b"p cnf 2 3\n1 0\n-1 0\n0\n";
    let cnf = parse_cnf(&input[..]).unwrap();
    assert_eq!(cnf.clauses.len(), 3);
    assert!(cnf.clauses[2].is_empty());
}

#[test]
fn test_parse_error_no_header() {
    let input = b"1 2 0\n";
    assert!(parse_cnf(&input[..]).is_err());
}

#[test]
fn test_parse_multiple_clauses_on_one_line() {
    let input = b"p cnf 3 3\n1 2 0 -1 3 0 -2 -3 0\n";
    let cnf = parse_cnf(&input[..]).unwrap();
    assert_eq!(cnf.clauses.len(), 3);
    assert_eq!(cnf.clauses[0][0].to_dimacs(), 1);
    assert_eq!(cnf.clauses[1][0].to_dimacs(), -1);
    assert_eq!(cnf.clauses[2][0].to_dimacs(), -2);
}

/// parse_cnf rejects literals exceeding the declared variable count.
#[test]
fn test_parse_cnf_rejects_out_of_range_literal() {
    let input = b"p cnf 2 1\n10 0\n";
    let result = parse_cnf(&input[..]);
    assert!(
        result.is_err(),
        "literal 10 should be rejected with num_vars=2"
    );
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("exceeds declared variable count"));
}

/// parse_cnf now also rejects duplicate problem lines (unified behavior).
#[test]
fn test_parse_cnf_duplicate_problem_line() {
    let input = b"p cnf 2 1\np cnf 3 2\n1 2 0\n";
    let err = parse_cnf(&input[..]).unwrap_err();
    assert!(err.to_string().contains("duplicate"), "got: {err}");
}

// ─── parse_cnf_with_ids tests ──────────────────────────────────

#[test]
fn test_parse_with_ids_simple() {
    let input = b"c comment\np cnf 3 2\n1 -2 0\n2 3 0\n";
    let cnf = parse_cnf_with_ids(&input[..]).unwrap();
    assert_eq!(cnf.num_vars, 3);
    assert_eq!(cnf.clauses.len(), 2);
    assert_eq!(cnf.clauses[0].0, 1); // first clause ID = 1
    assert_eq!(cnf.clauses[1].0, 2); // second clause ID = 2
    assert_eq!(cnf.clauses[0].1[0].to_dimacs(), 1);
    assert_eq!(cnf.clauses[0].1[1].to_dimacs(), -2);
}

#[test]
fn test_parse_with_ids_sequential() {
    let input = b"p cnf 3 4\n1 2 0\n-1 3 0\n2 -3 0\n-2 -3 0\n";
    let cnf = parse_cnf_with_ids(&input[..]).unwrap();
    assert_eq!(cnf.clauses.len(), 4);
    for (i, (id, _)) in cnf.clauses.iter().enumerate() {
        assert_eq!(*id, (i + 1) as u64);
    }
}

#[test]
fn test_parse_with_ids_empty_clause() {
    let input = b"p cnf 2 3\n1 0\n0\n-1 0\n";
    let cnf = parse_cnf_with_ids(&input[..]).unwrap();
    assert_eq!(cnf.clauses.len(), 3);
    assert_eq!(cnf.clauses[0].0, 1);
    assert_eq!(cnf.clauses[1].0, 2);
    assert!(cnf.clauses[1].1.is_empty()); // empty clause
    assert_eq!(cnf.clauses[2].0, 3);
}

#[test]
fn test_parse_with_ids_duplicate_header_rejected() {
    let input = b"p cnf 2 1\np cnf 3 2\n1 2 0\n";
    let err = parse_cnf_with_ids(&input[..]).unwrap_err();
    assert!(err.to_string().contains("duplicate"), "got: {err}");
}

#[test]
fn test_parse_with_ids_trailing_clause() {
    let input = b"p cnf 2 1\n1 2\n";
    let cnf = parse_cnf_with_ids(&input[..]).unwrap();
    assert_eq!(cnf.clauses.len(), 1);
    assert_eq!(cnf.clauses[0].0, 1);
    assert_eq!(
        cnf.clauses[0].1,
        vec![Literal::from_dimacs(1), Literal::from_dimacs(2)]
    );
}

#[test]
fn test_parse_with_ids_out_of_range_rejected() {
    let input = b"p cnf 2 1\n10 0\n";
    let result = parse_cnf_with_ids(&input[..]);
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("exceeds declared variable count"));
}
