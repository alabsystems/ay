// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for ordering and counting constraints: lex_lesseq_int, lex_less_int,
// set_le, count_eq with optimization. Split from tests.rs for file size.

use ay_cp::engine::CpSolveResult;

use super::tests::{parse_and_solve, solve_cp_output};

// ── Lex constraint soundness tests (Part of #6120) ──────────────────

/// lex_lesseq: [3, 5] ≤_lex [3, 2] should be UNSAT.
/// First positions equal (3 == 3), second position 5 > 2 violates lex order.
/// Bug: half-reified chain indicators allow solver to set chain=0 even when
/// positions are equal, making the constraint for position 1 vacuous.
#[test]
fn test_lex_lesseq_equal_prefix_violation() {
    let fzn = "\
        var 3..3: x1 :: output_var;\n\
        var 5..5: x2 :: output_var;\n\
        var 3..3: y1 :: output_var;\n\
        var 2..2: y2 :: output_var;\n\
        constraint fzn_lex_lesseq_int([x1, x2], [y1, y2]);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat ([3,5] is not ≤_lex [3,2]), got {other:?}"),
    }
}

/// lex_lesseq: [3, 2] ≤_lex [3, 5] should be SAT.
/// First positions equal (3 == 3), second position 2 <= 5.
#[test]
fn test_lex_lesseq_equal_prefix_valid() {
    let fzn = "\
        var 3..3: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 3..3: y1 :: output_var;\n\
        var 5..5: y2 :: output_var;\n\
        constraint fzn_lex_lesseq_int([x1, x2], [y1, y2]);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat ([3,2] ≤_lex [3,5]), got {other:?}"),
    }
}

/// lex_lesseq: 3-element case with equal prefix length 2.
/// [3, 3, 5] ≤_lex [3, 3, 2] should be UNSAT.
#[test]
fn test_lex_lesseq_three_element_equal_prefix() {
    let fzn = "\
        var 3..3: x1 :: output_var;\n\
        var 3..3: x2 :: output_var;\n\
        var 5..5: x3 :: output_var;\n\
        var 3..3: y1 :: output_var;\n\
        var 3..3: y2 :: output_var;\n\
        var 2..2: y3 :: output_var;\n\
        constraint fzn_lex_lesseq_int([x1, x2, x3], [y1, y2, y3]);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat ([3,3,5] is not ≤_lex [3,3,2]), got {other:?}"),
    }
}

/// lex_less: [3, 2] <_lex [3, 5] should be SAT.
/// First positions equal, then 2 < 5.
#[test]
fn test_lex_less_equal_prefix_valid() {
    let fzn = "\
        var 3..3: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 3..3: y1 :: output_var;\n\
        var 5..5: y2 :: output_var;\n\
        constraint fzn_lex_less_int([x1, x2], [y1, y2]);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat ([3,2] <_lex [3,5]), got {other:?}"),
    }
}

/// lex_less: [3, 3] <_lex [3, 3] should be UNSAT (equal, not strictly less).
#[test]
fn test_lex_less_equal_arrays_unsat() {
    let fzn = "\
        var 3..3: x1 :: output_var;\n\
        var 3..3: x2 :: output_var;\n\
        var 3..3: y1 :: output_var;\n\
        var 3..3: y2 :: output_var;\n\
        constraint fzn_lex_less_int([x1, x2], [y1, y2]);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat ([3,3] is not <_lex [3,3]), got {other:?}"),
    }
}

/// lex_less: [3, 5] <_lex [3, 2] should be UNSAT.
/// First positions equal, then 5 > 2.
#[test]
fn test_lex_less_equal_prefix_violation() {
    let fzn = "\
        var 3..3: x1 :: output_var;\n\
        var 5..5: x2 :: output_var;\n\
        var 3..3: y1 :: output_var;\n\
        var 2..2: y2 :: output_var;\n\
        constraint fzn_lex_less_int([x1, x2], [y1, y2]);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat ([3,5] is not <_lex [3,2]), got {other:?}"),
    }
}

// ── set_le soundness tests (half-reification fix) ────────────────────

/// set_le: S1={1,3} ≤ S2={1,2} should be UNSAT.
/// Indicator arrays: S1=[1,0,1], S2=[1,1,0].
/// set_le(S1,S2) encodes lex_lesseq(ind(S2), ind(S1)) = [1,1,0] ≤_lex [1,0,1].
/// Position 0: equal (1==1), Position 1: 1 > 0 violates lex order.
/// Bug: half-reified chain indicators allow solver to set chain=0 even when
/// position 0 is equal, making the constraint for position 1 vacuous → false SAT.
#[test]
fn test_set_le_equal_prefix_violation() {
    let fzn = "\
        var set of 1..3: s1;\n\
        var set of 1..3: s2;\n\
        var 1..1: c1;\n\
        var 3..3: c3;\n\
        var 1..1: d1;\n\
        var 2..2: d2;\n\
        constraint set_in(c1, s1);\n\
        constraint set_in(c3, s1);\n\
        constraint set_card(s1, 2);\n\
        constraint set_in(d1, s2);\n\
        constraint set_in(d2, s2);\n\
        constraint set_card(s2, 2);\n\
        constraint set_le(s1, s2);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat ({{1,3}} is not ≤ {{1,2}} in set ordering), got {other:?}"),
    }
}

/// set_le: S1={1,2} ≤ S2={1,3} should be SAT.
/// Indicator arrays: S1=[1,1,0], S2=[1,0,1].
/// set_le(S1,S2) encodes lex_lesseq(ind(S2), ind(S1)) = [1,0,1] ≤_lex [1,1,0].
/// Position 0: equal (1==1), Position 1: 0 ≤ 1 → SAT.
#[test]
fn test_set_le_equal_prefix_valid() {
    let fzn = "\
        var set of 1..3: s1;\n\
        var set of 1..3: s2;\n\
        var 1..1: c1;\n\
        var 2..2: c2;\n\
        var 1..1: d1;\n\
        var 3..3: d3;\n\
        constraint set_in(c1, s1);\n\
        constraint set_in(c2, s1);\n\
        constraint set_card(s1, 2);\n\
        constraint set_in(d1, s2);\n\
        constraint set_in(d3, s2);\n\
        constraint set_card(s2, 2);\n\
        constraint set_le(s1, s2);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat ({{1,2}} ≤ {{1,3}} in set ordering), got {other:?}"),
    }
}

/// set_le: 5-element domain with 2-position equal prefix then violation.
/// S1={1,2,5}, S2={1,2,4} over domain 1..5.
/// Indicators: S1=[1,1,0,0,1], S2=[1,1,0,1,0].
/// lex_lesseq(ind(S2), ind(S1)) = [1,1,0,1,0] ≤_lex [1,1,0,0,1].
/// Positions 0,1,2: all equal, Position 3: 1 > 0 → UNSAT.
/// Tests that chain equality propagates correctly through multiple positions.
#[test]
fn test_set_le_three_position_equal_prefix() {
    let fzn = "\
        var set of 1..5: s1;\n\
        var set of 1..5: s2;\n\
        var 1..1: a1;\n\
        var 2..2: a2;\n\
        var 5..5: a5;\n\
        var 1..1: b1;\n\
        var 2..2: b2;\n\
        var 4..4: b4;\n\
        constraint set_in(a1, s1);\n\
        constraint set_in(a2, s1);\n\
        constraint set_in(a5, s1);\n\
        constraint set_card(s1, 3);\n\
        constraint set_in(b1, s2);\n\
        constraint set_in(b2, s2);\n\
        constraint set_in(b4, s2);\n\
        constraint set_card(s2, 3);\n\
        constraint set_le(s1, s2);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => {
            panic!("expected Unsat ({{1,2,5}} is not ≤ {{1,2,4}} in set ordering), got {other:?}")
        }
    }
}

// ── count_eq soundness tests ─────────────────────────────────────────

/// count_eq with variable y: xs = [1, 2, 3, 2, 1], y in [1..3], count = obj.
/// For y=1: count=2, y=2: count=2, y=3: count=1.
/// Force obj=2: satisfiable with y=1 or y=2.
#[test]
fn test_count_eq_variable_y() {
    let fzn = "\
        var 1..1: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 3..3: x3 :: output_var;\n\
        var 2..2: x4 :: output_var;\n\
        var 1..1: x5 :: output_var;\n\
        var 1..3: y :: output_var;\n\
        var 0..5: obj :: output_var;\n\
        array [1..5] of var int: xs = [x1, x2, x3, x4, x5];\n\
        constraint fzn_count_eq(xs, y, obj);\n\
        constraint int_eq(obj, 2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(!output.contains("UNSATISFIABLE"), "should be SAT: {output}");
    // y must be 1 or 2 (the values with count=2)
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("y = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                let y: i64 = val_str.parse().unwrap();
                assert!(y == 1 || y == 2, "y must be 1 or 2 for count=2, got y={y}");
            }
        }
    }
}

/// Regression test for #6119 Pattern 1: count_eq with asymmetric domains
/// causing false UNSAT in optimization problems.
///
/// This test mimics the peaceable_queens pattern: maximize the count of
/// elements matching a value from a different domain range. The count_eq
/// sign error (d = y-xi had domain of xi-y) caused immediate false UNSAT
/// during root propagation when domains were asymmetric.
#[test]
fn test_maximize_count_eq_asymmetric_domains() {
    // xs[i] in [5..8], y in [1..8], maximize count(xs[i] == y).
    // With y free, solver can set y=5,6,7,8 to match xs elements.
    // Optimal: y=5 (or 6,7,8), count=3 since all xs can equal y.
    let fzn = "\
        var 5..8: x1 :: output_var;\n\
        var 5..8: x2 :: output_var;\n\
        var 5..8: x3 :: output_var;\n\
        var 1..8: y :: output_var;\n\
        var 0..3: cnt :: output_var;\n\
        constraint fzn_count_eq([x1, x2, x3], y, cnt);\n\
        solve maximize cnt;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal, not false UNSAT: {output}"
    );
    // Optimal count should be 3 (all xs can equal y when y is in [5..8])
    let mut last_cnt = None;
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("cnt = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                last_cnt = Some(val_str.parse::<i64>().unwrap());
            }
        }
    }
    assert_eq!(
        last_cnt,
        Some(3),
        "optimal count should be 3, output:\n{output}"
    );
}
