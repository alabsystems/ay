// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test the three cases of failing_analysis:
/// Case 1: assumption falsified at level 0 by unit propagation.
#[test]
fn test_failing_analysis_unit_level_falsification() {
    let mut k = Kitten::new();
    // Unit clause forces x1=true at level 0.
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    // Binary to propagate x2=true at level 0.
    k.add_clause_with_id(1, &[ext_lit(-1), ext_lit(2)], INVALID);
    k.seal_original();

    // Assume ¬x2: falsified at level 0 (unit propagation forces x2=true).
    k.assume(ext_lit(-2));
    assert_eq!(k.solve(), 20, "¬x2 should be UNSAT (x2 forced at level 0)");
}

/// Test the three cases of failing_analysis:
/// Case 2: assumption clashes with another assumption.
#[test]
fn test_failing_analysis_clashing_assumptions() {
    let mut k = Kitten::new();
    // Minimal formula — just need variables to exist.
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(-1)], INVALID); // tautology
    k.seal_original();

    // Assume x1 and ¬x1 — direct clash.
    k.assume(ext_lit(1));
    k.assume(ext_lit(-1));
    assert_eq!(
        k.solve(),
        20,
        "x1 ∧ ¬x1 should be UNSAT (clashing assumptions)"
    );
}

/// Test the three cases of failing_analysis:
/// Case 3: general failure — assumption falsified by propagation at non-zero level.
#[test]
fn test_failing_analysis_general_propagation() {
    let mut k = Kitten::new();
    // (x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (¬x2 ∨ x3) ∧ (¬x3)
    // Under assumption x1: propagation forces x2=true → x3=true, but ¬x3 clause
    // makes x3=false at level 0. So assumption x1 leads to a contradiction
    // through propagation.
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(2)], INVALID);
    k.add_clause_with_id(1, &[ext_lit(-1), ext_lit(2)], INVALID);
    k.add_clause_with_id(2, &[ext_lit(-2), ext_lit(3)], INVALID);
    k.add_clause_with_id(3, &[ext_lit(-3)], INVALID);
    k.seal_original();

    // x2 is forced true by resolution of clauses 0 and 1.
    // Then x3 is forced true by clause 2, but clause 3 forces x3 false.
    // This is actually unconditionally UNSAT.
    assert_eq!(k.solve(), 20, "formula should be UNSAT");

    // With assumptions it should also be UNSAT.
    k.assume(ext_lit(1));
    assert_eq!(k.solve(), 20, "UNSAT formula stays UNSAT under assumptions");
}
