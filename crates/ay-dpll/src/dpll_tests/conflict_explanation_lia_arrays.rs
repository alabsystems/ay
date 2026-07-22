// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gap 11: Theory conflict explanation soundness — LIA and Arrays.
//!
//! When a theory reports a conflict, the explanation literals should
//! logically imply the conflict.

use super::*;

/// Gap 11: LIA Conflict Explanation Soundness
///
/// When LIA reports a conflict (specifically for integer-infeasibility),
/// the explanation literals should be sufficient to cause the conflict.
#[test]
fn test_lia_conflict_explanation_soundness_gap11() {
    use ay_lia::LiaSolver;

    // Test that LIA produces sound explanations for integer conflicts.
    // Set up: x >= 5 ∧ x <= 3 where x is an integer is UNSAT
    // (inherited from LRA relaxation conflict)

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let three = terms.mk_int(3.into());

    // x >= 5 is (>= x 5)
    let ge_5 = terms.mk_app(Symbol::Named(">=".to_string()), vec![x, five], Sort::Bool);
    // x <= 3 is (<= x 3)
    let le_3 = terms.mk_app(Symbol::Named("<=".to_string()), vec![x, three], Sort::Bool);

    // Create LIA solver and assert literals
    let mut lia = LiaSolver::new(&terms);

    // Assert: x >= 5, x <= 3
    lia.assert_literal(ge_5, true);
    lia.assert_literal(le_3, true);

    // Check should return Unsat (conflict from LRA relaxation)
    let result = lia.check();
    match result {
        TheoryResult::Unsat(explanation) => {
            // Explanation should contain the conflicting bound atoms
            assert!(
                !explanation.is_empty(),
                "LIA conflict explanation is empty - soundness violation"
            );

            // Soundness verification: re-solve with only explanation literals
            let mut lia2 = LiaSolver::new(&terms);
            for lit in &explanation {
                lia2.assert_literal(lit.term, lit.value);
            }
            let result2 = lia2.check();
            assert!(
                matches!(result2, TheoryResult::Unsat(_)),
                "LIA explanation is not sound: re-asserting explanation literals did not cause conflict"
            );
        }
        TheoryResult::Sat => {
            panic!("LIA should find conflict for x >= 5 ∧ x <= 3");
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            // Same handling as Unsat
            assert!(
                !conflict.literals.is_empty(),
                "LIA conflict explanation is empty - soundness violation"
            );
            let mut lia2 = LiaSolver::new(&terms);
            for lit in &conflict.literals {
                lia2.assert_literal(lit.term, lit.value);
            }
            let result2 = lia2.check();
            assert!(
                matches!(result2, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
                "LIA explanation is not sound: re-asserting explanation literals did not cause conflict"
            );
        }
        other => {
            panic!("LIA should detect x >= 5 ∧ x <= 3 as Unsat, got {other:?}");
        }
    }
}

/// Gap 11: LIA Integer-Specific Conflict Explanation
///
/// Test LIA explanation for integer-specific conflicts (no real solution in range).
/// For integer x: x > 5 ∧ x < 6 is UNSAT (no integer between 5 and 6).
#[test]
fn test_lia_integer_bounds_conflict_explanation_gap11() {
    use ay_lia::LiaSolver;

    // For an integer variable x:
    // x > 5 means x >= 6 (next integer)
    // x < 6 means x <= 5 (previous integer)
    // Together: x >= 6 and x <= 5 is UNSAT

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let six = terms.mk_int(6.into());

    // x > 5 is (> x 5)
    let gt_5 = terms.mk_app(Symbol::Named(">".to_string()), vec![x, five], Sort::Bool);
    // x < 6 is (< x 6)
    let lt_6 = terms.mk_app(Symbol::Named("<".to_string()), vec![x, six], Sort::Bool);

    let mut lia = LiaSolver::new(&terms);

    // Assert: x > 5, x < 6
    lia.assert_literal(gt_5, true);
    lia.assert_literal(lt_6, true);

    // Check should return Unsat (no integer satisfies both)
    let result = lia.check();
    match result {
        TheoryResult::Unsat(explanation) => {
            // Explanation should be non-empty
            assert!(
                !explanation.is_empty(),
                "LIA integer bounds conflict explanation is empty"
            );

            // Verify soundness
            let mut lia2 = LiaSolver::new(&terms);
            for lit in &explanation {
                lia2.assert_literal(lit.term, lit.value);
            }
            let result2 = lia2.check();
            assert!(
                matches!(result2, TheoryResult::Unsat(_)),
                "LIA integer bounds explanation is not sound"
            );
        }
        TheoryResult::Sat => {
            panic!("LIA should find conflict for x > 5 ∧ x < 6 (no integer in range)");
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            // Same handling as Unsat
            assert!(
                !conflict.literals.is_empty(),
                "LIA integer bounds conflict explanation is empty"
            );
            let mut lia2 = LiaSolver::new(&terms);
            for lit in &conflict.literals {
                lia2.assert_literal(lit.term, lit.value);
            }
            let result2 = lia2.check();
            assert!(
                matches!(
                    result2,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                ),
                "LIA integer bounds explanation is not sound"
            );
        }
        other => {
            panic!("LIA should detect x > 5 ∧ x < 6 (no integer in range) as Unsat, got {other:?}");
        }
    }
}

/// Gap 11: Arrays ROW1 Conflict Explanation Soundness
///
/// When Arrays reports a conflict for ROW1 violation (read-over-write axiom 1),
/// the explanation should be sufficient to cause the conflict.
#[test]
fn test_arrays_row1_conflict_explanation_soundness_gap11() {
    use ay_arrays::ArraySolver;

    // ROW1: select(store(a, i, v), j) = v when i = j
    // Conflict: Assert i = j AND select(store(a, i, v), j) ≠ v
    //
    // We use different index variables (i, j) and assert i = j explicitly,
    // because the solver's known_equal() needs to track equalities.

    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int); // Different index variable
    let v = terms.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j)
    let stored = terms.mk_store(a, i, v);
    let selected = terms.mk_select(stored, j);

    // Create equalities
    let eq_ij = terms.mk_eq(i, j); // i = j
    let eq_sel_v = terms.mk_eq(selected, v); // select(store(a,i,v), j) = v

    let mut solver = ArraySolver::new(&terms);

    // Assert i = j (so ROW1 applies)
    solver.assert_literal(eq_ij, true);
    // Assert select(store(a, i, v), j) ≠ v (violates ROW1 when i=j)
    solver.assert_literal(eq_sel_v, false);

    // ROW1 now emits NeedLemmas instead of direct Unsat (#6743)
    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("Arrays ROW1 should emit NeedLemmas for i=j ∧ select(store(a,i,v),j) ≠ v");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW1 lemma clause");
    assert!(
        !lemmas[0].clause.is_empty(),
        "Arrays ROW1 lemma clause must not be empty"
    );
    // Lemma clause is the negated conflict: at least one reason must be violated
    // for the theory state to be consistent. Verify the diseq term appears negated.
    assert!(
        lemmas[0]
            .clause
            .iter()
            .any(|lit| lit.term == eq_sel_v && lit.value),
        "ROW1 lemma must include eq_sel_v=true (negated diseq)"
    );
}

/// Gap 11: Arrays ROW2 Conflict Explanation Soundness
///
/// When Arrays reports a conflict for ROW2 violation (read-over-write axiom 2),
/// the explanation should be sufficient to cause the conflict.
#[test]
fn test_arrays_row2_conflict_explanation_soundness_gap11() {
    use ay_arrays::ArraySolver;

    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("a", arr_sort);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let stored = terms.mk_store(a, i, v);
    let sel_stored_j = terms.mk_select(stored, j);
    let sel_a_j = terms.mk_select(a, j);
    let eq_ij = terms.mk_eq(i, j);
    let eq_sels = terms.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&terms);
    solver.assert_literal(eq_ij, false); // i ≠ j
    solver.assert_literal(eq_sels, false); // violates ROW2

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::NeedLemmas(_)),
        "Arrays should request the ROW2 lemma for i≠j ∧ select(store(a,i,v),j) ≠ select(a,j), got {result:?}"
    );
    let TheoryResult::NeedLemmas(lemmas) = result else {
        unreachable!("assert above guarantees NeedLemmas");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW2 lemma clause");
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sels, true)],
        "ROW2 lemma must assert i=j or select(store(a,i,v),j)=select(a,j)"
    );
}

/// Gap 11: Arrays Explanation Minimality
///
/// Test that Arrays explanations don't include irrelevant literals.
#[test]
fn test_arrays_explanation_minimality_gap11() {
    use ay_arrays::ArraySolver;

    // Set up ROW1 conflict with an irrelevant assertion
    // Use different index variables (i, j) and assert i = j explicitly.
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort); // Irrelevant array
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int); // Different index variable
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int); // Irrelevant value

    // Create store(a, i, v) and select(store(a, i, v), j)
    let stored = terms.mk_store(a, i, v);
    let selected = terms.mk_select(stored, j);

    // Irrelevant: select(b, i) = w (has nothing to do with the conflict)
    let sel_b = terms.mk_select(b, i);
    let eq_sel_b_w = terms.mk_eq(sel_b, w);

    // Relevant equalities
    let eq_ij = terms.mk_eq(i, j); // i = j
    let eq_sel_v = terms.mk_eq(selected, v); // select(store(a,i,v), j) = v

    let mut solver = ArraySolver::new(&terms);

    // Assert irrelevant fact
    solver.assert_literal(eq_sel_b_w, true);
    // Assert i = j (so ROW1 applies)
    solver.assert_literal(eq_ij, true);
    // Assert the conflict: select(store(a, i, v), j) ≠ v
    solver.assert_literal(eq_sel_v, false);

    // ROW1 now emits NeedLemmas instead of direct Unsat (#6743)
    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("Arrays ROW1 minimality test should emit NeedLemmas");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW1 lemma clause");
    // Lemma clause should NOT include the irrelevant eq_sel_b_w
    let contains_irrelevant = lemmas[0].clause.iter().any(|lit| lit.term == eq_sel_b_w);
    assert!(
        !contains_irrelevant,
        "Arrays lemma includes irrelevant constraint - minimality violation"
    );
}
