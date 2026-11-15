// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A theory-`Sat` must come with an assignment / materialised model that
//! satisfies every ASSERTED atom (bounds AND disequalities AND constant
//! atoms). Found by the CHC-COMP 2026 Rung 1 `HornSmt` push/pop fuzz (WP-4):
//! four independent ways `LraSolver` answered `Sat` while its assignment or
//! model violated an asserted atom (fix `fix(lra): four ways a theory-Sat
//! assignment/model violated an asserted atom`). Each test below is the
//! bare-solver shape of one of them; none needs a SAT solver.

use super::*;

fn rat(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

fn is_unsat(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    )
}

fn is_split_request(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedExpressionSplits(_)
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_)
    )
}

/// Defect 3: a CONSTANT equality (`x + 7 = x`, which cancels to `7 = 0`)
/// skipped both bound assertions, so asserting it was a silent no-op and
/// `check` answered `Sat`. It must be a conflict blaming the atom.
#[test]
fn asserted_constant_equality_that_cancels_to_false_is_a_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let seven = terms.mk_rational(rat(7));
    let x_plus_7 = terms.mk_add(vec![x, seven]);
    // Built raw: the shape the CHC converter hands the theory (no folding).
    let eq = terms.mk_app(Symbol::named("="), vec![x, x_plus_7], Sort::Bool);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x = x + 7 is unsatisfiable, got {result:?}"
    );
    if let TheoryResult::Unsat(lits) = &result {
        assert!(
            lits.iter().any(|l| l.term == eq),
            "the conflict blames the atom: {lits:?}"
        );
    }
    if let TheoryResult::UnsatWithFarkas(c) = &result {
        assert!(
            c.literals.iter().any(|l| l.term == eq),
            "the conflict blames the atom: {:?}",
            c.literals
        );
    }

    // Its negation is the tautology `7 != 0`.
    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, false);
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "not (x = x + 7) is valid"
    );
}

/// Defect 4: δ-materialisation considered bounds only. With `x > 2`,
/// `x <= 3`, `2x != 5` the simplex sits at `x = 2 + ε`; the bound slack gives
/// δ = 1/2, i.e. `x = 5/2` — exactly the excluded value.
#[test]
fn materialised_model_avoids_the_roots_of_asserted_disequalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(rat(2));
    let three = terms.mk_rational(rat(3));
    let five = terms.mk_rational(rat(5));
    let x_gt_2 = terms.mk_gt(x, two);
    let x_le_3 = terms.mk_le(x, three);
    let two_x = terms.mk_mul(vec![two, x]);
    let two_x_eq_5 = terms.mk_eq(two_x, five);

    let mut solver = LraSolver::new(&terms);
    for a in [x_gt_2, x_le_3, two_x_eq_5] {
        solver.register_atom(a);
    }
    solver.assert_literal(x_gt_2, true);
    solver.assert_literal(x_le_3, true);
    solver.assert_literal(two_x_eq_5, false);
    let mut result = solver.check();
    // A split request is a legitimate answer; the model is only read on Sat.
    for _ in 0..4 {
        if !is_split_request(&result) {
            break;
        }
        result = solver.check();
    }
    if !matches!(result, TheoryResult::Sat) {
        assert!(
            !is_unsat(&result),
            "x ∈ (2, 3], 2x != 5 is satisfiable, got {result:?}"
        );
        return;
    }
    let v = solver.get_value(x).expect("x has a value");
    assert!(v > rat(2) && v <= rat(3), "bounds hold: x = {v}");
    assert_ne!(
        &v * rat(2),
        rat(5),
        "2x != 5 must hold in the materialised model (x = {v})"
    );
    let model = solver.extract_model();
    if let Some(mv) = model.values.get(&x) {
        assert_ne!(mv * rat(2), rat(5), "extract_model agrees (x = {mv})");
    }
}

/// Defects 1 and 2: the model-seeded propagation probes run AFTER the
/// disequality check and restore only BOUND feasibility. `x <= -4` holds
/// the assignment at -4; the probe of the unasserted `x > -7` asserts
/// `x <= -7` in a temporary scope, and after its pop the restore keeps
/// `x = -7` (within `x <= -4`) — the excluded value of the asserted
/// `not (x = -7)`. Neither the returned verdict nor a follow-up `check()`
/// (the not-dirty cached-`Sat` path) may present that assignment as `Sat`.
#[test]
fn seeded_probe_restore_never_presents_an_excluded_value_as_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let m4 = terms.mk_rational(rat(-4));
    let m7 = terms.mk_rational(rat(-7));
    let x_le_m4 = terms.mk_le(x, m4);
    let x_gt_m7 = terms.mk_gt(x, m7);
    let x_eq_m7 = terms.mk_eq(x, m7);

    let mut solver = LraSolver::new(&terms);
    for a in [x_le_m4, x_gt_m7, x_eq_m7] {
        solver.register_atom(a);
    }
    solver.assert_literal(x_le_m4, true);
    solver.assert_literal(x_eq_m7, false);
    for round in 0..3 {
        let result = solver.check();
        assert!(
            !is_unsat(&result),
            "round {round}: satisfiable, got {result:?}"
        );
        if matches!(result, TheoryResult::Sat) {
            let v = solver.get_value(x).expect("x has a value");
            assert!(v <= rat(-4), "round {round}: x <= -4 holds (x = {v})");
            assert_ne!(
                v,
                rat(-7),
                "round {round}: Sat with the excluded value x = -7"
            );
        }
    }
}
