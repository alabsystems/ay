// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheoryConflict;
use num_rational::Rational64;

#[derive(Debug)]
struct LeZeroConstraint {
    expr: LinearExpr,
    strict: bool,
}

fn tableau_conflict_fixture() -> (TermStore, TheoryConflict, Vec<TheoryLit>) {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let six = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_10 = terms.mk_le(sum, ten);
    let x_ge_5 = terms.mk_ge(x, five);
    let y_ge_6 = terms.mk_ge(y, six);

    let expected = vec![
        TheoryLit::new(sum_le_10, true),
        TheoryLit::new(x_ge_5, true),
        TheoryLit::new(y_ge_6, true),
    ];

    let mut solver = LraSolver::new(&terms);
    for lit in &expected {
        solver.assert_literal(lit.term, lit.value);
    }

    let result = solver.check();
    let conflict = match result {
        TheoryResult::UnsatWithFarkas(conflict) => conflict,
        other => panic!("expected tableau UNSAT with Farkas annotation, got {other:?}"),
    };

    (terms, conflict, expected)
}

fn rational64_to_big(coeff: Rational64) -> BigRational {
    BigRational::new(BigInt::from(*coeff.numer()), BigInt::from(*coeff.denom()))
}

fn normalize_to_le_zero(parser: &mut LraSolver, lit: TheoryLit) -> LeZeroConstraint {
    match parser.terms().get(lit.term) {
        TermData::App(Symbol::Named(name), _) if name == "=" || name == "distinct" => {
            panic!("test helper only supports inequality reasons, got {name} for {lit:?}")
        }
        _ => {}
    }

    let Some((mut expr, is_le, strict)) = parser.parse_atom(lit.term) else {
        panic!("conflict literal must be a parsed arithmetic atom: {lit:?}");
    };

    if lit.value != is_le {
        expr.negate();
    }

    LeZeroConstraint {
        expr,
        strict: if lit.value { strict } else { !strict },
    }
}

fn assert_farkas_combination_is_contradictory(terms: &TermStore, conflict: &TheoryConflict) {
    let farkas = conflict
        .farkas
        .as_ref()
        .expect("tableau conflict must keep a Farkas annotation");
    assert!(
        farkas.is_valid(),
        "Farkas coefficients must stay non-negative: {:?}",
        farkas.coefficients
    );
    assert_eq!(
        conflict.literals.len(),
        farkas.coefficients.len(),
        "each conflict literal must have a matching Farkas coefficient"
    );

    let mut parser = LraSolver::new(terms);
    let mut combined = LinearExpr::zero();
    let mut combined_strict = false;

    for (lit, coeff) in conflict.literals.iter().zip(&farkas.coefficients) {
        let coeff = rational64_to_big(*coeff);
        assert!(
            coeff >= BigRational::zero(),
            "Farkas coefficient must be non-negative, got {coeff}"
        );
        if coeff.is_zero() {
            continue;
        }

        let row = normalize_to_le_zero(&mut parser, *lit);
        let mut scaled = row.expr.clone();
        scaled.scale(&coeff);
        combined.add(&scaled);
        combined_strict |= row.strict;
    }

    let combined = combined.normalize();
    assert!(
        combined.coeffs.is_empty(),
        "Farkas combination must eliminate all variables, got {combined:?}"
    );
    assert!(
        combined.constant > BigRational::zero()
            || (combined.constant.is_zero() && combined_strict),
        "Farkas combination must yield a contradictory row, got {combined:?}, strict={combined_strict}"
    );
}

fn assert_conflict_is_literal_minimal(terms: &TermStore, conflict: &TheoryConflict) {
    assert!(
        !conflict.literals.is_empty(),
        "minimality check needs a non-empty conflict"
    );

    for (remove_idx, removed) in conflict.literals.iter().enumerate() {
        let mut solver = LraSolver::new(terms);
        for (idx, lit) in conflict.literals.iter().enumerate() {
            if idx != remove_idx {
                solver.assert_literal(lit.term, lit.value);
            }
        }

        let result = solver.check();
        assert!(
            matches!(result, TheoryResult::Sat),
            "removing literal {removed:?} must make the conflict satisfiable, got {result:?}"
        );
    }
}

#[test]
fn test_lra_tableau_conflict_literals_match_expected_reason_atoms_issue_6617() {
    let (terms, conflict, expected) = tableau_conflict_fixture();

    let expected_set: HashSet<_> = expected.iter().copied().collect();
    let actual_set: HashSet<_> = conflict.literals.iter().copied().collect();

    assert_eq!(
        conflict.literals.len(),
        expected_set.len(),
        "tableau conflict should not contain duplicate or extra literals: {:?}",
        conflict.literals
    );
    assert_eq!(
        actual_set, expected_set,
        "tableau conflict should reference exactly the asserted infeasible bounds"
    );

    let sound_conflict = assert_conflict_soundness(
        TheoryResult::UnsatWithFarkas(conflict),
        LraSolver::new(&terms),
    );
    let sound_set: HashSet<_> = sound_conflict.into_iter().collect();
    assert_eq!(
        sound_set, expected_set,
        "soundness re-check should preserve the same conflict reason atoms"
    );
}

#[test]
fn test_lra_tableau_conflict_farkas_combination_is_contradictory_issue_6617() {
    let (terms, conflict, _) = tableau_conflict_fixture();
    assert_farkas_combination_is_contradictory(&terms, &conflict);
}

#[test]
fn test_lra_tableau_conflict_is_literal_minimal_issue_6617() {
    let (terms, conflict, _) = tableau_conflict_fixture();
    assert_conflict_is_literal_minimal(&terms, &conflict);
}
