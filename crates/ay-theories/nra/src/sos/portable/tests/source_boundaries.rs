// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn exact_clause_polarity_is_preserved_for_every_comparison(
) -> Result<(), Box<dyn std::error::Error>> {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    for (name, asserted, negated) in [
        ("<", Rel::Lt, Rel::Ge),
        ("<=", Rel::Le, Rel::Gt),
        ("=", Rel::Eq, Rel::Ne),
        (">=", Rel::Ge, Rel::Lt),
        (">", Rel::Gt, Rel::Le),
    ] {
        let atom = terms.mk_app(Symbol::named(name), [x, zero], Sort::Bool);
        let not_atom = terms.mk_not_raw(atom);
        let not_not_atom = terms.mk_not_raw(not_atom);
        for (literal, expected) in [
            (atom, negated),
            (not_atom, asserted),
            (not_not_atom, negated),
        ] {
            let source = source(&terms, &[literal]);
            let constraint = source
                .constraints()
                .first()
                .ok_or("a one-literal clause yields a constraint")?;
            assert_eq!(constraint.rel, expected);
            assert_eq!(constraint.poly.terms, vec![(vec![x], one())]);
        }
    }
    Ok(())
}

#[test]
fn exact_clause_declines_boolean_packing_and_noncomparison_slots() {
    let (mut terms, clause, _) = linear();
    let packed = terms.mk_app(Symbol::named("or"), &clause, Sort::Bool);
    let x = terms.mk_var("other", Sort::Real);
    let zero = real(&mut terms, 0);
    let distinct = terms.mk_app(Symbol::named("distinct"), [x, zero], Sort::Bool);
    let boolean = terms.true_term();
    for term in [packed, distinct, boolean, x] {
        assert!(
            SosClauseSource::from_clause(&terms, &[term], &mut SosPolynomialBudget::default())
                .is_none()
        );
    }
}

#[test]
fn exact_clause_refuses_forged_constant_kinds_and_dangling_descendants() {
    let (terms, clause, _) = linear();
    let TermData::Not(atom) = terms.get(clause[0]) else {
        panic!("literal")
    };
    let TermData::App(_, arguments) = terms.get(*atom) else {
        panic!("comparison")
    };
    let constant = arguments[1];
    let mut entries = terms.entries_snapshot();
    entries[constant.index()].0 = TermData::Const(Constant::Int(2.into()));
    let malformed = TermStore::from_entries(entries, None, None, 0);
    assert!(
        SosClauseSource::from_clause(&malformed, &clause, &mut SosPolynomialBudget::default())
            .is_none()
    );
    for missing in [TermId(terms.len() as u32), TermId(u32::MAX)] {
        let mut entries = terms.entries_snapshot();
        entries[clause[0].index()].0 = TermData::Not(missing);
        let malformed = TermStore::from_entries(entries, None, None, 0);
        assert!(SosClauseSource::from_clause(
            &malformed,
            &clause,
            &mut SosPolynomialBudget::default()
        )
        .is_none());
        assert!(SosClauseSource::from_clause(
            &terms,
            &[missing],
            &mut SosPolynomialBudget::default()
        )
        .is_none());
    }
}

#[test]
fn exact_clause_enforces_degree_and_total_source_variable_bounds() {
    let mut terms = TermStore::new();
    let zero = real(&mut terms, 0);
    let x = terms.mk_var("x", Sort::Real);
    let fifth = terms.mk_app(Symbol::named("*"), [x; 5], Sort::Real);
    let over_degree = literal(&mut terms, "<", fifth, zero);
    assert!(SosClauseSource::from_clause(
        &terms,
        &[over_degree],
        &mut SosPolynomialBudget::default()
    )
    .is_none());
    let mut clause = Vec::new();
    for index in 0..9 {
        let variable = terms.mk_var(format!("x{index}"), Sort::Real);
        clause.push(literal(&mut terms, ">", variable, zero));
    }
    assert!(SosClauseSource::from_clause(
        &terms,
        &clause[..8],
        &mut SosPolynomialBudget::default()
    )
    .is_some());
    assert!(
        SosClauseSource::from_clause(&terms, &clause, &mut SosPolynomialBudget::default())
            .is_none()
    );
}
