// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::super::{EvalValue, EvalVar, EvalVarKind};
use super::{evaluate, evaluate_legacy, validate, EvalError};
use crate::ProofCheckError;
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;

mod closed;
mod indexed;
mod malformed;
mod operators;
mod oracle;
mod progress;

fn bv(terms: &mut TermStore, value: u64, width: u32) -> TermId {
    terms.mk_bitvec(BigInt::from(value), width)
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn indexed(terms: &mut TermStore, name: &str, indices: &[u32], arg: TermId, width: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed(name, indices.to_vec()),
        [arg],
        Sort::bitvec(width),
    )
}

fn compare(terms: &TermStore, term: TermId, env: &[(TermId, EvalValue)]) -> Option<EvalValue> {
    let expected = oracle::eval_term(terms, term, env);
    let actual = match evaluate(terms, term, env, &mut || Ok::<(), ProofCheckError>(())) {
        Ok(value) => Some(value),
        Err(EvalError::Unsupported) => None,
        Err(EvalError::Interrupted(error)) => panic!("live callback interrupted: {error}"),
    };
    assert_eq!(actual, expected, "term {:?}", terms.get(term));
    assert_eq!(evaluate_legacy(terms, term, env), expected);
    actual
}

fn compare_clause(terms: &TermStore, clause: &[TermId]) -> Result<(), ProofCheckError> {
    let expected = oracle::validate(terms, ProofId(17), clause);
    assert_eq!(
        validate(terms, ProofId(17), clause, &mut || Ok(())),
        expected
    );
    expected
}

#[test]
fn boolean_connectives_evaluate_all_children_but_ite_only_the_selected_branch() {
    let mut terms = TermStore::new();
    let truth = terms.true_term();
    let falsity = terms.false_term();
    let unsupported = app(&mut terms, "unsupported", &[], Sort::Bool);
    for (name, decisive, identity) in [("or", truth, false), ("and", falsity, true)] {
        let empty = app(&mut terms, name, &[], Sort::Bool);
        assert_eq!(compare(&terms, empty, &[]), Some(EvalValue::Bool(identity)));
        for args in [[decisive, unsupported], [unsupported, decisive]] {
            let term = app(&mut terms, name, &args, Sort::Bool);
            assert_eq!(compare(&terms, term, &[]), None);
        }
        let duplicate = app(&mut terms, name, &[decisive, decisive], Sort::Bool);
        assert_eq!(
            compare(&terms, duplicate, &[]),
            Some(EvalValue::Bool(!identity))
        );
    }
    for (cond, then_term, else_term, expected) in [
        (truth, truth, unsupported, Some(EvalValue::Bool(true))),
        (falsity, unsupported, falsity, Some(EvalValue::Bool(false))),
        (truth, unsupported, falsity, None),
        (falsity, truth, unsupported, None),
        (unsupported, truth, truth, None),
    ] {
        let ite = terms.mk_ite_raw(cond, then_term, else_term);
        assert_eq!(compare(&terms, ite, &[]), expected);
    }
    let negated = terms.mk_not_raw(truth);
    assert_eq!(compare(&terms, negated, &[]), Some(EvalValue::Bool(false)));
}

#[test]
fn environment_lookup_keeps_first_match_and_raw_equality_keeps_value_variants() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("value", Sort::bitvec(2));
    let first = EvalValue::BitVec { value: 2, width: 2 };
    let env = [(variable, first), (variable, EvalValue::Bool(true))];
    assert_eq!(compare(&terms, variable, &env), Some(first));
    assert_eq!(compare(&terms, variable, &[]), None);
    let truth = terms.true_term();
    let one = bv(&mut terms, 1, 1);
    let heterogeneous = app(&mut terms, "=", &[truth, one], Sort::Bool);
    assert_eq!(
        compare(&terms, heterogeneous, &[]),
        Some(EvalValue::Bool(false))
    );
}

#[test]
fn bounded_clause_acceptance_and_exact_error_reasons_match_the_frozen_validator() {
    let mut terms = TermStore::new();
    let truth = terms.true_term();
    let falsity = terms.false_term();
    let x = terms.mk_var("x", Sort::bitvec(2));
    let zero = bv(&mut terms, 0, 2);
    let identity = app(&mut terms, "=", &[x, x], Sort::Bool);
    let false_for_some_assignment = app(&mut terms, "=", &[x, zero], Sort::Bool);
    let malformed = app(&mut terms, "bvadd", &[x], Sort::bitvec(2));
    let malformed_bool = app(&mut terms, "=", &[malformed, zero], Sort::Bool);
    let unsupported = app(&mut terms, "unknown", &[], Sort::Bool);
    assert!(compare_clause(&terms, &[identity]).is_ok());
    assert!(compare_clause(&terms, &[identity, malformed_bool]).is_ok());
    assert!(compare_clause(&terms, &[malformed_bool, identity]).is_err());
    assert!(compare_clause(&terms, &[truth, unsupported]).is_err());
    for clause in [
        vec![],
        vec![falsity],
        vec![false_for_some_assignment],
        vec![zero],
    ] {
        assert!(compare_clause(&terms, &clause).is_err());
    }
    // Exactly eight assignment bits are accepted; the ninth retains its error.
    let mut identities = Vec::new();
    for index in 0..9 {
        let bit = terms.mk_var(format!("bit-{index}"), Sort::Bool);
        identities.push(app(&mut terms, "=", &[bit, bit], Sort::Bool));
    }
    assert!(compare_clause(&terms, &identities[..8]).is_ok());
    assert!(compare_clause(&terms, &identities).is_err());
}
