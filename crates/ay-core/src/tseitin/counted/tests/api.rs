// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn actual_public_exports_preserve_rows_steps_and_exact_materialized_literals() {
    let (mut terms, root, _) = formula(CountedBuiltin::Distinct);
    let original = ample();
    let cnf = crate::CountedCnf::encode(&mut terms, &[root], &original).unwrap();
    let _: &crate::CountedCnfRow = &cnf.rows()[0];
    let _: &crate::CountedCnfStep = &cnf.steps()[0];
    let _: crate::CountedCnfDistinctBridge = cnf.bridges()[0];
    let _: crate::CountedCnfJustification = cnf.rows()[0].justification();
    assert_eq!(cnf.roots(), [root]);
    assert!(cnf.theory_atoms().is_empty());
    for step in cnf.steps() {
        let _ = (step.rule(), step.source(), step.premises(), step.pivot());
        for &literal in step.clause() {
            let _: crate::CountedCnfSourceLit = literal;
            let term = cnf.source_literal_term(literal).unwrap();
            if literal.positive {
                assert_eq!(term, literal.term);
            } else {
                assert_eq!(cnf.terms().get(term), &TermData::Not(literal.term));
            }
        }
    }
    for row in cnf.rows() {
        for &literal in row.literals() {
            let _ = cnf.sat_literal_term(literal).unwrap();
        }
    }
    cnf.finish().unwrap();
}

#[test]
fn both_sat_polarities_are_materialized_and_do_not_modify_the_sealed_store() {
    let (mut terms, root, _) = formula(CountedBuiltin::Implies);
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    let count = cnf.terms().len();
    for variable in 1..=cnf.num_vars() {
        let positive = cnf.sat_literal_term(variable as i32).unwrap();
        let negative = cnf.sat_literal_term(-(variable as i32)).unwrap();
        assert_eq!(cnf.terms().get(negative), &TermData::Not(positive));
        assert_eq!(cnf.literal_for_term(positive).unwrap(), variable as i32);
    }
    assert_eq!(cnf.terms().len(), count);
}

#[test]
fn exact_source_negation_does_not_collapse_a_nested_not_into_sat_alias() {
    let (mut terms, not_a, variables) = formula(CountedBuiltin::Not);
    let source = ample();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let root = builder
        .apply(CountedBuiltin::Eq, &[not_a, variables[1]])
        .unwrap();
    builder.finish().unwrap();
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    let exact = cnf
        .source_literal_term(SourceLit {
            term: not_a,
            positive: false,
        })
        .unwrap();
    assert_eq!(cnf.terms().get(exact), &TermData::Not(not_a));
    let canonical = cnf
        .sat_literal_term(-cnf.literal_for_term(not_a).unwrap())
        .unwrap();
    assert_eq!(canonical, variables[0]);
    assert_ne!(exact, canonical);
}

#[test]
fn invalid_source_and_sat_lookups_refuse_without_inventing_authority() {
    let (mut terms, root, _) = formula(CountedBuiltin::Implies);
    let unknown_bool = terms.mk_var("unrelated", Sort::Bool);
    let non_bool = terms.mk_var("bits", Sort::bitvec(8));
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    for literal in [0, i32::MIN, i32::MAX, -(cnf.num_vars() as i32 + 1)] {
        assert_eq!(cnf.sat_literal_term(literal), Err(Error::Invalid));
    }
    for term in [unknown_bool, non_bool, TermId(u32::MAX)] {
        assert_eq!(cnf.literal_for_term(term), Err(Error::Invalid));
        for positive in [false, true] {
            assert_eq!(
                cnf.source_literal_term(SourceLit { term, positive }),
                Err(Error::Invalid)
            );
        }
    }
    assert_eq!(
        cnf.source_literal_term(SourceLit {
            term: root,
            positive: true
        }),
        Ok(root)
    );
}

#[test]
fn lookup_fees_use_only_the_retained_original_owner() {
    let (mut terms, root, _) = formula(CountedBuiltin::Implies);
    let original = ample();
    let cnf = CountedCnf::encode(&mut terms, &[root], &original).unwrap();
    let before = original.usage().unwrap().work_admitted;
    cnf.literal_for_term(root).unwrap();
    assert_eq!(original.usage().unwrap().work_admitted, before + 1);
    let _ = cnf
        .source_literal_term(SourceLit {
            term: root,
            positive: true,
        })
        .unwrap();
    assert_eq!(original.usage().unwrap().work_admitted, before + 2);
    let _ = cnf.sat_literal_term(1).unwrap();
    assert_eq!(original.usage().unwrap().work_admitted, before + 4);
    let remaining = cnf.admission().usage().unwrap().work_remaining as usize;
    cnf.admission().admit(remaining, 0).unwrap();
    drop(original);
    assert_eq!(
        cnf.sat_literal_term(1),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    );
    assert!(cnf.finish().is_err());
}

#[test]
fn cancellation_survives_lookup_callback_reset_and_final_disposal() {
    let stopped = Arc::new(AtomicBool::new(false));
    let seen = stopped.clone();
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 24),
        None,
        Arc::new(move || seen.load(Ordering::SeqCst)),
    )
    .unwrap();
    let (mut terms, root, _) = formula(CountedBuiltin::Distinct);
    let cnf = CountedCnf::encode(&mut terms, &[root], &original).unwrap();
    stopped.store(true, Ordering::SeqCst);
    assert!(matches!(
        cnf.source_literal_term(SourceLit {
            term: root,
            positive: true
        }),
        Err(Error::Stopped(_))
    ));
    stopped.store(false, Ordering::SeqCst);
    assert!(cnf.literal_for_term(root).is_err());
    assert!(cnf.finish().is_err());
}
