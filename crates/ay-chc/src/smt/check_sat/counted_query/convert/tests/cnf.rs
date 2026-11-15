// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_core::original_query::OriginalAdmissionError;
use ay_core::{AletheRule, CountedCnfJustification};
use std::sync::atomic::{AtomicBool, Ordering};

mod arrays;
mod resources;

fn formula() -> ChcExpr {
    let p = Arc::new(var("p", ChcSort::Bool));
    let q = Arc::new(var("q", ChcSort::Bool));
    ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::Op(ChcOp::Implies, vec![p.clone(), q.clone()])),
            Arc::new(ChcExpr::Op(ChcOp::Ne, vec![p, q])),
        ],
    )
}

#[test]
fn original_mapping_and_native_distinct_ledger_share_one_exact_source() {
    let source = formula();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    let expected_census = built.census();
    built
        .with_cnf(|context, cnf| {
            assert!(std::ptr::eq(context.original(), &source));
            assert_eq!(context.census(), expected_census);
            assert_eq!(context.term_for(&source)?, context.root());
            assert_eq!(cnf.roots(), &[context.root()]);
            assert_eq!(context.bindings().len(), 2);
            for binding in context.bindings() {
                assert_eq!(cnf.terms().sort(binding.term), &Sort::Bool);
                assert!(
                    matches!(cnf.terms().get(binding.term), TermData::Var(name, _)
                    if name.as_ref() == binding.original.name)
                );
            }
            assert_eq!(
                context.term_for(&ChcExpr::Bool(false)),
                Err(Error::IllTyped)
            );
            assert_eq!(cnf.bridges().len(), 1);
            assert!(cnf.steps().iter().any(|step| {
                step.rule() == &AletheRule::Resolution && step.premises().is_some()
            }));
            assert_eq!(
                cnf.rows().last().unwrap().justification(),
                CountedCnfJustification::Root(context.root())
            );
            context.admission().admit(7, 13)?;
            assert_eq!(context.admission().usage(), cnf.admission().usage());
            assert_eq!(context.admission().deadline(), None);
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn boolean_array_reads_and_bv_comparisons_remain_explicit_theory_obligations() {
    let index = Arc::new(var("same", ChcSort::BitVec(8)));
    let array = Arc::new(var(
        "same",
        ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::Bool)),
    ));
    let read = Arc::new(ChcExpr::Op(ChcOp::Select, vec![array, index.clone()]));
    let compare = Arc::new(ChcExpr::Op(
        ChcOp::BvULt,
        vec![index, Arc::new(ChcExpr::BitVec(9, 8))],
    ));
    let source = ChcExpr::Op(ChcOp::And, vec![read.clone(), compare.clone()]);
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_cnf(|context, cnf| {
            assert!(context.census().has_arrays);
            assert_eq!(context.bindings().len(), 2);
            assert_eq!(context.bindings()[0].original.name, "same");
            assert_eq!(context.bindings()[1].original.name, "same");
            assert_ne!(context.bindings()[0].term, context.bindings()[1].term);
            assert_eq!(
                cnf.theory_atoms(),
                &[context.term_for(&read)?, context.term_for(&compare)?]
            );
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn semantic_callback_decline_does_not_fabricate_a_resource_refusal() {
    let source = formula();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    assert_eq!(
        built.with_cnf::<()>(|_, _| Err(Error::Unsupported)),
        Err(Error::Unsupported)
    );
    assert_eq!(original.usage().unwrap().refusal, None);
    built
        .with_cnf(|_, cnf| {
            cnf.check()?;
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn callback_unwind_latches_original_owner_without_escaping_or_revival() {
    let source = formula();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::OperationPanicked);
    assert_eq!(
        built.with_cnf::<()>(|_, _| panic!("callback stopped")),
        Err(Error::Stopped(expected))
    );
    assert_eq!(original.check(), Err(expected));
    let reached = AtomicBool::new(false);
    assert_eq!(
        built.with_cnf(|_, _| {
            reached.store(true, Ordering::SeqCst);
            Ok(())
        }),
        Err(Error::Stopped(expected))
    );
    assert!(!reached.load(Ordering::SeqCst));
}

#[test]
fn a_reported_stop_is_shared_even_when_the_callback_did_not_debit() {
    let source = formula();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    let expected = CountedAdmissionError::StorageExhausted;
    assert_eq!(
        built.with_cnf::<()>(|_, _| Err(Error::Stopped(expected))),
        Err(Error::Stopped(expected))
    );
    assert_eq!(original.clone().check(), Err(expected));
    assert_eq!(built.finish(), Err(Error::Stopped(expected)));
}
