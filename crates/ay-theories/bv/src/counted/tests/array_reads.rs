// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_arrays::counted_reads::{CountedArrayReadClosure, Derivation};
use ay_core::term::{CountedBuiltin, CountedTermBuilder};

mod unwind;

fn fixture(original: &CountedAdmission, element: Sort) -> (TermStore, TermId, TermId) {
    let mut terms = TermStore::try_new_with_admission(original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, original).unwrap();
    let base = builder
        .variable("base", &Sort::array(Sort::bitvec(2), element.clone()))
        .unwrap();
    let index = builder.variable("i", &Sort::bitvec(2)).unwrap();
    let value = builder.variable("v", &element).unwrap();
    let stored = builder
        .apply(CountedBuiltin::Store, &[base, index, value])
        .unwrap();
    let select = builder
        .apply(CountedBuiltin::Select, &[stored, index])
        .unwrap();
    let root = builder.apply(CountedBuiltin::Eq, &[select, value]).unwrap();
    builder.finish().unwrap();
    (terms, root, select)
}

#[test]
fn authentic_array_read_leaves_keep_exact_store_owner_and_unasserted_obligations() {
    for element in [Sort::Bool, Sort::bitvec(8)] {
        let original = ample();
        let (mut terms, root, read) = fixture(&original, element.clone());
        let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
        let mut encoder = CountedBvEncoder::with_array_reads(&terms, &closure).unwrap();
        assert!(std::ptr::eq(
            encoder.array_read_obligations().unwrap(),
            &closure
        ));
        assert!(encoder.clauses().unwrap().is_empty());
        assert!(closure
            .steps()
            .iter()
            .any(|step| matches!(step.derivation(), Derivation::Row1 { .. })));
        assert_eq!(closure.unresolved().len(), 1);
        encoder.encode_terms(&[root]).unwrap();
        match element {
            Sort::Bool => assert_ne!(encoder.literal(read).unwrap(), 0),
            Sort::BitVec(_) => assert_eq!(encoder.bits(read).unwrap().len(), 8),
            _ => unreachable!(),
        }
        // The read relation is NOT asserted by the leaf constructor: both
        // truth values of the equality remain satisfiable without theory rows.
        let literal = encoder.literal(root).unwrap();
        for value in [false, true] {
            assert!(matches!(
                pinned_solver(
                    encoder.num_vars().unwrap(),
                    encoder.clauses().unwrap(),
                    &[(literal, value)]
                )
                .solve()
                .into_inner(),
                SatResult::Sat(_)
            ));
        }
        let before = original.usage().unwrap().work_admitted;
        encoder.admission().admit(5, 0).unwrap();
        assert_eq!(original.usage().unwrap().work_admitted, before + 5);
        encoder.finish().unwrap();
        closure.finish().unwrap();
    }
}

#[test]
fn identical_numeric_foreign_store_is_not_a_read_leaf_capability() {
    let original = ample();
    let (mut terms, root, _) = fixture(&original, Sort::bitvec(8));
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    let foreign = terms.clone();
    assert!(matches!(
        CountedBvEncoder::with_array_reads(&foreign, &closure),
        Err(CountedBvError::Invalid)
    ));
    CountedBvEncoder::with_array_reads(&terms, &closure)
        .unwrap()
        .finish()
        .unwrap();
    closure.finish().unwrap();
}

#[test]
fn post_closure_builtin_declaration_is_rejected_before_array_leaf_creation() {
    let original = ample();
    let (mut terms, root, _) = fixture(&original, Sort::Bool);
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    terms.register_declared_function("select");
    assert!(matches!(
        CountedBvEncoder::with_array_reads(&terms, &closure),
        Err(CountedBvError::Unsupported(_))
    ));
    original.check().unwrap();
    closure.finish().unwrap();
}

#[test]
fn an_unlisted_appended_read_cannot_use_the_existing_array_leaf_permission() {
    let original = ample();
    let (mut terms, root, _) = fixture(&original, Sort::Bool);
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let array = builder
        .variable("different", &Sort::array(Sort::bitvec(2), Sort::Bool))
        .unwrap();
    let index = builder
        .variable("different-index", &Sort::bitvec(2))
        .unwrap();
    let extra = builder
        .apply(CountedBuiltin::Select, &[array, index])
        .unwrap();
    builder.finish().unwrap();
    let mut encoder = CountedBvEncoder::with_array_reads(&terms, &closure).unwrap();
    assert!(encoder.encode_terms(&[extra]).is_err());
    assert!(original.check().is_err());
    assert!(encoder.finish().is_err());
    assert!(closure.finish().is_err());
}

#[test]
fn original_work_exhaustion_never_creates_a_refreshed_array_encoder() {
    let original = ample();
    let (mut terms, root, _) = fixture(&original, Sort::bitvec(8));
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    original
        .admit(original.usage().unwrap().work_remaining as usize, 0)
        .unwrap();
    assert!(matches!(
        CountedBvEncoder::with_array_reads(&terms, &closure),
        Err(CountedBvError::Stopped(
            CountedAdmissionError::WorkExhausted
        ))
    ));
    assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
}
