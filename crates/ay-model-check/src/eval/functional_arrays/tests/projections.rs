// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ProjectionLookupError;

struct Projected<'a> {
    ordinary: &'a View,
    term: TermId,
    claim: Result<Option<usize>, ProjectionLookupError>,
}
impl ModelView for Projected<'_> {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.ordinary.leaf_value(term)
    }
    fn array_snapshot(&self, term: TermId) -> Result<Option<Arc<ArraySnapshot>>, String> {
        self.ordinary.array_snapshot(term)
    }
    fn has_functional_arrays(&self) -> bool {
        self.ordinary.has_functional_arrays()
    }
    fn charge_functional_array_work(&self, amount: usize) -> Result<(), String> {
        self.ordinary.charge_functional_array_work(amount)
    }
    fn functional_array_interrupted(&self) -> bool {
        self.ordinary.functional_array_interrupted()
    }
    fn projection_argument(&self, term: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        if term == self.term {
            self.claim.clone()
        } else {
            Ok(None)
        }
    }
}

#[test]
fn checked_projected_store_keeps_base_semantics_during_capture_and_complete_equality() {
    let mut case = case(false, 3);
    let destination = recognize_range_lambda(&case.terms, case.lambda)
        .expect("original recipe")
        .destination;
    let index = case.terms.mk_bitvec(0.into(), 64);
    let datum = case.terms.mk_bitvec(9.into(), 8);
    let sort = case.terms.sort(destination).clone();
    let store = app(&mut case.terms, "store", &[destination, index, datum], sort);
    let ordinary = Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(store)
        .expect("literal write");
    case.view.arrays.insert(case.target, ordinary);
    let equality = app(&mut case.terms, "=", &[case.target, store], Sort::Bool);
    let view = Projected {
        ordinary: &case.view,
        term: store,
        claim: Ok(Some(0)),
    };
    assert!(!matches!(
        confirm_completed_model(&case.terms, &view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
    let captured = Evaluator::new(&case.terms, &view)
        .capture_array_snapshot(store)
        .expect("checked base projection");
    assert!(captured
        .same_function(&base(7), &mut 10_000)
        .expect("whole base function"));
    case.view.arrays.insert(case.target, captured);
    let view = Projected {
        ordinary: &case.view,
        term: store,
        claim: Ok(Some(0)),
    };
    assert!(matches!(
        confirm_completed_model(&case.terms, &view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn projected_store_errors_indices_and_sort_claims_propagate_without_literal_fallback() {
    let mut case = case(false, 3);
    let destination = recognize_range_lambda(&case.terms, case.lambda)
        .expect("original recipe")
        .destination;
    let index = case.terms.mk_bitvec(0.into(), 64);
    let datum = case.terms.mk_bitvec(9.into(), 8);
    let sort = case.terms.sort(destination).clone();
    let store = app(&mut case.terms, "store", &[destination, index, datum], sort);
    for claim in [
        Err(ProjectionLookupError::inconsistent_model("source refusal")),
        Ok(Some(99)),
        Ok(Some(1)),
    ] {
        let view = Projected {
            ordinary: &case.view,
            term: store,
            claim,
        };
        assert!(Evaluator::new(&case.terms, &view)
            .capture_array_snapshot(store)
            .is_err());
    }
}

#[test]
fn checked_projection_inside_range_grammar_never_receives_literal_range_credit() {
    let case = case(false, 3);
    let TermData::App(_, lambda) = case.terms.get(case.lambda) else {
        panic!("actual lambda")
    };
    let TermData::Ite(cond, _, _) = case.terms.get(lambda[1]) else {
        panic!("actual range body")
    };
    for claim in [
        Ok(Some(0)),
        Err(ProjectionLookupError::inconsistent_model("source refusal")),
        Ok(Some(99)),
    ] {
        let view = Projected {
            ordinary: &case.view,
            term: *cond,
            claim,
        };
        assert!(Evaluator::new(&case.terms, &view)
            .capture_array_snapshot(case.lambda)
            .is_err());
        assert!(!matches!(
            confirm_completed_model(&case.terms, &view, &[case.definition]),
            GateVerdict::ConfirmedSat
        ));
    }
}
