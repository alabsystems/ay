// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{recognize_identity_lambda, ProjectionLookupError};

struct Identity {
    terms: TermStore,
    view: View,
    source: TermId,
    target: TermId,
    bound: TermId,
    read: TermId,
    lambda: TermId,
}

fn identity(width: u32) -> Identity {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(width));
    let source = terms.mk_var("identity_source", sort.clone());
    let target = terms.mk_var("identity_target", sort.clone());
    let bound = terms.mk_var("identity_bound", Sort::bitvec(64));
    let read = app(&mut terms, "select", &[source, bound], Sort::bitvec(width));
    let lambda = app(&mut terms, "lambda-array", &[bound, read], sort.clone());
    let captured = ArraySnapshot::finite(
        ArrayValue {
            default: bv(7, width),
            store: vec![],
        },
        &sort,
        &mut 1000,
    )
    .expect("complete entire source");
    let mut view = View {
        left: Cell::new(100_000),
        ..View::default()
    };
    view.arrays.insert(source, captured.clone());
    view.arrays.insert(target, captured);
    Identity {
        terms,
        view,
        source,
        target,
        bound,
        read,
        lambda,
    }
}

fn refuses(case: &mut Identity, lambda: TermId) {
    assert!(recognize_identity_lambda(&case.terms, lambda).is_none());
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .is_err());
    let equality = app(&mut case.terms, "=", &[case.target, lambda], Sort::Bool);
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn normalized_identity_validates_full_function_and_all_independent_reads() {
    let mut case = identity(8);
    let equality = app(
        &mut case.terms,
        "=",
        &[case.target, case.lambda],
        Sort::Bool,
    );
    let index = case.terms.mk_bitvec(u64::MAX.into(), 64);
    let read = app(
        &mut case.terms,
        "select",
        &[case.target, index],
        Sort::bitvec(8),
    );
    let seven = case.terms.mk_bitvec(7.into(), 8);
    let nine = case.terms.mk_bitvec(9.into(), 8);
    let good = app(&mut case.terms, "=", &[read, seven], Sort::Bool);
    let wrong = app(&mut case.terms, "=", &[read, nine], Sort::Bool);
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[equality, good]),
        GateVerdict::ConfirmedSat
    ));
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[equality, wrong]),
        GateVerdict::ModelViolates { .. }
    ));
}

#[test]
fn identity_requires_exact_named_operators_and_original_binder_index_and_sorts() {
    for changed in 0..7 {
        let mut case = identity(8);
        let sort = case.terms.sort(case.target).clone();
        let bad = match changed {
            0 => case.terms.mk_app(
                Symbol::indexed("lambda-array", vec![0]),
                &[case.bound, case.read],
                sort,
            ),
            1 => {
                let read = case.terms.mk_app(
                    Symbol::indexed("select", vec![0]),
                    &[case.source, case.bound],
                    Sort::bitvec(8),
                );
                app(&mut case.terms, "lambda-array", &[case.bound, read], sort)
            }
            2 => {
                let other = case.terms.mk_var("unrelated_index", Sort::bitvec(64));
                let read = app(
                    &mut case.terms,
                    "select",
                    &[case.source, other],
                    Sort::bitvec(8),
                );
                app(&mut case.terms, "lambda-array", &[case.bound, read], sort)
            }
            3 => {
                let nonvariable = case.terms.mk_bitvec(0.into(), 64);
                let read = app(
                    &mut case.terms,
                    "select",
                    &[case.source, nonvariable],
                    Sort::bitvec(8),
                );
                app(&mut case.terms, "lambda-array", &[nonvariable, read], sort)
            }
            4 => {
                let bound = case.terms.mk_var("wrong_width_bound", Sort::bitvec(32));
                let read = app(
                    &mut case.terms,
                    "select",
                    &[case.source, bound],
                    Sort::bitvec(8),
                );
                app(&mut case.terms, "lambda-array", &[bound, read], sort)
            }
            5 => {
                let read = app(
                    &mut case.terms,
                    "select",
                    &[case.source, case.bound],
                    Sort::bitvec(16),
                );
                app(&mut case.terms, "lambda-array", &[case.bound, read], sort)
            }
            _ => app(
                &mut case.terms,
                "lambda-array",
                &[case.bound, case.read],
                Sort::array(Sort::bitvec(64), Sort::bitvec(16)),
            ),
        };
        refuses(&mut case, bad);
    }
}

#[test]
fn identity_capture_declines_a_source_array_that_depends_on_its_bound_index() {
    let mut case = identity(8);
    let value = case.terms.mk_bitvec(9.into(), 8);
    let sort = case.terms.sort(case.source).clone();
    let captured = app(
        &mut case.terms,
        "store",
        &[case.source, case.bound, value],
        sort.clone(),
    );
    let read = app(
        &mut case.terms,
        "select",
        &[captured, case.bound],
        Sort::bitvec(8),
    );
    let lambda = app(&mut case.terms, "lambda-array", &[case.bound, read], sort);
    assert!(
        recognize_identity_lambda(&case.terms, lambda).is_some(),
        "grammar alone is not capture authority"
    );
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .is_err());
    let equality = app(&mut case.terms, "=", &[case.target, lambda], Sort::Bool);
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
}

struct Projection<'a> {
    ordinary: &'a View,
    term: TermId,
    claim: Result<Option<usize>, ProjectionLookupError>,
}
impl ModelView for Projection<'_> {
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
    fn projection_argument(&self, term: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        if term == self.term {
            self.claim.clone()
        } else {
            Ok(None)
        }
    }
}

#[test]
fn identity_read_projection_errors_indices_and_same_sort_changes_cannot_be_ignored() {
    let mut case = identity(64);
    let equality = app(
        &mut case.terms,
        "=",
        &[case.target, case.lambda],
        Sort::Bool,
    );
    for claim in [
        Err(ProjectionLookupError::inconsistent_model(
            "original refusal",
        )),
        Ok(Some(99)),
        Ok(Some(0)),
        Ok(Some(1)),
    ] {
        let view = Projection {
            ordinary: &case.view,
            term: case.read,
            claim,
        };
        assert!(Evaluator::new(&case.terms, &view)
            .capture_array_snapshot(case.lambda)
            .is_err());
        assert!(!matches!(
            confirm_completed_model(&case.terms, &view, &[equality]),
            GateVerdict::ConfirmedSat
        ));
    }
}

#[test]
fn identity_source_store_obeys_its_original_checked_projection() {
    let mut case = identity(8);
    let index = case.terms.mk_bitvec(0.into(), 64);
    let datum = case.terms.mk_bitvec(9.into(), 8);
    let sort = case.terms.sort(case.source).clone();
    let store = app(
        &mut case.terms,
        "store",
        &[case.source, index, datum],
        sort.clone(),
    );
    let read = app(
        &mut case.terms,
        "select",
        &[store, case.bound],
        Sort::bitvec(8),
    );
    let lambda = app(&mut case.terms, "lambda-array", &[case.bound, read], sort);
    let equality = app(&mut case.terms, "=", &[case.target, lambda], Sort::Bool);
    let view = Projection {
        ordinary: &case.view,
        term: store,
        claim: Ok(Some(0)),
    };
    assert!(matches!(
        confirm_completed_model(&case.terms, &view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
    for claim in [
        Err(ProjectionLookupError::inconsistent_model("source refusal")),
        Ok(Some(99)),
        Ok(Some(1)),
    ] {
        let view = Projection {
            ordinary: &case.view,
            term: store,
            claim,
        };
        assert!(Evaluator::new(&case.terms, &view)
            .capture_array_snapshot(lambda)
            .is_err());
    }
}
