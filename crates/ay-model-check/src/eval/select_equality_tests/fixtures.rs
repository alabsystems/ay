// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Equality must not materialize arrays before exact scalar reads can run.

use super::super::*;

#[derive(Default)]
pub(super) struct Model {
    pub(super) leaves: HashMap<TermId, ModelValue>,
    pub(super) reads: HashMap<TermId, ModelValue>,
    pub(super) applications: HashMap<TermId, ModelValue>,
    pub(super) projections: HashMap<TermId, Result<Option<usize>, crate::ProjectionLookupError>>,
    pub(super) read_calls: RefCell<Vec<TermId>>,
    pub(super) application_calls: RefCell<Vec<TermId>>,
}

impl ModelView for Model {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaves.get(&term).cloned()
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.read_calls.borrow_mut().push(term);
        self.reads.get(&term).cloned()
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.application_calls.borrow_mut().push(term);
        self.applications.get(&term).cloned()
    }

    fn projection_argument(
        &self,
        term: TermId,
    ) -> Result<Option<usize>, crate::ProjectionLookupError> {
        self.projections.get(&term).cloned().unwrap_or(Ok(None))
    }
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

pub(super) fn integer(value: i64) -> ModelValue {
    ModelValue::Int(BigInt::from(value))
}

pub(super) fn lambda(terms: &mut TermStore, increment: i64) -> TermId {
    let bound = terms.mk_var("bound", Sort::Int);
    let offset = terms.mk_int(BigInt::from(increment));
    let body = app(terms, "+", &[bound, offset], Sort::Int);
    app(
        terms,
        "lambda-array",
        &[bound, body],
        Sort::array(Sort::Int, Sort::Int),
    )
}

pub(super) fn read(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    app(terms, "select", &[array, index], Sort::Int)
}

pub(super) fn equality(terms: &mut TermStore, operands: &[TermId]) -> TermId {
    app(terms, "=", operands, Sort::Bool)
}

pub(super) fn linear_case(right_index: i64) -> (TermStore, Model, [TermId; 2]) {
    let mut terms = TermStore::new();
    let array = lambda(&mut terms, 1);
    let left_index = terms.mk_int(BigInt::from(2));
    let right_index = terms.mk_int(BigInt::from(right_index));
    let zero = terms.mk_int(BigInt::from(0));
    // Raw application keeps equal-valued indices syntactically distinct.
    let right_index = app(&mut terms, "+", &[right_index, zero], Sort::Int);
    let reads = [
        read(&mut terms, array, left_index),
        read(&mut terms, array, right_index),
    ];
    assert_ne!(
        reads[0], reads[1],
        "reflexivity must not hide the optional shortcut"
    );
    let mut model = Model::default();
    model.reads.insert(reads[0], integer(999));
    model.reads.insert(reads[1], integer(-999));
    (terms, model, reads)
}

pub(super) fn assert_gate_boolean(terms: &TermStore, model: &Model, root: TermId, expected: bool) {
    for actual in [
        crate::confirm_model(terms, model, &[root]),
        crate::confirm_completed_model(terms, model, &[root]),
    ] {
        assert!(
            matches!(
                (&actual, expected),
                (crate::GateVerdict::ConfirmedSat, true)
                    | (crate::GateVerdict::ModelViolates { .. }, false)
            ),
            "expected {expected}, got {actual:?}"
        );
    }
}
