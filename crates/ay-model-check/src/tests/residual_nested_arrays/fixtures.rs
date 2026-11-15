// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored PbTerm / Vec_bv40 carrier, not a captured compiler export.

use super::*;

#[derive(Default)]
pub(super) struct Model {
    pub(super) leaves: HashMap<TermId, Arc<ModelValue>>,
    pub(super) applications: HashMap<TermId, ModelValue>,
    pub(super) selects: HashMap<TermId, ModelValue>,
}

impl ModelView for Model {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaves.get(&term).map(|value| value.as_ref().clone())
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.applications.get(&term).cloned()
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.selects.get(&term).cloned()
    }
}

impl Model {
    pub(super) fn install(&mut self, terms: &TermStore, values: Vec<CompletedArrayAssignment>) {
        for assignment in values {
            let (term, stamp, value) = assignment.into_parts();
            assert_eq!(Some(stamp), terms.entry_stamp(term));
            assert!(self.leaves.insert(term, value).is_none());
        }
    }
}

pub(super) fn record(name: &str, ctor: &str, fields: Vec<DatatypeField>) -> Sort {
    Sort::Datatype(DatatypeSort::new(
        name,
        vec![DatatypeConstructor::new(ctor, fields)],
    ))
}

pub(super) fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), width)
}

pub(super) fn data(default: u64, stores: &[(u64, u64)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: bv(default, 40),
        store: stores
            .iter()
            .map(|&(k, v)| (bv(k, 64), bv(v, 40)))
            .collect(),
    }))
}

pub(super) fn vector(data: ModelValue) -> ModelValue {
    ModelValue::Datatype {
        ctor: "mkVec_bv40".into(),
        args: vec![bv(0, 64), bv(65, 64), bv(66, 64), data],
    }
}

pub(super) fn element(data: ModelValue) -> ModelValue {
    ModelValue::Datatype {
        ctor: "mkPbTerm".into(),
        args: vec![bv(7, 128), vector(data)],
    }
}

pub(super) fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    app(terms, "=", &[left, right], Sort::Bool)
}

pub(super) fn eq_bv(terms: &mut TermStore, left: TermId, value: u64, width: u32) -> TermId {
    let right = terms.mk_bitvec(BigInt::from(value), width);
    eq(terms, left, right)
}

pub(super) struct Fixture {
    pub(super) vector: Sort,
    pub(super) element: Sort,
    pub(super) data: Sort,
    pub(super) a: TermId,
    pub(super) b: TermId,
    pub(super) outer: TermId,
    pub(super) inner: TermId,
}

impl Fixture {
    pub(super) fn new(terms: &mut TermStore) -> Self {
        let data = Sort::array(Sort::bitvec(64), Sort::bitvec(40));
        let vector = record(
            "Vec_bv40",
            "mkVec_bv40",
            vec![
                DatatypeField::new("fld_ptr", Sort::bitvec(64)),
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("fld_cap", Sort::bitvec(64)),
                DatatypeField::new("fld_data", data.clone()),
            ],
        );
        let element = record(
            "PbTerm",
            "mkPbTerm",
            vec![
                DatatypeField::new("fld_coeff", Sort::bitvec(128)),
                DatatypeField::new("fld_lits", vector.clone()),
            ],
        );
        let array = Sort::array(Sort::bitvec(64), element.clone());
        let a = terms.mk_var("a", array.clone());
        let b = terms.mk_var("b", array);
        let outer = terms.mk_bitvec(BigInt::from(0x8000_0000_0000_0001u64), 64);
        let inner = terms.mk_bitvec(BigInt::from(33), 64);
        Self {
            vector,
            element,
            data,
            a,
            b,
            outer,
            inner,
        }
    }

    pub(super) fn read(
        &self,
        terms: &mut TermStore,
        array: TermId,
        outer: TermId,
        inner: TermId,
    ) -> [TermId; 4] {
        let element = app(terms, "select", &[array, outer], self.element.clone());
        let vector = app(terms, "fld_lits", &[element], self.vector.clone());
        let data = app(terms, "fld_data", &[vector], self.data.clone());
        let cell = app(terms, "select", &[data, inner], Sort::bitvec(40));
        [element, vector, data, cell]
    }
}

pub(super) fn complete(
    terms: &TermStore,
    model: &Model,
    roots: &[TermId],
) -> Vec<CompletedArrayAssignment> {
    let (verdict, completion) =
        confirm_model_with_array_completion(terms, model, roots).into_parts();
    assert_confirmed(&verdict);
    completion
        .expect("this fixture must require genuine residual completion")
        .into_assignments()
        .unwrap()
}

pub(super) fn refused(terms: &TermStore, model: &dyn ModelView, roots: &[TermId]) {
    let (verdict, completion) =
        confirm_model_with_array_completion(terms, model, roots).into_parts();
    assert!(!matches!(verdict, GateVerdict::ConfirmedSat), "{verdict:?}");
    assert!(completion.is_none());
}

pub(super) fn assert_bv(terms: &TermStore, model: &Model, term: TermId, expected: u64, width: u32) {
    let EvalOutcome::Value(actual) = evaluate_term(terms, model, term) else {
        panic!("completed read must be concrete");
    };
    assert!(value_eq(&actual, &bv(expected, width)).unwrap());
}
